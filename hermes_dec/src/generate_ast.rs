use std::collections::VecDeque;

use petgraph::{
    graph::EdgeReference,
    stable_graph::NodeIndex,
    visit::{Bfs, Dfs, DfsPostOrder, EdgeRef, VisitMap},
    Graph,
};
use swc_common::DUMMY_SP;
use swc_ecma_ast::{
    ArrayLit, AssignExpr, AssignOp, BinExpr, BinaryOp, BlockStmt, Bool, CallExpr, Callee,
    ComputedPropName, CondExpr, ContinueStmt, DebuggerStmt, DoWhileStmt, Expr, ExprOrSpread,
    ExprStmt, Ident, IfStmt, KeyValueProp, Lit, MemberExpr, MemberProp, NewExpr, Null, Number,
    ObjectLit, ParenExpr, PatOrExpr, Prop, PropName, PropOrSpread, ReturnStmt, Stmt, Str,
    ThrowStmt, UnaryExpr, UnaryOp, UpdateExpr, UpdateOp, WhileStmt,
};

use crate::{
    bytecode::v93::{Instruction, JS_BUILTINS},
    hermes_file_reader::{BytecodeFile, InstructionInfo},
};

enum AstGeneratorStage {
    BeginProcessBlock,
    LoopCheck,
    IfCheck,
    AfterIf,
    ProcessingDone,
}

pub struct AstGenerator<'a> {
    stmt_queue: VecDeque<Stmt>,

    f: &'a BytecodeFile,
    cfg: &'a Graph<Vec<usize>, bool>,
    instructions: &'a [InstructionInfo<Instruction>],
    node: NodeIndex,
    is_do_while_first_block: bool,
    while_cond_block: Option<NodeIndex>,
    do_while_cond_block: Option<NodeIndex>,

    after_if_node: Option<NodeIndex>,
    stage: AstGeneratorStage,

    chained_iterator: Option<Box<AstGenerator<'a>>>,

    is_last_instruction_return: bool,
}

impl<'a> AstGenerator<'a> {
    pub fn new(
        f: &'a BytecodeFile,
        cfg: &'a Graph<Vec<usize>, bool>,
        instructions: &'a [InstructionInfo<Instruction>],
        node: NodeIndex,
        is_do_while_first_block: bool,
        while_cond_block: Option<NodeIndex>,
        do_while_cond_block: Option<NodeIndex>,
    ) -> Self {
        Self {
            stmt_queue: VecDeque::new(),
            f,
            cfg,
            instructions,
            node,
            is_do_while_first_block,
            while_cond_block,
            do_while_cond_block,
            after_if_node: None,
            stage: AstGeneratorStage::BeginProcessBlock,
            chained_iterator: None,

            is_last_instruction_return: false,
        }
    }

    fn populate_next_stage(&mut self) -> bool {
        match self.stage {
            AstGeneratorStage::BeginProcessBlock => {
                if let Some(while_cond_block) = self.while_cond_block {
                    //this means that we got redirected through a jump back to a while loop condition
                    //we don't need to decompile anything at this point so we just return a "continue;"
                    if while_cond_block == self.node {
                        self.stmt_queue.push_back(Stmt::Continue(ContinueStmt {
                            span: DUMMY_SP,
                            label: None,
                        }));
                        self.stage = AstGeneratorStage::ProcessingDone;
                        return false;
                    }
                }

                self.stmt_queue.append(
                    &mut simple_instructions_to_ast(self.f, self.cfg, self.node, self.instructions)
                        .into(),
                );

                if self.do_while_cond_block.is_some()
                    && self.do_while_cond_block.unwrap() == self.node
                {
                    //we reached the end of a do..while loop statement so we just put decompiled statements in that block into stmts
                    //and then don't check for loops as it'll throw us in an infinite loop
                    self.stage = AstGeneratorStage::ProcessingDone;
                    return false;
                }
                self.stage = AstGeneratorStage::LoopCheck;
                true
            }
            AstGeneratorStage::LoopCheck => {
                let indecies = self.cfg.node_weight(self.node).unwrap();
                let flow_index = indecies.last().unwrap();
                let incoming_edges = self
                    .cfg
                    .edges_directed(self.node, petgraph::Direction::Incoming)
                    .collect::<Vec<EdgeReference<'_, bool>>>();
                if !self.is_do_while_first_block && incoming_edges.len() >= 2 {
                    //is_do_while_first_block -> prevent going into a loop
                    //either loop or "if target"
                    let edges_from = incoming_edges
                        .iter()
                        .map(|e| e.source())
                        .collect::<Vec<NodeIndex>>();
                    let mut dfs = DfsPostOrder::new(self.cfg, self.node);
                    {
                        let mut dfs_a = Dfs::new(self.cfg, NodeIndex::new(0));
                        dfs_a.discovered.visit(self.node);
                        while let Some(node) = dfs_a.next(self.cfg) {
                            dfs.discovered.visit(node);
                            dfs.finished.visit(node);
                        }
                    }

                    let mut is_loop = false;
                    let mut possible_loop_condition_index = None;
                    while let Some(node) = dfs.next(self.cfg) {
                        if edges_from.contains(&node) {
                            is_loop = true;
                            possible_loop_condition_index = Some(node);
                            break;
                        }
                    }

                    if is_loop {
                        let cond_index = self
                            .cfg
                            .node_weight(possible_loop_condition_index.unwrap())
                            .unwrap()
                            .last()
                            .unwrap();
                        let mut skip_do_while_check = false;
                        if let Instruction::Jmp { .. } = &self.instructions[*cond_index].instruction
                        {
                            skip_do_while_check = true; //can't be do_while if ends with jmp
                        }
                        let (index, loop_cond_index) = if skip_do_while_check {
                            (*flow_index, self.node)
                        } else {
                            (*cond_index, possible_loop_condition_index.unwrap())
                        };

                        let cond = jump_inst_to_test(&self.instructions[index].instruction);
                        let outgoing_edges = self
                            .cfg
                            .edges_directed(loop_cond_index, petgraph::Direction::Outgoing)
                            .collect::<Vec<EdgeReference<'_, bool>>>();
                        let (tru, fals) = {
                            let mut tru = None;
                            let mut fals = None;
                            for edge in &outgoing_edges {
                                if *edge.weight() {
                                    tru = Some(edge);
                                } else {
                                    fals = Some(edge);
                                }
                            }
                            (tru.unwrap(), fals.unwrap())
                        };
                        if tru.target() == self.node {
                            //do..while
                            let body = AstGenerator::new(
                                self.f,
                                self.cfg,
                                self.instructions,
                                self.node,
                                true,
                                None,
                                Some(possible_loop_condition_index.unwrap()),
                            )
                            .collect::<Vec<Stmt>>();
                            if indecies.len() > 1 {
                                //add_inside_while(&mut body, &stmts)
                            }
                            self.stmt_queue.push_back(Stmt::DoWhile(DoWhileStmt {
                                span: DUMMY_SP,
                                test: Box::new(Expr::Paren(ParenExpr {
                                    span: DUMMY_SP,
                                    expr: Box::new(cond),
                                })),
                                body: Box::new(Stmt::Block(BlockStmt {
                                    span: DUMMY_SP,
                                    stmts: body,
                                })),
                            }));
                            self.chained_iterator = Some(Box::new(AstGenerator::new(
                                self.f,
                                self.cfg,
                                self.instructions,
                                fals.target(),
                                false,
                                None,
                                None,
                            )));
                        } else {
                            //while..do
                            let mut body = AstGenerator::new(
                                self.f,
                                self.cfg,
                                self.instructions,
                                fals.target(),
                                false,
                                Some(self.node),
                                self.do_while_cond_block,
                            )
                            .collect::<Vec<Stmt>>();
                            if indecies.len() > 1 {
                                add_inside_while(&mut body, &self.stmt_queue)
                            }
                            self.stmt_queue.push_back(Stmt::While(WhileStmt {
                                span: DUMMY_SP,
                                test: Box::new(Expr::Unary(UnaryExpr {
                                    span: DUMMY_SP,
                                    op: UnaryOp::Bang,
                                    arg: Box::new(Expr::Paren(ParenExpr {
                                        span: DUMMY_SP,
                                        expr: Box::new(cond),
                                    })),
                                })),
                                body: Box::new(Stmt::Block(BlockStmt {
                                    span: DUMMY_SP,
                                    stmts: body,
                                })),
                            }));
                            self.chained_iterator = Some(Box::new(AstGenerator::new(
                                self.f,
                                self.cfg,
                                self.instructions,
                                tru.target(),
                                false,
                                None,
                                self.do_while_cond_block,
                            )));
                        }

                        self.stage = AstGeneratorStage::ProcessingDone;
                        return true;
                    }
                }

                self.stage = AstGeneratorStage::IfCheck;
                true
            }
            AstGeneratorStage::IfCheck => {
                let indecies = self.cfg.node_weight(self.node).unwrap();
                let flow_index = indecies.last().unwrap();
                let outgoing_edges = self
                    .cfg
                    .edges_directed(self.node, petgraph::Direction::Outgoing)
                    .collect::<Vec<EdgeReference<'_, bool>>>();
                if outgoing_edges.len() == 2 {
                    //not sure about else if
                    //if, can't have more outgoing edges in hermes bytecode
                    let (tru, fals) = {
                        let mut tru = None;
                        let mut fals = None;
                        for edge in &outgoing_edges {
                            if *edge.weight() {
                                tru = Some(edge);
                            } else {
                                fals = Some(edge);
                            }
                        }
                        (tru.unwrap(), fals.unwrap())
                    };

                    let mut skip_else_false = false;
                    let mut skip_else_true = false;
                    {
                        let mut bfs = Bfs::new(self.cfg, fals.target());
                        while let Some(node) = bfs.next(self.cfg) {
                            if tru.target() == node {
                                skip_else_false = true;
                                break;
                            }
                        }

                        //other way around
                        if !skip_else_false {
                            let mut bfs = Bfs::new(self.cfg, tru.target());
                            while let Some(node) = bfs.next(self.cfg) {
                                if fals.target() == node {
                                    skip_else_true = true;
                                    break;
                                }
                            }
                        }
                    }

                    if skip_else_false {
                        self.stmt_queue.push_back(Stmt::If(IfStmt {
                            span: DUMMY_SP,
                            test: Box::new(jump_inst_to_test(
                                &self.instructions[*flow_index].instruction,
                            )),
                            cons: Box::new(Stmt::Block(BlockStmt {
                                span: DUMMY_SP,
                                stmts: AstGenerator::new(
                                    self.f,
                                    self.cfg,
                                    self.instructions,
                                    tru.target(),
                                    false,
                                    self.while_cond_block,
                                    self.do_while_cond_block,
                                )
                                .collect(),
                            })),
                            alt: None,
                        }));
                        self.after_if_node = Some(fals.target());
                        self.stage = AstGeneratorStage::AfterIf;
                    } else if skip_else_true {
                        self.stmt_queue.push_back(Stmt::If(IfStmt {
                            span: DUMMY_SP,
                            test: Box::new(Expr::Unary(UnaryExpr {
                                //revert the if condition
                                span: DUMMY_SP,
                                op: UnaryOp::Bang,
                                arg: Box::new(Expr::Paren(ParenExpr {
                                    span: DUMMY_SP,
                                    expr: Box::new(jump_inst_to_test(
                                        &self.instructions[*flow_index].instruction,
                                    )),
                                })),
                            })),
                            cons: Box::new(Stmt::Block(BlockStmt {
                                span: DUMMY_SP,
                                stmts: AstGenerator::new(
                                    self.f,
                                    self.cfg,
                                    self.instructions,
                                    fals.target(),
                                    false,
                                    self.while_cond_block,
                                    self.do_while_cond_block,
                                )
                                .collect(),
                            })),
                            alt: None,
                        }));
                        self.after_if_node = Some(tru.target());
                        self.stage = AstGeneratorStage::AfterIf;
                    } else {
                        let mut cons_gen = AstGenerator::new(
                            self.f,
                            self.cfg,
                            self.instructions,
                            tru.target(),
                            false,
                            self.while_cond_block,
                            self.do_while_cond_block,
                        );
                        let cons_stmts = (&mut cons_gen).collect();
                        if cons_gen.is_last_instruction_return {
                            self.stmt_queue.push_back(Stmt::If(IfStmt {
                                span: DUMMY_SP,
                                test: Box::new(jump_inst_to_test(
                                    &self.instructions[*flow_index].instruction,
                                )),
                                cons: Box::new(Stmt::Block(BlockStmt {
                                    span: DUMMY_SP,
                                    stmts: cons_stmts,
                                })),
                                alt: None,
                            }));
                            self.chained_iterator = Some(Box::new(AstGenerator::new(
                                self.f,
                                self.cfg,
                                self.instructions,
                                fals.target(),
                                false,
                                self.while_cond_block,
                                self.do_while_cond_block,
                            )));
                        } else {
                            self.stmt_queue.push_back(Stmt::If(IfStmt {
                                span: DUMMY_SP,
                                test: Box::new(jump_inst_to_test(
                                    &self.instructions[*flow_index].instruction,
                                )),
                                cons: Box::new(Stmt::Block(BlockStmt {
                                    span: DUMMY_SP,
                                    stmts: cons_stmts,
                                })),
                                alt: Some(Box::new(Stmt::Block(BlockStmt {
                                    span: DUMMY_SP,
                                    stmts: AstGenerator::new(
                                        self.f,
                                        self.cfg,
                                        self.instructions,
                                        fals.target(),
                                        false,
                                        self.while_cond_block,
                                        self.do_while_cond_block,
                                    )
                                    .collect(),
                                }))),
                            }));
                        }

                        self.stage = AstGeneratorStage::ProcessingDone;
                    }
                } else if outgoing_edges.len() == 1 {
                    self.chained_iterator = Some(Box::new(AstGenerator::new(
                        self.f,
                        self.cfg,
                        self.instructions,
                        outgoing_edges[0].target(),
                        false,
                        self.while_cond_block,
                        self.do_while_cond_block,
                    )));
                    self.stage = AstGeneratorStage::ProcessingDone;
                } else {
                    self.stage = AstGeneratorStage::ProcessingDone;
                }
                true
            }
            AstGeneratorStage::AfterIf => {
                if let Some(after_if_node) = self.after_if_node {
                    self.chained_iterator = Some(Box::new(AstGenerator::new(
                        self.f,
                        self.cfg,
                        self.instructions,
                        after_if_node,
                        false,
                        self.while_cond_block,
                        self.do_while_cond_block,
                    )));
                }
                self.stage = AstGeneratorStage::ProcessingDone;
                true
            }
            AstGeneratorStage::ProcessingDone => false,
        }
    }
}

impl Iterator for AstGenerator<'_> {
    type Item = Stmt;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.stmt_queue.pop_front() {
            match item {
                Stmt::Return(_) => {
                    self.is_last_instruction_return = true;
                }
                Stmt::Throw(_) => {
                    self.is_last_instruction_return = true;
                }
                _ => (),
            }
            Some(item)
        } else if self.populate_next_stage() {
            self.next()
        } else if let Some(_) = &mut self.chained_iterator {
            *self = *self.chained_iterator.take().unwrap();
            self.next()
        } else {
            None
        }
    }
}

fn jump_inst_to_test(instruction: &Instruction) -> Expr {
    match instruction {
        //should be a conditional jump
        Instruction::JmpTrue {
            relative_offset: _,
            check_value_reg,
        } => {
            return Expr::Ident(Ident {
                span: DUMMY_SP,
                sym: format!("r{check_value_reg}").as_str().into(),
                optional: false,
            })
        }
        Instruction::JmpTrueLong {
            relative_offset: _,
            check_value_reg,
        } => {
            return Expr::Ident(Ident {
                span: DUMMY_SP,
                sym: format!("r{check_value_reg}").as_str().into(),
                optional: false,
            })
        }
        Instruction::JmpFalse {
            relative_offset: _,
            check_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{check_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JmpFalseLong {
            relative_offset: _,
            check_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{check_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JmpUndefined {
            relative_offset: _,
            check_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{check_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: "undefined".into(),
                    optional: false,
                })),
            })
        }
        Instruction::JmpUndefinedLong {
            relative_offset: _,
            check_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{check_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: "undefined".into(),
                    optional: false,
                })),
            })
        }
        Instruction::JLess {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Lt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JLessLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Lt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotLess {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Lt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotLessLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Lt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JLessN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Lt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JLessNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Lt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotLessN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Lt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotLessNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Lt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JLessEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::LtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JLessEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::LtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotLessEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::LtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotLessEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::LtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JLessEqualN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::LtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JLessEqualNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::LtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotLessEqualN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::LtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotLessEqualNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::LtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JGreater {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Gt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JGreaterLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Gt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotGreater {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Gt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotGreaterLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Gt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JGreaterN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Gt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JGreaterNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::Gt,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotGreaterN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Gt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotGreaterNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Gt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JGreaterEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::GtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JGreaterEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::GtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotGreaterEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::GtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotGreaterEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::GtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JGreaterEqualN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::GtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JGreaterEqualNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::GtEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotGreaterEqualN {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::GtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JNotGreaterEqualNLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Unary(UnaryExpr {
                span: DUMMY_SP,
                op: UnaryOp::Bang,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::GtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_value_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })
        }
        Instruction::JEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::NotEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JNotEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::NotEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JStrictEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JStrictEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JStrictNotEqual {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::NotEqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        Instruction::JStrictNotEqualLong {
            relative_offset: _,
            arg1_value_reg,
            arg2_value_reg,
        } => {
            return Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::NotEqEq,
                left: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg1_value_reg}").as_str().into(),
                    optional: false,
                })),
                right: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{arg2_value_reg}").as_str().into(),
                    optional: false,
                })),
            })
        }
        _ => panic!("got a non-jump: {instruction:?}"),
    }
}

fn add_inside_while(body: &mut Vec<Stmt>, to_add: &VecDeque<Stmt>) {
    let mut i = 0;
    //println!("{}", body.len());
    while i < body.len() {
        let stmt = &mut body[i];
        match stmt {
            Stmt::Continue(_) => {
                for i1 in 0..to_add.len() {
                    body.insert(i + i1, to_add[i1].clone())
                }
                i += to_add.len();
            }
            Stmt::If(stmt) => {
                if let Stmt::Block(b) = &mut *stmt.cons {
                    add_inside_while(&mut b.stmts, to_add);
                }
                if let Some(o) = &mut stmt.alt {
                    if let Stmt::Block(b) = &mut **o {
                        add_inside_while(&mut b.stmts, to_add);
                    }
                }
            }
            Stmt::Expr(_) => (),
            Stmt::Return(_) => (),
            _ => unimplemented!("{:?}", stmt),
        }
        i += 1;
    }
}

fn simple_instructions_to_ast(
    f: &BytecodeFile,
    cfg: &Graph<Vec<usize>, bool>,
    node: NodeIndex,
    instructions: &[InstructionInfo<Instruction>],
) -> Vec<Stmt> {
    let mut stmts = Vec::new();
    for index in cfg.node_weight(node).unwrap() {
        match &instructions[*index].instruction {
            Instruction::Mov { dst_reg, src_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{src_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::LoadParam {
                dst_reg,
                param_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident::new(
                        format!("r{dst_reg}").as_str().into(),
                        DUMMY_SP,
                    )))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident::new("arguments".into(), DUMMY_SP))),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Ident(Ident::new(
                                param_index.to_string().as_str().into(),
                                DUMMY_SP,
                            ))),
                        }),
                    })),
                })),
            })),
            Instruction::LoadConstNull { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident::new(
                        format!("r{dst_reg}").as_str().into(),
                        DUMMY_SP,
                    )))),
                    right: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                })),
            })),
            Instruction::LoadConstUndefined { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident::new(
                        format!("r{dst_reg}").as_str().into(),
                        DUMMY_SP,
                    )))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: "undefined".into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::Call1 {
                dst_reg,
                closure_reg,
                argument_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{closure_reg}").as_str().into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "bind".into(),
                                    optional: false,
                                }),
                            }))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }],
                            type_args: None,
                        }))),
                        args: vec![],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::Call2 {
                dst_reg,
                closure_reg,
                argument1_reg,
                argument2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{closure_reg}").as_str().into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "bind".into(),
                                    optional: false,
                                }),
                            }))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument1_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }],
                            type_args: None,
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{argument2_reg}").as_str().into(),
                                optional: false,
                            })),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::Call3 {
                dst_reg,
                closure_reg,
                argument1_reg,
                argument2_reg,
                argument3_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{closure_reg}").as_str().into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "bind".into(),
                                    optional: false,
                                }),
                            }))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument1_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }],
                            type_args: None,
                        }))),
                        args: vec![
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument2_reg}").as_str().into(),
                                    optional: false,
                                })),
                            },
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument3_reg}").as_str().into(),
                                    optional: false,
                                })),
                            },
                        ],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::Call4 {
                dst_reg,
                closure_reg,
                argument1_reg,
                argument2_reg,
                argument3_reg,
                argument4_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{closure_reg}").as_str().into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "bind".into(),
                                    optional: false,
                                }),
                            }))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument1_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }],
                            type_args: None,
                        }))),
                        args: vec![
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument2_reg}").as_str().into(),
                                    optional: false,
                                })),
                            },
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument3_reg}").as_str().into(),
                                    optional: false,
                                })),
                            },
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{argument4_reg}").as_str().into(),
                                    optional: false,
                                })),
                            },
                        ],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::GetByIdShort {
                dst_reg,
                obj_reg,
                string_table_index,
                ..
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    })),
                })),
            })),
            Instruction::GetById {
                dst_reg,
                obj_reg,
                string_table_index,
                ..
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    })),
                })),
            })),
            Instruction::PutById {
                dst_obj_reg,
                value_reg,
                string_table_index,
                ..
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::LoadConstString {
                dst_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Str(Str {
                        span: DUMMY_SP,
                        value: f
                            .get_string(u32::from(*string_table_index))
                            .unwrap_or_default()
                            .as_str()
                            .into(),
                        raw: None,
                    }))),
                })),
            })),
            Instruction::LoadConstUInt8 { dst_reg, value } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: f64::from(*value),
                        raw: None,
                    }))),
                })),
            })),
            Instruction::LoadConstZero { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: 0.0,
                        raw: None,
                    }))),
                })),
            })),
            Instruction::LoadConstFalse { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Bool(Bool {
                        span: DUMMY_SP,
                        value: false,
                    }))),
                })),
            })),
            Instruction::LoadConstTrue { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Bool(Bool {
                        span: DUMMY_SP,
                        value: false,
                    }))),
                })),
            })),
            Instruction::BitAnd {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: if dst_reg == arg1_reg {
                        AssignOp::BitAndAssign
                    } else {
                        AssignOp::Assign
                    },
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(if dst_reg == arg1_reg {
                        Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })
                    } else {
                        Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::BitAnd,
                            left: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{arg1_reg}").as_str().into(),
                                optional: false,
                            })),
                            right: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{arg2_reg}").as_str().into(),
                                optional: false,
                            })),
                        })
                    }),
                })),
            })),
            Instruction::BitOr {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: if dst_reg == arg1_reg {
                        AssignOp::BitOrAssign
                    } else {
                        AssignOp::Assign
                    },
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(if dst_reg == arg1_reg {
                        Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })
                    } else {
                        Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::BitOr,
                            left: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{arg1_reg}").as_str().into(),
                                optional: false,
                            })),
                            right: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{arg2_reg}").as_str().into(),
                                optional: false,
                            })),
                        })
                    }),
                })),
            })),
            Instruction::StrictNeq {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::NotEqEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::TypeOf { dst_reg, src_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::TypeOf,
                        arg: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{src_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Ret { value_reg } => stmts.push(Stmt::Return(ReturnStmt {
                span: DUMMY_SP,
                arg: Some(Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{value_reg}").as_str().into(),
                    optional: false,
                }))),
            })),
            Instruction::GetEnvironment {
                dst_reg,
                num_environments,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "get_environment".into(),
                            optional: false,
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{num_environments}").as_str().into(),
                                optional: false,
                            })),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::LoadFromEnvironment {
                dst_reg,
                env_reg,
                env_slot_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{env_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "get".into(),
                                optional: false,
                            }),
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*env_slot_index),
                                raw: None,
                            }))),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::LoadFromEnvironmentL {
                dst_reg,
                env_reg,
                env_slot_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{env_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "get".into(),
                                optional: false,
                            }),
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*env_slot_index),
                                raw: None,
                            }))),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::Unreachable => (),
            Instruction::NewObjectWithBuffer {
                dst_reg,
                size_hint: _,
                static_elements_num: _,
                object_key_buffer_index: _,
                object_value_buffer_index: _,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props: Vec::new(),
                    })),
                })),
            })),
            Instruction::NewObjectWithBufferLong {
                dst_reg,
                preallocation_size_hint: _,
                static_elements_num: _,
                object_key_buffer_index: _,
                object_value_buffer_index: _,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props: Vec::new(),
                    })),
                })),
            })),
            Instruction::NewObject { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props: Vec::new(),
                    })),
                })),
            })),
            Instruction::NewObjectWithParent {
                dst_reg,
                parent_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "Object".into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "create".into(),
                                optional: false,
                            }),
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{parent_reg}").as_str().into(),
                                optional: false,
                            })),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::NewArrayWithBuffer {
                dst_reg,
                preallocation_size_hint: _,
                static_elements_num: _,
                array_buffer_table_index: _,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Array(ArrayLit {
                        span: DUMMY_SP,
                        elems: Vec::new(),
                    })),
                })),
            })),
            Instruction::NewArrayWithBufferLong {
                dst_reg,
                preallocation_size_hint: _,
                static_elements_num: _,
                array_buffer_table_index: _,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Array(ArrayLit {
                        span: DUMMY_SP,
                        elems: Vec::new(),
                    })),
                })),
            })),
            Instruction::NewArray { dst_reg, size: _ } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Array(ArrayLit {
                        span: DUMMY_SP,
                        elems: Vec::new(),
                    })),
                })),
            })),
            Instruction::MovLong { dst_reg, src_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{src_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::Negate { dst_reg, src_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::Minus,
                        arg: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{src_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Not { dst_reg, src_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::Bang,
                        arg: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{src_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::BitNot { dst_reg, src_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::Tilde,
                        arg: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{src_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Eq {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::EqEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::StrictEq {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::EqEqEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Neq {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::NotEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Less {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Lt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::LessEq {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::LtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Greater {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Gt,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::GreaterEq {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::GtEq,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Add {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Add,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::AddN {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Add,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Mul {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Mul,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::MulN {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Mul,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Div {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Div,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::DivN {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Div,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Mod {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Mod,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Sub {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Sub,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::SubN {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::Sub,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::LShift {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::LShift,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::RShift {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::RShift,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::URshift {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::ZeroFillRShift,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::BitXor {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::BitXor,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::Inc { dst_reg, arg_reg } => {
                if *dst_reg == *arg_reg {
                    stmts.push(Stmt::Expr(ExprStmt {
                        span: DUMMY_SP,
                        expr: Box::new(Expr::Update(UpdateExpr {
                            span: DUMMY_SP,
                            op: UpdateOp::PlusPlus,
                            prefix: false,
                            arg: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{arg_reg}").as_str().into(),
                                optional: false,
                            })),
                        })),
                    }))
                } else {
                    stmts.push(Stmt::Expr(ExprStmt {
                        span: DUMMY_SP,
                        expr: Box::new(Expr::Assign(AssignExpr {
                            span: DUMMY_SP,
                            op: AssignOp::Assign,
                            left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{dst_reg}").as_str().into(),
                                optional: false,
                            }))),
                            right: Box::new(Expr::Bin(BinExpr {
                                span: DUMMY_SP,
                                op: BinaryOp::Add,
                                left: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{arg_reg}").as_str().into(),
                                    optional: false,
                                })),
                                right: Box::new(Expr::Lit(Lit::Num(Number {
                                    span: DUMMY_SP,
                                    value: 1.0,
                                    raw: None,
                                }))),
                            })),
                        })),
                    }))
                }
            }
            Instruction::Dec { dst_reg, arg_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Update(UpdateExpr {
                        span: DUMMY_SP,
                        op: UpdateOp::MinusMinus,
                        prefix: false,
                        arg: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::InstanceOf {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::InstanceOf,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::IsIn {
                dst_reg,
                arg1_reg,
                arg2_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::In,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg1_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{arg2_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::StoreToEnvironment {
                env_reg,
                env_slot_index,
                value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{env_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "store".into(),
                            optional: false,
                        }),
                    }))),
                    args: vec![
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*env_slot_index),
                                raw: None,
                            }))),
                        },
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        },
                    ],
                    type_args: None,
                })),
            })),
            Instruction::StoreToEnvironmentL {
                env_reg,
                env_slot_index,
                value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{env_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "store".into(),
                            optional: false,
                        }),
                    }))),
                    args: vec![
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*env_slot_index),
                                raw: None,
                            }))),
                        },
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        },
                    ],
                    type_args: None,
                })),
            })),
            Instruction::StoreNPToEnvironment {
                env_reg,
                env_slot_index,
                value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{env_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "store".into(),
                            optional: false,
                        }),
                    }))),
                    args: vec![
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*env_slot_index),
                                raw: None,
                            }))),
                        },
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        },
                    ],
                    type_args: None,
                })),
            })),
            Instruction::StoreNPToEnvironmentL {
                env_reg,
                env_slot_index,
                value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{env_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "store".into(),
                            optional: false,
                        }),
                    }))),
                    args: vec![
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*env_slot_index),
                                raw: None,
                            }))),
                        },
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        },
                    ],
                    type_args: None,
                })),
            })),
            Instruction::GetGlobalObject { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: "globalThis".into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::GetNewTarget { dst_reg: _ } => todo!(),
            Instruction::CreateEnvironment { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "create_environment".into(),
                            optional: false,
                        }))),
                        args: vec![],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::DeclareGlobalVar { string_table_index } => {
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "globalThis".into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                                optional: false,
                            }),
                        }))),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "undefined".into(),
                            optional: false,
                        })),
                    })),
                }))
            }
            Instruction::GetByIdLong {
                dst_reg,
                obj_reg,
                cache_index: _,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                            optional: false,
                        }),
                    })),
                })),
            })),
            Instruction::TryGetById {
                dst_reg,
                obj_reg,
                cache_index: _,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    })),
                })),
            })),
            Instruction::TryGetByIdLong {
                dst_reg,
                obj_reg,
                cache_index: _,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                            optional: false,
                        }),
                    })),
                })),
            })),
            Instruction::PutByIdLong {
                dst_obj_reg,
                value_reg,
                cache_index: _,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::TryPutById {
                dst_obj_reg,
                value_reg,
                cache_index: _,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::TryPutByIdLong {
                dst_obj_reg,
                value_reg,
                cache_index: _,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            //Todo: probably via defineProperty
            Instruction::PutNewOwnByIdShort {
                dst_obj_reg,
                value_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::PutNewOwnById {
                dst_obj_reg,
                value_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f
                                .get_string(u32::from(*string_table_index))
                                .unwrap()
                                .as_str()
                                .into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::PutNewOwnByIdLong {
                dst_obj_reg,
                value_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                            optional: false,
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::PutNewOwnNEById {
                dst_obj_reg: _,
                value_reg: _,
                string_table_index: _,
            } => todo!(),
            Instruction::PutNewOwnNEByIdLong {
                dst_obj_reg: _,
                value_reg: _,
                string_table_index: _,
            } => todo!(),
            Instruction::PutOwnByIndex {
                dst_obj_reg,
                value_reg,
                index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*index),
                                raw: None,
                            }))),
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::PutOwnByIndexL {
                dst_obj_reg,
                value_reg,
                index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: f64::from(*index),
                                raw: None,
                            }))),
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::PutOwnByVal {
                dst_obj_reg,
                value_reg,
                property_name_reg,
                enumerable,
            } => {
                if *enumerable {
                    stmts.push(Stmt::Expr(ExprStmt {
                        span: DUMMY_SP,
                        expr: Box::new(Expr::Assign(AssignExpr {
                            span: DUMMY_SP,
                            op: AssignOp::Assign,
                            left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{dst_obj_reg}").as_str().into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Computed(ComputedPropName {
                                    span: DUMMY_SP,
                                    expr: Box::new(Expr::Ident(Ident {
                                        span: DUMMY_SP,
                                        sym: format!("r{property_name_reg}").as_str().into(),
                                        optional: false,
                                    })),
                                }),
                            }))),
                            right: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        })),
                    }))
                } else {
                    stmts.push(Stmt::Expr(ExprStmt {
                        span: DUMMY_SP,
                        expr: Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "Object".into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "defineProperty".into(),
                                    optional: false,
                                }),
                            }))),
                            args: vec![
                                ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Ident(Ident {
                                        span: DUMMY_SP,
                                        sym: format!("r{dst_obj_reg}").as_str().into(),
                                        optional: false,
                                    })),
                                },
                                ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Ident(Ident {
                                        span: DUMMY_SP,
                                        sym: format!("r{property_name_reg}").as_str().into(),
                                        optional: false,
                                    })),
                                },
                                ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Object(ObjectLit {
                                        span: DUMMY_SP,
                                        props: vec![
                                            PropOrSpread::Prop(Box::new(Prop::KeyValue(
                                                KeyValueProp {
                                                    key: PropName::Ident(Ident {
                                                        span: DUMMY_SP,
                                                        sym: "value".into(),
                                                        optional: false,
                                                    }),
                                                    value: Box::new(Expr::Ident(Ident {
                                                        span: DUMMY_SP,
                                                        sym: format!("r{value_reg}")
                                                            .as_str()
                                                            .into(),
                                                        optional: false,
                                                    })),
                                                },
                                            ))),
                                            PropOrSpread::Prop(Box::new(Prop::KeyValue(
                                                KeyValueProp {
                                                    key: PropName::Ident(Ident {
                                                        span: DUMMY_SP,
                                                        sym: "enumerable".into(),
                                                        optional: false,
                                                    }),
                                                    value: Box::new(Expr::Lit(Lit::Bool(Bool {
                                                        span: DUMMY_SP,
                                                        value: false,
                                                    }))),
                                                },
                                            ))),
                                        ],
                                    })),
                                },
                            ],
                            type_args: None,
                        })),
                    }))
                }
            }
            Instruction::DelById {
                dst_reg,
                obj_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::Delete,
                        arg: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{obj_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: f
                                    .get_string(u32::from(*string_table_index))
                                    .unwrap()
                                    .as_str()
                                    .into(),
                                optional: false,
                            }),
                        })),
                    })),
                })),
            })),
            Instruction::DelByIdLong {
                dst_reg,
                obj_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::Delete,
                        arg: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{obj_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: f.get_string(*string_table_index).unwrap().as_str().into(),
                                optional: false,
                            }),
                        })),
                    })),
                })),
            })),
            Instruction::GetByVal {
                dst_reg,
                obj_reg,
                index_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{index_reg}").as_str().into(),
                                optional: false,
                            })),
                        }),
                    })),
                })),
            })),
            Instruction::PutByVal {
                dst_obj_reg,
                index_reg,
                value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{index_reg}").as_str().into(),
                                optional: false,
                            })),
                        }),
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::DelByVal {
                dst_reg,
                obj_reg,
                index_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Unary(UnaryExpr {
                        span: DUMMY_SP,
                        op: UnaryOp::Delete,
                        arg: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{obj_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Computed(ComputedPropName {
                                span: DUMMY_SP,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{index_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }),
                        })),
                    })),
                })),
            })),
            Instruction::PutOwnGetterSetterByVal {
                obj_reg,
                property_name_reg,
                getter_closure_reg,
                setter_closure_reg,
                enumerable,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "Object".into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "defineProperty".into(),
                            optional: false,
                        }),
                    }))),
                    args: vec![
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{obj_reg}").as_str().into(),
                                optional: false,
                            })),
                        },
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{property_name_reg}").as_str().into(),
                                optional: false,
                            })),
                        },
                        ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Object(ObjectLit {
                                span: DUMMY_SP,
                                props: vec![
                                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                        key: PropName::Ident(Ident {
                                            span: DUMMY_SP,
                                            sym: "get".into(),
                                            optional: false,
                                        }),
                                        value: Box::new(Expr::Ident(Ident {
                                            span: DUMMY_SP,
                                            sym: format!("r{getter_closure_reg}").as_str().into(),
                                            optional: false,
                                        })),
                                    }))),
                                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                        key: PropName::Ident(Ident {
                                            span: DUMMY_SP,
                                            sym: "set".into(),
                                            optional: false,
                                        }),
                                        value: Box::new(Expr::Ident(Ident {
                                            span: DUMMY_SP,
                                            sym: format!("r{setter_closure_reg}").as_str().into(),
                                            optional: false,
                                        })),
                                    }))),
                                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                        key: PropName::Ident(Ident {
                                            span: DUMMY_SP,
                                            sym: "enumerable".into(),
                                            optional: false,
                                        }),
                                        value: Box::new(Expr::Lit(Lit::Bool(Bool {
                                            span: DUMMY_SP,
                                            value: *enumerable,
                                        }))),
                                    }))),
                                ],
                            })),
                        },
                    ],
                    type_args: None,
                })),
            })),
            Instruction::GetPNameList {
                dst_reg,
                obj_reg,
                iterating_index_reg,
                property_list_size_reg,
            } => {
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{iterating_index_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::Lit(Lit::Num(Number {
                            span: DUMMY_SP,
                            value: 0.0,
                            raw: None,
                        }))),
                    })),
                }));
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "Object".into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: "keys".into(),
                                    optional: false,
                                }),
                            }))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{obj_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }],
                            type_args: None,
                        })),
                    })),
                }));
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{property_list_size_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{dst_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "length".into(),
                                optional: false,
                            }),
                        })),
                    })),
                }));
            }
            Instruction::GetNextPName {
                dst_reg,
                properties_array_reg,
                obj_reg: _,
                iterating_index_reg,
                property_list_size_reg: _,
            } => {
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{properties_array_reg}").as_str().into(),
                                optional: false,
                            })),
                            prop: MemberProp::Computed(ComputedPropName {
                                span: DUMMY_SP,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{iterating_index_reg}").as_str().into(),
                                    optional: false,
                                })),
                            }),
                        })),
                    })),
                }));
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Update(UpdateExpr {
                        span: DUMMY_SP,
                        op: UpdateOp::PlusPlus,
                        prefix: false,
                        arg: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{iterating_index_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                }));
            }
            Instruction::Call {
                dst_reg,
                closure_reg,
                arguments_len,
            } => {
                let mut arguments = Vec::new();
                for s in &stmts[stmts.len() - *arguments_len as usize..stmts.len()] {
                    if let Stmt::Expr(s) = s {
                        if let Expr::Assign(s) = &*s.expr {
                            arguments.push(ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(s.left.as_ident().unwrap().clone())),
                            });
                        }
                    }
                }
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Call(CallExpr {
                                span: DUMMY_SP,
                                callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                    span: DUMMY_SP,
                                    obj: Box::new(Expr::Ident(Ident {
                                        span: DUMMY_SP,
                                        sym: format!("r{closure_reg}").as_str().into(),
                                        optional: false,
                                    })),
                                    prop: MemberProp::Ident(Ident {
                                        span: DUMMY_SP,
                                        sym: "bind".into(),
                                        optional: false,
                                    }),
                                }))),
                                args: vec![arguments[0].clone()],
                                type_args: None,
                            }))),
                            args: arguments[1..].to_vec(),
                            type_args: None,
                        })),
                    })),
                }));
            }
            Instruction::Construct {
                dst_reg,
                closure_reg,
                arguments_len,
            } => {
                let mut arguments = Vec::new();
                for s in &stmts[stmts.len() - *arguments_len as usize..stmts.len()] {
                    if let Stmt::Expr(s) = s {
                        if let Expr::Assign(s) = &*s.expr {
                            arguments.push(ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(s.left.as_ident().unwrap().clone())),
                            });
                        }
                    }
                }
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::New(NewExpr {
                            span: DUMMY_SP,
                            callee: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{closure_reg}").as_str().into(),
                                optional: false,
                            })),
                            args: Some(arguments),
                            type_args: None,
                        })),
                    })),
                }))
            }
            Instruction::CallDirect {
                dst_reg: _,
                arguments_len: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CallLong {
                dst_reg: _,
                closure_reg: _,
                arguments_len: _,
            } => todo!(),
            Instruction::ConstructLong {
                dst_reg: _,
                closure_reg: _,
                arguments_len: _,
            } => todo!(),
            Instruction::CallDirectLongIndex {
                dst_reg: _,
                arguments_len: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CallBuiltin {
                dst_reg: _,
                builtin_number: _,
                arguments_len: _,
            } => todo!(),
            Instruction::CallBuiltinLong {
                dst_reg: _,
                builtin_number: _,
                arguments_len: _,
            } => todo!(),
            Instruction::GetBuiltinClosure {
                dst_reg,
                builtin_number,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new({
                        let builtin = *JS_BUILTINS.get(*builtin_number as usize).unwrap();
                        if builtin.contains('.') {
                            let mut s = builtin.split('.');
                            Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: s.next().unwrap().into(),
                                    optional: false,
                                })),
                                prop: MemberProp::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: s.next().unwrap().into(),
                                    optional: false,
                                }),
                            })
                        } else {
                            Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: builtin.into(),
                                optional: false,
                            })
                        }
                    }),
                })),
            })),
            Instruction::Catch { dst_reg: _ } => todo!(),
            Instruction::DirectEval { dst_reg, value_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "eval".into(),
                            optional: false,
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::Throw { value_reg } => stmts.push(Stmt::Throw(ThrowStmt {
                span: DUMMY_SP,
                arg: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    sym: format!("r{value_reg}").as_str().into(),
                    optional: false,
                })),
            })),
            Instruction::ThrowIfEmpty {
                dst_reg: _,
                checked_value_reg: _,
            } => todo!(),
            Instruction::Debugger => stmts.push(Stmt::Debugger(DebuggerStmt { span: DUMMY_SP })),
            Instruction::AsyncBreakCheck => (),
            Instruction::ProfilePoint {
                function_local_profile_point_index: _,
            } => (),
            Instruction::CreateClosure {
                dst_reg,
                current_environment_reg: _,
                function_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("f{function_table_index}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::CreateClosureLongIndex {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CreateGeneratorClosure {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CreateGeneratorClosureLongIndex {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CreateAsyncClosure {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CreateAsyncClosureLongIndex {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CreateThis {
                dst_reg,
                prototype_reg,
                constructor_closure_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "Object".into(),
                                optional: false,
                            })),
                            prop: MemberProp::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "create".into(),
                                optional: false,
                            }),
                        }))),
                        args: vec![
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident {
                                    span: DUMMY_SP,
                                    sym: format!("r{prototype_reg}").as_str().into(),
                                    optional: false,
                                })),
                            },
                            ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Object(ObjectLit {
                                    span: DUMMY_SP,
                                    props: vec![PropOrSpread::Prop(Box::new(Prop::KeyValue(
                                        KeyValueProp {
                                            key: PropName::Ident(Ident {
                                                span: DUMMY_SP,
                                                sym: "constructor".into(),
                                                optional: false,
                                            }),
                                            value: Box::new(Expr::Object(ObjectLit {
                                                span: DUMMY_SP,
                                                props: vec![PropOrSpread::Prop(Box::new(
                                                    Prop::KeyValue(KeyValueProp {
                                                        key: PropName::Ident(Ident {
                                                            span: DUMMY_SP,
                                                            sym: "value".into(),
                                                            optional: false,
                                                        }),
                                                        value: Box::new(Expr::Ident(Ident {
                                                            span: DUMMY_SP,
                                                            sym: format!(
                                                                "r{constructor_closure_reg}"
                                                            )
                                                            .as_str()
                                                            .into(),
                                                            optional: false,
                                                        })),
                                                    }),
                                                ))],
                                            })),
                                        },
                                    )))],
                                })),
                            },
                        ],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::SelectObject {
                dst_reg,
                this_obj_reg,
                return_value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Cond(CondExpr {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::InstanceOf,
                            left: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{return_value_reg}").as_str().into(),
                                optional: false,
                            })),
                            right: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "Object".into(),
                                optional: false,
                            })),
                        })),
                        cons: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{return_value_reg}").as_str().into(),
                            optional: false,
                        })),
                        alt: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{this_obj_reg}").as_str().into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::LoadParamLong {
                dst_reg,
                param_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident::new(
                        format!("r{dst_reg}").as_str().into(),
                        DUMMY_SP,
                    )))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident::new("arguments".into(), DUMMY_SP))),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Ident(Ident::new(
                                param_index.to_string().as_str().into(),
                                DUMMY_SP,
                            ))),
                        }),
                    })),
                })),
            })),
            Instruction::LoadConstInt { dst_reg, value } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: f64::from(*value),
                        raw: None,
                    }))),
                })),
            })),
            Instruction::LoadConstDouble { dst_reg, value } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: *value,
                        raw: None,
                    }))),
                })),
            })),
            Instruction::LoadConstBigInt {
                dst_reg: _,
                bigint_table_index: _,
            } =>
            /*stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::BigInt(BigInt {
                        span: DUMMY_SP,
                        value: Box::new(f.get_bigint(*bigint_table_index)),
                        raw: None
                    }))),
                })),
            }))*/
            {
                todo!()
            }
            Instruction::LoadConstBigIntLongIndex {
                dst_reg: _,
                bigint_table_index: _,
            } => todo!(),
            Instruction::LoadConstStringLongIndex {
                dst_reg,
                string_table_index,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Lit(Lit::Str(Str {
                        span: DUMMY_SP,
                        value: f
                            .get_string(*string_table_index)
                            .unwrap_or_default()
                            .as_str()
                            .into(),
                        raw: None,
                    }))),
                })),
            })),
            Instruction::LoadConstEmpty { dst_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident::new(
                        format!("r{dst_reg}").as_str().into(),
                        DUMMY_SP,
                    )))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: "undefined".into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::CoerceThisNS {
                dst_reg,
                this_value_reg,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{this_value_reg}").as_str().into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::LoadThisNS { dst_this_obj_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_this_obj_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: "this".into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::ToNumber { dst_reg, value_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Call(CallExpr {
                        span: DUMMY_SP,
                        callee: Callee::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "Number".into(),
                            optional: false,
                        }))),
                        args: vec![ExprOrSpread {
                            spread: None,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        }],
                        type_args: None,
                    })),
                })),
            })),
            Instruction::ToNumeric {
                dst_reg: _,
                value_reg: _,
            } => todo!(),
            Instruction::ToInt32 { dst_reg, value_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::BitOr,
                        left: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{value_reg}").as_str().into(),
                            optional: false,
                        })),
                        right: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "0".into(),
                            optional: false,
                        })),
                    })),
                })),
            })),
            Instruction::AddEmptyString { dst_reg, value_reg } => {
                stmts.push(Stmt::Expr(ExprStmt {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: DUMMY_SP,
                        op: AssignOp::Assign,
                        left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: format!("r{dst_reg}").as_str().into(),
                            optional: false,
                        }))),
                        right: Box::new(Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::Add,
                            left: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: "\"\"".into(),
                                optional: false,
                            })),
                            right: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{value_reg}").as_str().into(),
                                optional: false,
                            })),
                        })),
                    })),
                }))
            }
            Instruction::GetArgumentsPropByVal {
                dst_reg,
                index_reg,
                lazy_loaded_reg: _,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "arguments".into(),
                            optional: false,
                        })),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Ident(Ident {
                                span: DUMMY_SP,
                                sym: format!("r{index_reg}").as_str().into(),
                                optional: false,
                            })),
                        }),
                    })),
                })),
            })),
            Instruction::GetArgumentsLength {
                dst_reg,
                lazy_loaded_reg: _,
            } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{dst_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "arguments".into(),
                            optional: false,
                        })),
                        prop: MemberProp::Ident(Ident {
                            span: DUMMY_SP,
                            sym: "length".into(),
                            optional: false,
                        }),
                    })),
                })),
            })),
            Instruction::ReifyArguments { lazy_loaded_reg } => stmts.push(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: PatOrExpr::Expr(Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: format!("r{lazy_loaded_reg}").as_str().into(),
                        optional: false,
                    }))),
                    right: Box::new(Expr::Ident(Ident {
                        span: DUMMY_SP,
                        sym: "arguments".into(),
                        optional: false,
                    })),
                })),
            })),
            Instruction::CreateRegExp {
                dst_reg: _,
                pattern_string_index: _,
                flags_string_index: _,
                regexp_table_index: _,
            } => todo!(),
            Instruction::SwitchImm {
                value_reg: _,
                relative_jump_table_offset: _,
                relative_default_jump_offset: _,
                min_value: _,
                max_value: _,
            } => todo!(),
            Instruction::StartGenerator => todo!(),
            Instruction::ResumeGenerator {
                dst_result_reg: _,
                is_return: _,
            } => todo!(),
            Instruction::CompleteGenerator => todo!(),
            Instruction::CreateGenerator {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::CreateGeneratorLongIndex {
                dst_reg: _,
                current_environment_reg: _,
                function_table_index: _,
            } => todo!(),
            Instruction::IteratorBegin {
                dst_reg: _,
                source_reg: _,
            } => todo!(),
            Instruction::IteratorNext {
                dst_reg: _,
                iterator_or_index_reg: _,
                source_reg: _,
            } => todo!(),
            Instruction::IteratorClose {
                iterator_or_index_reg: _,
                ignore_inner_exception: _,
            } => todo!(),

            Instruction::Jmp { relative_offset: _ } => (),
            Instruction::JmpLong { relative_offset: _ } => (),
            Instruction::JmpTrue {
                relative_offset: _,
                check_value_reg: _,
            } => (),
            Instruction::JmpTrueLong {
                relative_offset: _,
                check_value_reg: _,
            } => (),
            Instruction::JmpFalse {
                relative_offset: _,
                check_value_reg: _,
            } => (),
            Instruction::JmpFalseLong {
                relative_offset: _,
                check_value_reg: _,
            } => (),
            Instruction::JmpUndefined {
                relative_offset: _,
                check_value_reg: _,
            } => (),
            Instruction::JmpUndefinedLong {
                relative_offset: _,
                check_value_reg: _,
            } => (),
            Instruction::SaveGenerator { relative_offset: _ } => todo!(),
            Instruction::SaveGeneratorLong { relative_offset: _ } => todo!(),
            Instruction::JLess {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLess {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessEqualN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JLessEqualNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessEqualN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotLessEqualNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreater {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreater {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterEqualN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JGreaterEqualNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterEqualN {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotGreaterEqualNLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JNotEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JStrictEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JStrictEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JStrictNotEqual {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),
            Instruction::JStrictNotEqualLong {
                relative_offset: _,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => (),

            Instruction::Add32 {
                dst_reg: _,
                arg1_reg: _,
                arg2_reg: _,
            } => todo!(),
            Instruction::Sub32 {
                dst_reg: _,
                arg1_reg: _,
                arg2_reg: _,
            } => todo!(),
            Instruction::Mul32 {
                dst_reg: _,
                arg1_reg: _,
                arg2_reg: _,
            } => todo!(),
            Instruction::Divi32 {
                dst_reg: _,
                arg1_reg: _,
                arg2_reg: _,
            } => todo!(),
            Instruction::Divu32 {
                dst_reg: _,
                arg1_reg: _,
                arg2_reg: _,
            } => todo!(),
            Instruction::Loadi8 {
                dst_reg: _,
                _unused_reg,
                heap_index_reg: _,
            } => todo!(),
            Instruction::Loadu8 {
                dst_reg: _,
                _unused_reg,
                heap_index_reg: _,
            } => todo!(),
            Instruction::Loadi16 {
                dst_reg: _,
                _unused_reg,
                heap_index_reg: _,
            } => todo!(),
            Instruction::Loadu16 {
                dst_reg: _,
                _unused_reg,
                heap_index_reg: _,
            } => todo!(),
            Instruction::Loadi32 {
                dst_reg: _,
                _unused_reg,
                heap_index_reg: _,
            } => todo!(),
            Instruction::Loadu32 {
                dst_reg: _,
                _unused_reg,
                heap_index_reg: _,
            } => todo!(),
            Instruction::Store8 {
                _unused_reg,
                heap_index_reg: _,
                value_reg: _,
            } => todo!(),
            Instruction::Store16 {
                _unused_reg,
                heap_index_reg: _,
                value_reg: _,
            } => todo!(),
            Instruction::Store32 {
                _unused_reg,
                heap_index_reg: _,
                value_reg: _,
            } => todo!(),
        }
    }

    stmts
}
