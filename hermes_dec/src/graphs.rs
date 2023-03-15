use std::collections::{HashMap, HashSet};

use petgraph::visit::{Dfs, EdgeRef};
use petgraph::{stable_graph::NodeIndex, Directed, Graph};

use crate::{bytecode::v93::Instruction, hermes_file_reader::InstructionInfo};

pub fn construct_flow_graph(
    instructions: &[InstructionInfo<Instruction>],
) -> Graph<(), bool, Directed, u32> {
    let mut flow_graph: Graph<(), bool, Directed, u32> = Graph::new();
    for _ in instructions {
        flow_graph.add_node(());
    }
    //for _ in 0..instructions.len() {
    //    flow_graph.add_node(());
    //}
    let mut instruction_index = 0;

    while instruction_index < instructions.len() {
        let instruction_info = &instructions[instruction_index];
        let instruction = &instruction_info.instruction;
        match instruction {
            Instruction::Jmp { relative_offset } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    false,
                );
            }
            Instruction::JmpLong { relative_offset } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    false,
                );
            }
            Instruction::JmpTrue {
                relative_offset,
                check_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JmpTrueLong {
                relative_offset,
                check_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JmpFalse {
                relative_offset,
                check_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JmpFalseLong {
                relative_offset,
                check_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JmpUndefined {
                relative_offset,
                check_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JmpUndefinedLong {
                relative_offset,
                check_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLess {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLess {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessEqualN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JLessEqualNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessEqualN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotLessEqualNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreater {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreater {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterEqualN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JGreaterEqualNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterEqualN {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotGreaterEqualNLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JNotEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JStrictEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JStrictEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JStrictNotEqual {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            i32::from(*relative_offset),
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::JStrictNotEqualLong {
                relative_offset,
                arg1_value_reg: _,
                arg2_value_reg: _,
            } => {
                flow_graph.add_edge(
                    NodeIndex::new(instruction_index),
                    NodeIndex::new(
                        get_instruction_by_offset(
                            instructions,
                            instruction_index,
                            *relative_offset,
                        )
                        .unwrap(),
                    ),
                    true,
                );
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
            Instruction::Ret { value_reg: _ } => {}
            Instruction::Throw { value_reg: _ } => {}
            _ => {
                if instruction_index < instructions.len() - 1 {
                    flow_graph.add_edge(
                        NodeIndex::new(instruction_index),
                        NodeIndex::new(instruction_index + 1),
                        false,
                    );
                }
            }
        };
        instruction_index += 1;
    }

    flow_graph
}

pub fn construct_cfg<N, E: Copy>(
    flow_graph: &Graph<N, E, Directed, u32>,
) -> Graph<Vec<usize>, E, Directed, u32> {
    let mut cfg: Graph<Vec<usize>, E, Directed, u32> = Graph::new();

    let mut current_block = Vec::new();
    let mut dfs = Dfs::new(flow_graph, NodeIndex::new(0));
    let mut visited = HashSet::new();
    while let Some(vertex) = dfs.next(flow_graph) {
        visited.insert(vertex);

        let num_edges_incoming = flow_graph
            .edges_directed(vertex, petgraph::Direction::Incoming)
            .count();
        let num_edges_outgoing = flow_graph
            .edges_directed(vertex, petgraph::Direction::Outgoing)
            .count();
        //can't be 0 unless end of a function(which we don't care about)

        if num_edges_incoming >= 2 && !current_block.is_empty() {
            cfg.add_node(current_block);
            current_block = Vec::new();
        }

        current_block.push(vertex.index());

        if num_edges_outgoing >= 2 {
            //if
            cfg.add_node(current_block);
            current_block = Vec::new();
        } else if num_edges_outgoing == 0 {
            cfg.add_node(current_block);
            current_block = Vec::new();
        } else {
            //1
            if visited.contains(
                &flow_graph
                    .edges_directed(vertex, petgraph::Direction::Outgoing)
                    .next()
                    .unwrap()
                    .target(),
            ) {
                cfg.add_node(current_block);
                current_block = Vec::new();
            }
        }
    }

    let mut add_edges = Vec::new();
    for (i, vertex) in cfg.raw_nodes().iter().enumerate() {
        let index = vertex.weight[0];
        let incoming =
            flow_graph.edges_directed(NodeIndex::new(index), petgraph::Direction::Incoming);

        let mut set = HashMap::new();
        for edge in incoming {
            set.insert(edge.source(), *edge.weight());
        }
        for (i2, vertex2) in cfg.raw_nodes().iter().enumerate() {
            let index2 = vertex2.weight.last().unwrap(); //we shouldn't have empty weights
            let k_i = NodeIndex::new(*index2);
            if set.contains_key(&k_i) {
                add_edges.push((
                    NodeIndex::<u32>::new(i),
                    NodeIndex::<u32>::new(i2),
                    set[&k_i],
                ));
            }
        }
    }
    for edge in add_edges {
        cfg.add_edge(edge.1, edge.0, edge.2);
    }

    cfg
}

fn get_instruction_by_offset(
    instructions: &[InstructionInfo<Instruction>],
    mut current_instruction_index: usize,
    relative_offset: i32,
) -> Option<usize> {
    let end_offset = instructions[current_instruction_index]
        .offset
        .wrapping_add_signed(relative_offset);
    while current_instruction_index < instructions.len() {
        if instructions[current_instruction_index].offset == end_offset {
            return Some(current_instruction_index);
        }
        if current_instruction_index == 0 {
            //prevent overflow
            break;
        }
        current_instruction_index =
            current_instruction_index.wrapping_add_signed(relative_offset.signum() as isize);
    }
    None
}
