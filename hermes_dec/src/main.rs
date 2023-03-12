#![feature(cursor_remaining)]

use petgraph::stable_graph::NodeIndex;
use std::env;
use std::fs::File;
use std::io::stdout;
use std::io::BufWriter;
use std::io::Cursor;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;
use std::str::FromStr;
use swc_common::sync::Lrc;
use swc_common::FilePathMapping;
use swc_common::SourceMap;
use swc_ecma_ast::{Decl, FnDecl, Ident, Program, Script, Stmt};
use swc_ecma_codegen::text_writer::JsWriter;

use hermes_file_reader::BytecodeFile;
use swc_common::DUMMY_SP;
use swc_ecma_ast::BlockStmt;
use swc_ecma_ast::EsVersion;
use swc_ecma_ast::Function;
use swc_ecma_codegen::Emitter;

use crate::bytecode::v93::Instruction;
use crate::generate_ast::generate_ast;
use crate::graphs::construct_cfg;
use crate::graphs::construct_flow_graph;

mod bytecode;
mod generate_ast;
mod graphs;
mod hermes_file_reader;

fn print_help() {
    println!("Correct usage: hermes_dec [bundle_path] [arg2]");
    println!("bundle_path is the path to an index.android.bundle from unpacked hermes application");
    println!("Possible options for arg2: \"show_functions\", \"disassemble function_id [output_path]\", \"strings [output_path]\"");
}

fn main() {
    let mut args = env::args();
    args.next();
    let bundle_path = args.next();
    let mut bundle_path = if let Some(bundle_path) = bundle_path {
        let bundle_path = PathBuf::from_str(&bundle_path).unwrap();
        if !bundle_path.is_file() {
            print_help();
            return;
        }
        match File::open(bundle_path.clone()) {
            Ok(f) => f,
            Err(e) => {
                println!("Error while opening {}: {}", bundle_path.display(), e);
                return;
            }
        }
    } else {
        print_help();
        return;
    };
    let arg2 = args.next();
    if let Some(arg2) = arg2 {
        match arg2.as_str() {
            "show_functions" => {
                let mut buf = Vec::new();
                match bundle_path.read_to_end(&mut buf) {
                    Ok(_) => (),
                    Err(e) => {
                        println!("Error while reading provided file: {e}");
                        return;
                    }
                };
                let mut cursor = Cursor::new(buf.as_slice());
                let f = BytecodeFile::from_reader(&mut cursor).unwrap();
                for (i, header) in f.function_headers.iter().enumerate() {
                    println!(
                        "Function {i}: (name: {}, offset: {}, size: {}, param_count: {})",
                        f.get_string(header.function_name()).unwrap_or_default(),
                        header.offset(),
                        header.bytecode_size_in_bytes(),
                        header.param_count()
                    )
                }
            }
            "disassemble" => {
                let arg3 = args.next();
                let function_id = if let Some(arg3) = arg3 {
                    match arg3.parse::<usize>() {
                        Ok(arg3) => arg3,
                        Err(_) => {
                            print_help();
                            return;
                        }
                    }
                } else {
                    print_help();
                    return;
                };
                let mut buf = Vec::new();
                match bundle_path.read_to_end(&mut buf) {
                    Ok(_) => (),
                    Err(e) => {
                        println!("Error while reading provided file: {e}");
                        return;
                    }
                };
                let mut cursor = Cursor::new(buf.as_slice());
                let f = BytecodeFile::from_reader(&mut cursor).unwrap();
                let arg4 = args.next();
                match arg4 {
                    Some(output_path) => {
                        let output_path = PathBuf::from_str(&output_path).unwrap();
                        let mut output_file = match File::create(output_path.clone()) {
                            Ok(f) => f,
                            Err(e) => {
                                println!(
                                    "Error while opening output file {}: {}",
                                    output_path.display(),
                                    e
                                );
                                return;
                            }
                        };
                        disassemble_function(&mut cursor, &f, function_id, &mut output_file);
                    }
                    None => {
                        disassemble_function(&mut cursor, &f, function_id, &mut stdout());
                    }
                }
            }
            "strings" => {
                let mut buf = Vec::new();
                match bundle_path.read_to_end(&mut buf) {
                    Ok(_) => (),
                    Err(e) => {
                        println!("Error while reading provided file: {e}");
                        return;
                    }
                };
                let mut cursor = Cursor::new(buf.as_slice());
                let f = BytecodeFile::from_reader(&mut cursor).unwrap();
                let arg4 = args.next();
                match arg4 {
                    Some(output_path) => {
                        let output_path = PathBuf::from_str(&output_path).unwrap();
                        let mut output_file = match File::create(output_path.clone()) {
                            Ok(f) => BufWriter::new(f),
                            Err(e) => {
                                println!(
                                    "Error while opening output file {}: {}",
                                    output_path.display(),
                                    e
                                );
                                return;
                            }
                        };
                        for s_index in 0..f.header.string_count {
                            let s = f.get_string(s_index).unwrap_or_default();
                            match writeln!(output_file, "{s_index}: {s}") {
                                Ok(_) => (),
                                Err(e) => {
                                    println!(
                                        "Error while writing output file {}: {}",
                                        output_path.display(),
                                        e
                                    );
                                }
                            };
                        }
                    }
                    None => {
                        for s_index in 0..f.header.string_count {
                            let s = f.get_string(s_index).unwrap_or_default();
                            println!("{s_index}: {s}");
                        }
                    }
                }
            }
            _ => {
                print_help();
            }
        }
    } else {
        print_help();
    }
}

fn disassemble_function<W: Write>(
    cursor: &mut Cursor<&[u8]>,
    f: &BytecodeFile,
    function_id: usize,
    output: &mut W,
) {
    let header = f.function_headers[function_id];
    let disassembled = header
        .disassemble_function::<Instruction, Cursor<&[u8]>>(cursor)
        .unwrap();
    let flow_graph = construct_flow_graph(&disassembled);
    #[cfg(test)]
    {
        writeln!(
            File::create("./out_flow.dot").unwrap(),
            "{:?}",
            petgraph::dot::Dot::new(&flow_graph)
        )
        .unwrap();
    }

    let cfg = construct_cfg(&flow_graph);
    #[cfg(test)]
    {
        writeln!(
            File::create("./out_cfg.dot").unwrap(),
            "{:?}",
            petgraph::dot::Dot::new(&cfg)
        )
        .unwrap();
    }

    let func = FnDecl {
        ident: Ident::new(format!("f{function_id}").as_str().into(), DUMMY_SP),
        function: Box::new(Function {
            params: Vec::new(),
            decorators: Vec::new(),
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: generate_ast(f, &cfg, &disassembled, NodeIndex::new(0), false, None, None),
            }),
            is_generator: false,
            is_async: false,
            type_params: None,
            return_type: None,
        }),
        declare: false,
    };
    let cm = Lrc::new(SourceMap::new(FilePathMapping::empty()));
    let mut emitter = Emitter {
        cfg: swc_ecma_codegen::Config {
            target: EsVersion::Es2022,
            ascii_only: false,
            minify: false,
            omit_last_semi: false,
        },
        cm: cm.clone(),
        comments: None,
        wr: JsWriter::new(cm, "\n", output, None),
    };
    let program = Program::Script(Script {
        span: DUMMY_SP,
        body: vec![Stmt::Decl(Decl::Fn(func))],
        shebang: None,
    });
    emitter.emit_program(&program).unwrap();
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        io::{Cursor, Read},
    };

    use crate::{disassemble_function, hermes_file_reader::BytecodeFile};

    #[test]
    fn t() {
        let mut buf = Vec::new();
        match File::open("./index.android.bundle")
            .unwrap()
            .read_to_end(&mut buf)
        {
            Ok(_) => (),
            Err(e) => {
                println!("Error while reading provided file: {e}");
                return;
            }
        };
        let mut cursor = Cursor::new(buf.as_slice());
        let f = BytecodeFile::from_reader(&mut cursor).unwrap();
        disassemble_function(&mut cursor, &f, 0, &mut File::create("./out.txt").unwrap())
    }
}
