#![feature(iter_advance_by)]

use std::{
    fs::File,
    io::{BufRead, BufReader, BufWriter, Write},
};

use indexmap::IndexMap;
use regex::Regex;
use serde::Serialize;

struct OpcodeArg {
    value: String,
    is_string: bool,
    is_function: bool,
    is_big_int: bool,
}

impl Serialize for OpcodeArg {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if self.is_string {
            serializer.serialize_str(&format!("{}:S", self.value))
        } else if self.is_function {
            serializer.serialize_str(&format!("{}:F", self.value))
        } else if self.is_big_int {
            serializer.serialize_str(&format!("{}:B", self.value))
        } else {
            serializer.serialize_str(&self.value)
        }
    }
}

//Most of the code is from hbctool
//https://github.com/bongtrop/hbctool/blob/main/hbctool/hbc/hbc85/tool/opcode_generator.py
fn main() {
    let mut args = std::env::args();
    args.advance_by(1).unwrap();
    let input_file_path = match args.next() {
        Some(path) => path,
        None => {
            println!("Usage: hbc_parser_tool [input_path] [output_path]");
            println!("Input path is usually a BytecodeList.def from https://github.com/facebook/hermes/blob/main/include/hermes/BCGen/HBC/BytecodeList.def");
            return;
        }
    };
    let output_file_path = match args.next() {
        Some(path) => path,
        None => {
            println!("Usage: hbc_parser_tool [input_path] [output_path]");
            println!("Input path is usually a BytecodeList.def from https://github.com/facebook/hermes/blob/main/include/hermes/BCGen/HBC/BytecodeList.def");
            return;
        }
    };

    let input_file = File::open(input_file_path).unwrap();
    let output_file = File::create(output_file_path).unwrap();

    let mut outmap = IndexMap::new();
    for (line_num, line) in BufReader::new(input_file).lines().enumerate() {
        let line = line.unwrap();
        if line.is_empty() {
            continue;
        }
        if line.starts_with("DEFINE_OPCODE_") {
            let m = Regex::new(r#"\((\w+)((, \w+)*)\)"#).unwrap();
            let captures = m.captures(&line).unwrap();
            let name = captures.get(1).unwrap().as_str();
            let operands = &captures
                .get(2)
                .unwrap()
                .as_str()
                .split(", ")
                .collect::<Vec<&str>>()[1..];
            outmap.insert(
                name.to_string(),
                operands
                    .iter()
                    .map(|operand| OpcodeArg {
                        value: operand.to_string(),
                        is_string: false,
                        is_function: false,
                        is_big_int: false,
                    })
                    .collect::<Vec<OpcodeArg>>(),
            );
        } else if line.starts_with("OPERAND_STRING_ID") {
            let m = Regex::new(r#"\((\w+), (\w+)\)"#).unwrap();
            let captures = m.captures(&line).unwrap();
            let name = captures.get(1).unwrap().as_str();
            let operand_id = captures.get(2).unwrap().as_str().parse::<u32>().unwrap() - 1;
            outmap.get_mut(name).unwrap()[operand_id as usize].is_string = true;
        } else if line.starts_with("OPERAND_FUNCTION_ID") {
            let m = Regex::new(r#"\((\w+), (\w+)\)"#).unwrap();
            let captures = m.captures(&line).unwrap();
            let name = captures.get(1).unwrap().as_str();
            let operand_id = captures.get(2).unwrap().as_str().parse::<u32>().unwrap() - 1;
            outmap.get_mut(name).unwrap()[operand_id as usize].is_function = true;
        } else if line.starts_with("OPERAND_BIGINT_ID") {
            let m = Regex::new(r#"\((\w+), (\w+)\)"#).unwrap();
            let captures = m.captures(&line).unwrap();
            let name = captures.get(1).unwrap().as_str();
            let operand_id = captures.get(2).unwrap().as_str().parse::<u32>().unwrap() - 1;
            outmap.get_mut(name).unwrap()[operand_id as usize].is_big_int = true;
        } else if line.starts_with("DEFINE_JUMP_") {
            let m = Regex::new(r#"(\d)\((\w+)\)"#).unwrap();
            let captures = m.captures(&line).unwrap();
            let num_op = captures.get(1).unwrap().as_str().parse::<u8>().unwrap();
            let name = captures.get(2).unwrap().as_str();
            let operands: &[&str] = match num_op {
                1 => &["Addr8"],
                2 => &["Addr8", "Reg8"],
                3 => &["Addr8", "Reg8", "Reg8"],
                _ => panic!(),
            };
            outmap.insert(
                name.to_string(),
                operands
                    .iter()
                    .map(|operand| OpcodeArg {
                        value: operand.to_string(),
                        is_string: false,
                        is_function: false,
                        is_big_int: false,
                    })
                    .collect::<Vec<OpcodeArg>>(),
            );
            let operands: &[&str] = match num_op {
                1 => &["Addr32"],
                2 => &["Addr32", "Reg8"],
                3 => &["Addr32", "Reg8", "Reg8"],
                _ => panic!(),
            };
            outmap.insert(
                format!("{name}Long"),
                operands
                    .iter()
                    .map(|operand| OpcodeArg {
                        value: operand.to_string(),
                        is_string: false,
                        is_function: false,
                        is_big_int: false,
                    })
                    .collect::<Vec<OpcodeArg>>(),
            );
        } else if !(line.starts_with("ASSERT_")
            || line.starts_with("DEFINE_RET_TARGET")
            || line.starts_with("DEFINE_OPERAND_TYPE")
            || line.starts_with('#')
            || line.starts_with("//")
            || line.starts_with("/*")
            || line.starts_with(" *")
            || line.starts_with("  "))
        {
            println!("Unhandled line {line_num}: {line}");
        }
    }

    println!(
        "{}",
        outmap.keys().cloned().collect::<Vec<String>>().join(",\n")
    );

    BufWriter::new(output_file)
        .write_all(serde_json::to_string_pretty(&outmap).unwrap().as_bytes())
        .unwrap();
}
