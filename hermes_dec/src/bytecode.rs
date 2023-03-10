use std::io::Read;

pub mod v93;

pub trait InstructionSet {
    fn get_bytecode_size(opcode: u8) -> u8;
    fn read_opcode<R: Read>(reader: &mut R) -> Self;
}
