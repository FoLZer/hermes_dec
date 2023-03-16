use std::{
    io::{Cursor, Read, Seek},
    os::raw::c_char, collections::HashMap,
};

use bitfield_struct::bitfield;
use byteorder::{LittleEndian, ReadBytesExt};
use c_struct_macro::FromBytes;
use lazy_static::lazy_static;

use safe_transmute::TriviallyTransmutable;

use crate::bytecode::InstructionSet;

lazy_static! {
    static ref IS_BIG_ENDIAN: bool = {
        let arr: [u8; 2] = 0x1234u16.to_ne_bytes();
        arr == [0x12, 0x34]
    };
}

fn transmute_field<T: TriviallyTransmutable>(slice: &[u8]) -> T {
    let size = std::mem::size_of::<T>();
    assert_eq!(
        slice.len(),
        size,
        "Input bytes must have the same size as the target struct"
    );
    if *IS_BIG_ENDIAN {
        let mut v = vec![0; size];
        v[..].clone_from_slice(slice);
        v.reverse();
        return safe_transmute::transmute_one_pedantic::<T>(v.as_slice()).unwrap();
    } else {
        return safe_transmute::transmute_one_pedantic::<T>(slice).unwrap();
    }
}

const MAGIC: u64 = 0x1F19_03C1_03BC_1FC6; //TODO
const SHA1_NUM_BYTES: usize = 20;
static SUPPORTED_VERSIONS: [u32; 1] = [93];

#[bitfield(u8)]
pub struct BytecodeOptions {
    pub static_builtins: bool,
    pub cjs_modules_statically_resolved: bool,
    pub has_async: bool,

    #[bits(5)]
    _padding: u8,
}
unsafe impl TriviallyTransmutable for BytecodeOptions {}

#[repr(C)]
#[derive(FromBytes, Clone, Copy, Debug)]
pub struct BytecodeFileHeader {
    pub magic: u64,
    pub version: u32,
    pub source_hash: [u8; SHA1_NUM_BYTES],
    pub file_length: u32,
    pub global_code_index: u32,
    pub function_count: u32,
    pub string_kind_count: u32,
    pub identifier_count: u32,
    pub string_count: u32,
    pub overflow_string_count: u32,
    pub string_storage_size: u32,
    pub big_int_count: u32,
    pub big_int_storage_size: u32,
    pub reg_exp_count: u32,
    pub reg_exp_storage_size: u32,
    pub array_buffer_size: u32,
    pub obj_key_buffer_size: u32,
    pub obj_value_buffer_size: u32,
    pub segment_id: u32,
    pub cjs_module_count: u32,
    pub function_source_count: u32,
    pub debug_info_offset: u32,
    pub options: BytecodeOptions,

    _padding: [u8; 19],
}

#[allow(dead_code)]
struct BytecodeFileFooter {
    file_hash: [u8; SHA1_NUM_BYTES],
}

#[repr(u8)]
#[derive(Debug)]
enum Prohibit {
    Call = 0,
    Construct = 1,
    None = 2,
}

impl From<u8> for Prohibit {
    fn from(value: u8) -> Self {
        match value {
            0 => Self::Call,
            1 => Self::Construct,
            2 => Self::None,
            _ => panic!("Invalid Prohibit value"),
        }
    }
}

impl From<Prohibit> for u8 {
    fn from(val: Prohibit) -> Self {
        val as Self
    }
}

#[bitfield(u8)]
struct FunctionHeaderFlags {
    #[bits(2)]
    prohibit_invoke: Prohibit,
    strict_mode: bool,
    has_exception_handler: bool,
    has_debug_info: bool,
    overflowed: bool,

    #[bits(2)]
    _padding: u8,
}

unsafe impl TriviallyTransmutable for FunctionHeaderFlags {}

impl From<FunctionHeaderFlags> for u128 {
    fn from(val: FunctionHeaderFlags) -> Self {
        Self::from(<FunctionHeaderFlags as Into<u8>>::into(val))
    }
}

impl From<u128> for FunctionHeaderFlags {
    fn from(value: u128) -> Self {
        <Self as From<u8>>::from(value as u8)
    }
}

#[allow(dead_code)]
enum FunctionHeaderFlag {
    Prohibits(Prohibit),
    FlagsStruct(FunctionHeaderFlags),
    Flags(u8),
}

#[repr(C)]
#[derive(FromBytes, Clone, Copy, Debug)]
pub struct ExceptionHandlerInfo {
    start: u32,
    end: u32,
    target: u32
}

#[repr(C)]
#[derive(FromBytes, Clone, Copy, Debug)]
pub struct FunctionHeader {
    offset: u32,
    param_count: u32,

    bytecode_size_in_bytes: u32,
    function_name: u32,

    info_offset: u32,
    frame_size: u32,

    environment_size: u32,
    highest_read_cache_index: u8,
    highest_write_cache_index: u8,

    flags: FunctionHeaderFlags,
}

impl FunctionHeader {
    pub fn read_bytecode<R: Seek + Read>(&self, reader: &mut R) -> Result<Vec<u8>, std::io::Error> {
        //let previous_offset = reader.stream_position()?;
        reader.seek(std::io::SeekFrom::Start(u64::from(self.offset)))?;
        let mut v = vec![0; self.bytecode_size_in_bytes as usize];
        reader.read_exact(&mut v)?;
        //reader.seek(std::io::SeekFrom::Start(previous_offset))?;
        Ok(v)
    }

    pub fn disassemble_function<T: InstructionSet + Clone, R: Seek + Read>(
        &self,
        reader: &mut R,
    ) -> Result<Vec<InstructionInfo<T>>, std::io::Error> {
        let bytecode = self.read_bytecode(reader)?;
        let mut bytecode_cursor = Cursor::new(&bytecode);
        let mut instructions = Vec::new();
        while !bytecode_cursor.is_empty() {
            let offset = bytecode_cursor.position() as u32;
            let opcode = T::read_opcode(&mut bytecode_cursor);
            //println!("{:?}", opcode);
            instructions.push(InstructionInfo {
                offset,
                instruction: opcode,
            });
        }
        Ok(instructions)
    }

    pub fn read_exception_handlers<R: Seek + Read>(&self, reader: &mut R) -> Result<Option<Vec<ExceptionHandlerInfo>>, std::io::Error> {
        if !self.flags.has_exception_handler() {
            return Ok(None);
        }
        reader.seek(std::io::SeekFrom::Start(self.info_offset as u64))?;
        let count = reader.read_u32::<LittleEndian>()?;
        let mut v = Vec::new();
        for _ in 0..count {
            v.push(ExceptionHandlerInfo::from_reader(reader))
        }
        return Ok(Some(v));
    }
}

#[bitfield(u128)]
pub struct SmallFuncHeader {
    #[bits(25)]
    pub offset: u32,
    #[bits(7)]
    pub param_count: u32,

    #[bits(15)]
    pub bytecode_size_in_bytes: u32,
    #[bits(17)]
    pub function_name: u32,

    #[bits(25)]
    info_offset: u32,
    #[bits(7)]
    frame_size: u32,

    #[bits(8)]
    environment_size: u8,
    #[bits(8)]
    highest_read_cache_index: u8,
    #[bits(8)]
    highest_write_cache_index: u8,

    #[bits(8)]
    flags: FunctionHeaderFlags,
}

impl SmallFuncHeader {
    pub fn read_large_header<R: Seek + Read>(
        &self,
        reader: &mut R,
    ) -> Result<FunctionHeader, std::io::Error> {
        let previous_offset = reader.stream_position()?;
        let offset = u64::from((self.info_offset() << 16) | self.offset());
        reader.seek(std::io::SeekFrom::Start(offset))?;
        let r = FunctionHeader::from_reader(reader);
        reader.seek(std::io::SeekFrom::Start(previous_offset))?;
        Ok(r)
    }

    pub fn read_bytecode<R: Seek + Read>(
        &self,
        reader: &mut R,
    ) -> Result<Option<Vec<u8>>, std::io::Error> {
        if self.flags().overflowed() {
            return Ok(None);
        }
        let previous_offset = reader.stream_position()?;
        reader.seek(std::io::SeekFrom::Start(u64::from(self.offset())))?;
        let mut v = vec![0; self.bytecode_size_in_bytes() as usize];
        reader.read_exact(&mut v)?;
        reader.seek(std::io::SeekFrom::Start(previous_offset))?;
        Ok(Some(v))
    }

    pub fn disassemble_function<T: InstructionSet + std::fmt::Debug + Clone, R: Seek + Read>(
        &self,
        reader: &mut R,
    ) -> Result<Vec<InstructionInfo<T>>, std::io::Error> {
        if self.flags().overflowed() {
            self.read_large_header(reader)?.disassemble_function(reader)
        } else {
            let bytecode = self.read_bytecode(reader)?.unwrap();
            let mut bytecode_cursor = Cursor::new(&bytecode);
            let mut instructions = Vec::new();
            while !bytecode_cursor.is_empty() {
                let offset = bytecode_cursor.position() as u32;
                let opcode = T::read_opcode(&mut bytecode_cursor);
                //println!("{:?}", opcode);
                instructions.push(InstructionInfo {
                    offset,
                    instruction: opcode,
                });
            }
            Ok(instructions)
        }
    }

    pub fn read_exception_handlers<R: Seek + Read>(&self, reader: &mut R) -> Result<Option<Vec<ExceptionHandlerInfo>>, std::io::Error> {
        if !self.flags().has_exception_handler() {
            return Ok(None);
        }
        reader.seek(std::io::SeekFrom::Start(self.info_offset() as u64))?;
        let count = reader.read_u32::<LittleEndian>()?;
        let mut v = Vec::new();
        for _ in 0..count {
            v.push(ExceptionHandlerInfo::from_reader(reader))
        }
        return Ok(Some(v));
    }
}

#[derive(Debug, Clone)]
pub struct InstructionInfo<T: InstructionSet + Clone> {
    pub offset: u32,
    pub instruction: T,
}

#[bitfield(u32)]
pub struct SmallStringTableEntry {
    #[bits(1)]
    is_utf16: u32,
    #[bits(23)]
    offset: u32,
    #[bits(8)]
    length: u32,
}

#[repr(u8)]
#[derive(Debug)]
pub enum StringKind {
    String = 0,
    Identifier = 1,
}

impl From<u32> for StringKind {
    fn from(value: u32) -> Self {
        unsafe { std::mem::transmute((value & 0x1) as u8) }
    }
}

impl From<StringKind> for u32 {
    fn from(val: StringKind) -> Self {
        val as Self
    }
}

#[bitfield(u32)]
pub struct StringKindEntry {
    #[bits(31)]
    count: u32,
    #[bits(1)]
    kind: StringKind,
}

#[bitfield(u64)]
pub struct OverflowStringTableEntry {
    offset: u32,
    length: u32,
}

#[bitfield(u64)]
pub struct BigIntTableEntry {
    offset: u32,
    length: u32,
}

#[bitfield(u64)]
pub struct RegExpTableEntry {
    offset: u32,
    length: u32,
}

#[derive(Debug)]
pub struct BytecodeFile {
    pub header: BytecodeFileHeader,
    pub function_headers: Vec<SmallFuncHeader>,
    pub string_table_entries: Vec<SmallStringTableEntry>,
    pub string_kinds: Vec<StringKindEntry>,
    pub identifier_hashes: Vec<u32>,
    pub string_table_overflow_entries: Vec<OverflowStringTableEntry>,
    pub string_storage: Vec<c_char>,
    pub array_buffer: Vec<u8>,
    pub obj_key_buffer: Vec<u8>,
    pub obj_value_buffer: Vec<u8>,
    pub big_int_table: Vec<BigIntTableEntry>,
    pub big_int_storage: Vec<u8>,
    pub reg_exp_table: Vec<RegExpTableEntry>,
    pub reg_exp_storage: Vec<u8>,
    pub cjs_module_table: Option<Vec<(u32, u32)>>,
    pub cjs_module_table_static: Option<Vec<(u32, u32)>>,
    pub function_source_table: Vec<(u32, u32)>,

    pub exception_handler_map: HashMap<usize, Vec<ExceptionHandlerInfo>>
}

#[allow(dead_code)]
impl BytecodeFile {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut offset = 0;
        let header = {
            let size = std::mem::size_of::<BytecodeFileHeader>();

            BytecodeFileHeader::from_bytes(&bytes[offset..offset + size])
        };
        if header.magic != MAGIC {
            println!(
                "WARN: Incorrect MAGIC header found (expected: {}, got: {})",
                MAGIC, header.magic
            );
        }
        if !SUPPORTED_VERSIONS.contains(&header.version) {
            println!(
                "WARN: Unsupported bytecode version found (got: {})",
                header.version
            );
        }
        let function_headers = {
            let mut v = Vec::with_capacity(header.function_count as usize);
            for _ in 0..header.function_count {
                let size = std::mem::size_of::<SmallFuncHeader>();
                v.push(unsafe {
                    <SmallFuncHeader as From<u128>>::from(
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap(),
                    )
                });
                offset += size;
            }
            v
        };
        let string_kinds = {
            let mut v = Vec::with_capacity(header.string_kind_count as usize);
            for _ in 0..header.string_kind_count {
                let size = std::mem::size_of::<StringKindEntry>();
                v.push(unsafe {
                    <StringKindEntry as From<u32>>::from(
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap(),
                    )
                });
                offset += size;
            }
            v
        };
        let identifier_hashes = {
            let mut v = Vec::with_capacity(header.identifier_count as usize);
            for _ in 0..header.identifier_count {
                let size = std::mem::size_of::<u32>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let string_table_entries = {
            let mut v = Vec::with_capacity(header.string_count as usize);
            for _ in 0..header.string_count {
                let size = std::mem::size_of::<SmallStringTableEntry>();
                v.push(unsafe {
                    <SmallStringTableEntry as From<u32>>::from(
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap(),
                    )
                });
                offset += size;
            }
            v
        };
        let string_table_overflow_entries = {
            let mut v = Vec::with_capacity(header.overflow_string_count as usize);
            for _ in 0..header.overflow_string_count {
                let size = std::mem::size_of::<OverflowStringTableEntry>();
                v.push(unsafe {
                    <OverflowStringTableEntry as From<u64>>::from(
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap(),
                    )
                });
                offset += size;
            }
            v
        };
        let string_storage = {
            let mut v = Vec::with_capacity(header.string_storage_size as usize);
            for _ in 0..header.string_storage_size {
                let size = std::mem::size_of::<c_char>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let array_buffer = {
            let mut v = Vec::with_capacity(header.array_buffer_size as usize);
            for _ in 0..header.array_buffer_size {
                let size = std::mem::size_of::<u8>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let obj_key_buffer = {
            let mut v = Vec::with_capacity(header.obj_key_buffer_size as usize);
            for _ in 0..header.obj_key_buffer_size {
                let size = std::mem::size_of::<u8>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let obj_value_buffer = {
            let mut v = Vec::with_capacity(header.obj_value_buffer_size as usize);
            for _ in 0..header.obj_value_buffer_size {
                let size = std::mem::size_of::<u8>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let big_int_table = {
            let mut v = Vec::with_capacity(header.big_int_count as usize);
            for _ in 0..header.big_int_count {
                let size = std::mem::size_of::<BigIntTableEntry>();
                v.push(unsafe {
                    <BigIntTableEntry as From<u64>>::from(
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap(),
                    )
                });
                offset += size;
            }
            v
        };
        let big_int_storage = {
            let mut v = Vec::with_capacity(header.big_int_storage_size as usize);
            for _ in 0..header.big_int_storage_size {
                let size = std::mem::size_of::<u8>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let reg_exp_table = {
            let mut v = Vec::with_capacity(header.reg_exp_count as usize);
            for _ in 0..header.reg_exp_count {
                let size = std::mem::size_of::<RegExpTableEntry>();
                v.push(unsafe {
                    <RegExpTableEntry as From<u64>>::from(
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap(),
                    )
                });
                offset += size;
            }
            v
        };
        let reg_exp_storage = {
            let mut v = Vec::with_capacity(header.reg_exp_storage_size as usize);
            for _ in 0..header.reg_exp_storage_size {
                let size = std::mem::size_of::<u8>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let (cjs_module_table, cjs_module_table_static) = {
            if header.options.cjs_modules_statically_resolved() {
                let mut v = Vec::with_capacity(header.cjs_module_count as usize);
                for _ in 0..header.cjs_module_count {
                    let size = std::mem::size_of::<u64>();
                    v.push(unsafe {
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap()
                    });
                    offset += size;
                }
                (None, Some(v))
            } else {
                let mut v = Vec::with_capacity(header.cjs_module_count as usize);
                for _ in 0..header.cjs_module_count {
                    let size = std::mem::size_of::<u64>();
                    v.push(unsafe {
                        safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                            .unwrap()
                    });
                    offset += size;
                }
                (Some(v), None)
            }
        };
        let function_source_table = {
            let mut v = Vec::with_capacity(header.function_source_count as usize);
            for _ in 0..header.function_source_count {
                let size = std::mem::size_of::<u64>();
                v.push(unsafe {
                    safe_transmute::base::from_bytes_pedantic(&bytes[offset..offset + size])
                        .unwrap()
                });
                offset += size;
            }
            v
        };
        let exception_handler_map = {
            let mut map = HashMap::new();
            for i in 0..function_headers.len() {
                if let Some(handlers) = function_headers[i].read_exception_handlers(&mut Cursor::new(bytes)).unwrap() {
                    map.insert(i, handlers);
                }
            }
            map
        };
        Self {
            header,
            function_headers,
            string_table_entries, //ALL TODO's
            string_kinds,
            identifier_hashes,
            string_table_overflow_entries,
            string_storage,
            array_buffer,
            obj_key_buffer,
            obj_value_buffer,
            big_int_table,
            big_int_storage,
            reg_exp_table,
            reg_exp_storage,
            cjs_module_table,
            cjs_module_table_static,
            function_source_table,

            exception_handler_map
        }
    }

    pub fn from_reader<T: Read + Seek>(reader: &mut T) -> Result<Self, std::io::Error> {
        let header = {
            let _size = std::mem::size_of::<BytecodeFileHeader>();

            BytecodeFileHeader::from_reader(reader)
        };
        if header.magic != MAGIC {
            println!(
                "WARN: Incorrect MAGIC header found (expected: {}, got: {})",
                MAGIC, header.magic
            );
        }
        if !SUPPORTED_VERSIONS.contains(&header.version) {
            println!(
                "WARN: Unsupported bytecode version found (got: {})",
                header.version
            );
        }
        let function_headers = {
            let mut v = Vec::with_capacity(header.function_count as usize);
            for _ in 0..header.function_count {
                v.push(<SmallFuncHeader as From<u128>>::from(
                    reader.read_u128::<LittleEndian>()?,
                ));
            }
            v
        };
        let string_kinds = {
            let mut v = Vec::with_capacity(header.string_kind_count as usize);
            for _ in 0..header.string_kind_count {
                v.push(<StringKindEntry as From<u32>>::from(
                    reader.read_u32::<LittleEndian>()?,
                ));
            }
            v
        };
        let identifier_hashes = {
            let mut v = Vec::with_capacity(header.identifier_count as usize);
            for _ in 0..header.identifier_count {
                v.push(reader.read_u32::<LittleEndian>()?);
            }
            v
        };
        let string_table_entries = {
            let mut v = Vec::with_capacity(header.string_count as usize);
            for _ in 0..header.string_count {
                let _size = std::mem::size_of::<SmallStringTableEntry>();
                v.push(<SmallStringTableEntry as From<u32>>::from(
                    reader.read_u32::<LittleEndian>()?,
                ));
            }
            v
        };
        let string_table_overflow_entries = {
            let mut v = Vec::with_capacity(header.overflow_string_count as usize);
            for _ in 0..header.overflow_string_count {
                let _size = std::mem::size_of::<OverflowStringTableEntry>();
                v.push(<OverflowStringTableEntry as From<u64>>::from(
                    reader.read_u64::<LittleEndian>()?,
                ));
            }
            v
        };
        let string_storage = {
            let mut v = Vec::with_capacity(header.string_storage_size as usize);
            for _ in 0..header.string_storage_size {
                let _size = std::mem::size_of::<c_char>();
                v.push(reader.read_u8()? as c_char);
            }
            v
        };
        let array_buffer = {
            let mut v = Vec::with_capacity(header.array_buffer_size as usize);
            for _ in 0..header.array_buffer_size {
                let _size = std::mem::size_of::<u8>();
                v.push(reader.read_u8()?);
            }
            v
        };
        let obj_key_buffer = {
            let mut v = Vec::with_capacity(header.obj_key_buffer_size as usize);
            for _ in 0..header.obj_key_buffer_size {
                let _size = std::mem::size_of::<u8>();
                v.push(reader.read_u8()?);
            }
            v
        };
        let obj_value_buffer = {
            let mut v = Vec::with_capacity(header.obj_value_buffer_size as usize);
            for _ in 0..header.obj_value_buffer_size {
                let _size = std::mem::size_of::<u8>();
                v.push(reader.read_u8()?);
            }
            v
        };
        let big_int_table = {
            let mut v = Vec::with_capacity(header.big_int_count as usize);
            for _ in 0..header.big_int_count {
                let _size = std::mem::size_of::<BigIntTableEntry>();
                v.push(<BigIntTableEntry as From<u64>>::from(
                    reader.read_u64::<LittleEndian>()?,
                ));
            }
            v
        };
        let big_int_storage = {
            let mut v = Vec::with_capacity(header.big_int_storage_size as usize);
            for _ in 0..header.big_int_storage_size {
                let _size = std::mem::size_of::<u8>();
                v.push(reader.read_u8()?);
            }
            v
        };
        let reg_exp_table = {
            let mut v = Vec::with_capacity(header.reg_exp_count as usize);
            for _ in 0..header.reg_exp_count {
                v.push(<RegExpTableEntry as From<u64>>::from(
                    reader.read_u64::<LittleEndian>()?,
                ));
            }
            v
        };
        let reg_exp_storage = {
            let mut v = Vec::with_capacity(header.reg_exp_storage_size as usize);
            for _ in 0..header.reg_exp_storage_size {
                let _size = std::mem::size_of::<u8>();
                v.push(reader.read_u8()?);
            }
            v
        };
        let (cjs_module_table, cjs_module_table_static) = {
            if header.options.cjs_modules_statically_resolved() {
                let mut v = Vec::with_capacity(header.cjs_module_count as usize);
                for _ in 0..header.cjs_module_count {
                    let _size = std::mem::size_of::<u64>();
                    v.push((
                        reader.read_u32::<LittleEndian>()?,
                        reader.read_u32::<LittleEndian>()?,
                    ));
                }
                (None, Some(v))
            } else {
                let mut v = Vec::with_capacity(header.cjs_module_count as usize);
                for _ in 0..header.cjs_module_count {
                    let _size = std::mem::size_of::<u64>();
                    v.push((
                        reader.read_u32::<LittleEndian>()?,
                        reader.read_u32::<LittleEndian>()?,
                    ));
                }
                (Some(v), None)
            }
        };
        let function_source_table = {
            let mut v = Vec::with_capacity(header.function_source_count as usize);
            for _ in 0..header.function_source_count {
                let _size = std::mem::size_of::<u64>();
                v.push((
                    reader.read_u32::<LittleEndian>()?,
                    reader.read_u32::<LittleEndian>()?,
                ));
            }
            v
        };
        let exception_handler_map = {
            let mut map = HashMap::new();
            for i in 0..function_headers.len() {
                if let Some(handlers) = function_headers[i].read_exception_handlers(reader).unwrap() {
                    map.insert(i, handlers);
                }
            }
            map
        };
        Ok(Self {
            header,
            function_headers,
            string_table_entries, //ALL TODO's
            string_kinds,
            identifier_hashes,
            string_table_overflow_entries,
            string_storage,
            array_buffer,
            obj_key_buffer,
            obj_value_buffer,
            big_int_table,
            big_int_storage,
            reg_exp_table,
            reg_exp_storage,
            cjs_module_table,
            cjs_module_table_static,
            function_source_table,

            exception_handler_map
        })
    }

    pub fn get_string(&self, index: u32) -> Option<String> {
        let entry = &self.string_table_entries[index as usize];
        if entry.length() == 0 {
            return None;
        }
        let begin_offset = entry.offset() as usize;
        let end_offset = begin_offset + entry.length() as usize;
        Some(
            self.string_storage[begin_offset..end_offset]
                .iter()
                .map(|c| *c as u8 as char)
                .collect::<String>(),
        )
    }

    /*
    pub fn get_bigint(&self, index: u32) -> Option<BigIntValue> {

    }*/
}
