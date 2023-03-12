use super::InstructionSet;
use byteorder::{LittleEndian, ReadBytesExt};
use help_macros::ByteCodeInstructions;
use std::io::Read;

pub static JS_BUILTINS: [&str; 52] = [
    "Array.isArray",
    "Date.UTC",
    "Date.parse",
    "JSON.parse",
    "JSON.stringify",
    "Math.abs",
    "Math.acos",
    "Math.asin",
    "Math.atan",
    "Math.atan2",
    "Math.ceil",
    "Math.cos",
    "Math.exp",
    "Math.floor",
    "Math.hypot",
    "Math.imul",
    "Math.log",
    "Math.max",
    "Math.min",
    "Math.pow",
    "Math.round",
    "Math.sin",
    "Math.sqrt",
    "Math.tan",
    "Math.trunc",
    "Object.create",
    "Object.defineProperties",
    "Object.defineProperty",
    "Object.freeze",
    "Object.getOwnPropertyDescriptor",
    "Object.getOwnPropertyNames",
    "Object.getPrototypeOf",
    "Object.isExtensible",
    "Object.isFrozen",
    "Object.keys",
    "Object.seal",
    "String.fromCharCode",
    "silentSetPrototypeOf",
    "requireFast",
    "getTemplateObject",
    "ensureObject",
    "getMethod",
    "throwTypeError",
    "generatorSetDelegated",
    "copyDataProperties",
    "copyRestArgs",
    "arraySpread",
    "apply",
    "exportAll",
    "exponentiationOperator",
    "initRegexNamedGroups",
    "spawnAsync"
];

#[repr(C)]
#[derive(ByteCodeInstructions, Debug, Clone)]
pub enum Instruction {
    Unreachable,
    NewObjectWithBuffer {
        dst_reg: u8,
        size_hint: u16,
        static_elements_num: u16,
        object_key_buffer_index: u16,
        object_value_buffer_index: u16,
    },
    NewObjectWithBufferLong {
        dst_reg: u8,
        preallocation_size_hint: u16,
        static_elements_num: u16,
        object_key_buffer_index: u32,
        object_value_buffer_index: u32,
    },
    NewObject {
        dst_reg: u8,
    },
    NewObjectWithParent {
        dst_reg: u8,
        parent_reg: u8,
    },
    NewArrayWithBuffer {
        dst_reg: u8,
        preallocation_size_hint: u16,
        static_elements_num: u16,
        array_buffer_table_index: u16,
    },
    NewArrayWithBufferLong {
        dst_reg: u8,
        preallocation_size_hint: u16,
        static_elements_num: u16,
        array_buffer_table_index: u32,
    },
    NewArray {
        dst_reg: u8,
        size: u16,
    },
    Mov {
        dst_reg: u8,
        src_reg: u8,
    },
    MovLong {
        dst_reg: u32,
        src_reg: u32,
    },
    Negate {
        dst_reg: u8,
        src_reg: u8,
    },
    Not {
        dst_reg: u8,
        src_reg: u8,
    },
    BitNot {
        dst_reg: u8,
        src_reg: u8,
    },
    TypeOf {
        dst_reg: u8,
        src_reg: u8,
    },
    Eq {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    StrictEq {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Neq {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    StrictNeq {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Less {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    LessEq {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Greater {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    GreaterEq {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Add {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    AddN {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Mul {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    MulN {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Div {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    DivN {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Mod {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Sub {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    SubN {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    LShift {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    RShift {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    URshift {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    BitAnd {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    BitXor {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    BitOr {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Inc {
        dst_reg: u8,
        arg_reg: u8,
    },
    Dec {
        dst_reg: u8,
        arg_reg: u8,
    },
    InstanceOf {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    IsIn {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    GetEnvironment {
        dst_reg: u8,
        num_environments: u8,
    },
    StoreToEnvironment {
        env_reg: u8, //Register containing environment from GetEnvironment
        env_slot_index: u8,
        value_reg: u8,
    },
    StoreToEnvironmentL {
        env_reg: u8, //Register containing environment from GetEnvironment
        env_slot_index: u16,
        value_reg: u8,
    },
    StoreNPToEnvironment {
        env_reg: u8, //Register containing environment from GetEnvironment
        env_slot_index: u8,
        value_reg: u8,
    },
    StoreNPToEnvironmentL {
        env_reg: u8, //Register containing environment from GetEnvironment
        env_slot_index: u16,
        value_reg: u8,
    },
    LoadFromEnvironment {
        dst_reg: u8,
        env_reg: u8, //Register containing environment from GetEnvironment
        env_slot_index: u8,
    },
    LoadFromEnvironmentL {
        dst_reg: u8,
        env_reg: u8, //Register containing environment from GetEnvironment
        env_slot_index: u16,
    },
    GetGlobalObject {
        dst_reg: u8,
    },
    GetNewTarget {
        dst_reg: u8,
    },
    CreateEnvironment {
        dst_reg: u8,
    },
    DeclareGlobalVar {
        string_table_index: u32,
    },
    GetByIdShort {
        dst_reg: u8,
        obj_reg: u8,
        cache_index: u8,
        string_table_index: u8,
    },
    GetById {
        dst_reg: u8,
        obj_reg: u8,
        cache_index: u8,
        string_table_index: u16,
    },
    GetByIdLong {
        dst_reg: u8,
        obj_reg: u8,
        cache_index: u8,
        string_table_index: u32,
    },
    TryGetById {
        //intented: obj_reg = GetGlobalObject
        dst_reg: u8,
        obj_reg: u8,
        cache_index: u8,
        string_table_index: u16,
    },
    TryGetByIdLong {
        //intented: obj_reg = GetGlobalObject
        dst_reg: u8,
        obj_reg: u8,
        cache_index: u8,
        string_table_index: u32,
    },
    PutById {
        dst_obj_reg: u8,
        value_reg: u8,
        cache_index: u8,
        string_table_index: u16,
    },
    PutByIdLong {
        dst_obj_reg: u8,
        value_reg: u8,
        cache_index: u8,
        string_table_index: u32,
    },
    TryPutById {
        //intented: dst_obj_reg = GetGlobalObject
        dst_obj_reg: u8,
        value_reg: u8,
        cache_index: u8,
        string_table_index: u16,
    },
    TryPutByIdLong {
        //intented: dst_obj_reg = GetGlobalObject
        dst_obj_reg: u8,
        value_reg: u8,
        cache_index: u8,
        string_table_index: u32,
    },
    PutNewOwnByIdShort {
        dst_obj_reg: u8,
        value_reg: u8,
        string_table_index: u8,
    },
    PutNewOwnById {
        dst_obj_reg: u8,
        value_reg: u8,
        string_table_index: u16,
    },
    PutNewOwnByIdLong {
        dst_obj_reg: u8,
        value_reg: u8,
        string_table_index: u32,
    },
    PutNewOwnNEById {
        dst_obj_reg: u8,
        value_reg: u8,
        string_table_index: u16,
    },
    PutNewOwnNEByIdLong {
        dst_obj_reg: u8,
        value_reg: u8,
        string_table_index: u32,
    },
    PutOwnByIndex {
        dst_obj_reg: u8,
        value_reg: u8,
        index: u8,
    },
    PutOwnByIndexL {
        dst_obj_reg: u8,
        value_reg: u8,
        index: u32,
    },
    PutOwnByVal {
        dst_obj_reg: u8,
        value_reg: u8,
        property_name_reg: u8,
        enumerable: bool,
    },
    DelById {
        dst_reg: u8,
        obj_reg: u8,
        string_table_index: u16,
    },
    DelByIdLong {
        dst_reg: u8,
        obj_reg: u8,
        string_table_index: u32,
    },
    GetByVal {
        dst_reg: u8,
        obj_reg: u8,
        index_reg: u8,
    },
    PutByVal {
        dst_obj_reg: u8,
        index_reg: u8,
        value_reg: u8,
    },
    DelByVal {
        dst_reg: u8,
        obj_reg: u8,
        index_reg: u8,
    },
    PutOwnGetterSetterByVal {
        obj_reg: u8,
        property_name_reg: u8,
        getter_closure_reg: u8,
        setter_closure_reg: u8,
        enumerable: bool,
    },
    GetPNameList {
        dst_reg: u8,
        obj_reg: u8,
        iterating_index_reg: u8,
        property_list_size_reg: u8,
    },
    GetNextPName {
        dst_reg: u8,
        properties_array_reg: u8,
        obj_reg: u8,
        iterating_index_reg: u8,
        property_list_size_reg: u8,
    },
    Call {
        dst_reg: u8,
        closure_reg: u8,
        arguments_len: u8,
    },
    Construct {
        dst_reg: u8,
        closure_reg: u8,
        arguments_len: u8,
    },
    Call1 {
        dst_reg: u8,
        closure_reg: u8,
        argument_reg: u8,
    },
    CallDirect {
        dst_reg: u8,
        arguments_len: u8,
        function_table_index: u16,
    },
    Call2 {
        dst_reg: u8,
        closure_reg: u8,
        argument1_reg: u8,
        argument2_reg: u8,
    },
    Call3 {
        dst_reg: u8,
        closure_reg: u8,
        argument1_reg: u8,
        argument2_reg: u8,
        argument3_reg: u8,
    },
    Call4 {
        dst_reg: u8,
        closure_reg: u8,
        argument1_reg: u8,
        argument2_reg: u8,
        argument3_reg: u8,
        argument4_reg: u8,
    },
    CallLong {
        dst_reg: u8,
        closure_reg: u8,
        arguments_len: u32,
    },
    ConstructLong {
        dst_reg: u8,
        closure_reg: u8,
        arguments_len: u32,
    },
    CallDirectLongIndex {
        dst_reg: u8,
        arguments_len: u8,
        function_table_index: u32,
    },
    CallBuiltin {
        dst_reg: u8,
        builtin_number: u8,
        arguments_len: u8,
    },
    CallBuiltinLong {
        dst_reg: u8,
        builtin_number: u8,
        arguments_len: u32,
    },
    GetBuiltinClosure {
        dst_reg: u8,
        builtin_number: u8,
    },
    Ret {
        value_reg: u8,
    },
    Catch {
        dst_reg: u8,
    },
    DirectEval {
        dst_reg: u8,
        value_reg: u8,
    },
    Throw {
        value_reg: u8,
    },
    ThrowIfEmpty {
        dst_reg: u8,
        checked_value_reg: u8,
    },
    Debugger,
    AsyncBreakCheck,
    ProfilePoint {
        function_local_profile_point_index: u16,
    },
    CreateClosure {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u16,
    },
    CreateClosureLongIndex {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u32,
    },
    CreateGeneratorClosure {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u16,
    },
    CreateGeneratorClosureLongIndex {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u32,
    },
    CreateAsyncClosure {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u16,
    },
    CreateAsyncClosureLongIndex {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u32,
    },
    CreateThis {
        dst_reg: u8,
        prototype_reg: u8,
        constructor_closure_reg: u8,
    },
    SelectObject {
        dst_reg: u8,
        this_obj_reg: u8,
        return_value_reg: u8,
    },
    LoadParam {
        dst_reg: u8,
        param_index: u8,
    },
    LoadParamLong {
        dst_reg: u8,
        param_index: u32,
    },
    LoadConstUInt8 {
        dst_reg: u8,
        value: u8,
    },
    LoadConstInt {
        dst_reg: u8,
        value: i32,
    },
    LoadConstDouble {
        dst_reg: u8,
        value: f64,
    },
    LoadConstBigInt {
        dst_reg: u8,
        bigint_table_index: u16,
    },
    LoadConstBigIntLongIndex {
        dst_reg: u8,
        bigint_table_index: u32,
    },
    LoadConstString {
        dst_reg: u8,
        string_table_index: u16,
    },
    LoadConstStringLongIndex {
        dst_reg: u8,
        string_table_index: u32,
    },
    LoadConstEmpty {
        dst_reg: u8,
    },
    LoadConstUndefined {
        dst_reg: u8,
    },
    LoadConstNull {
        dst_reg: u8,
    },
    LoadConstTrue {
        dst_reg: u8,
    },
    LoadConstFalse {
        dst_reg: u8,
    },
    LoadConstZero {
        dst_reg: u8,
    },
    CoerceThisNS {
        dst_reg: u8,
        this_value_reg: u8,
    },
    LoadThisNS {
        dst_this_obj_reg: u8,
    },
    ToNumber {
        dst_reg: u8,
        value_reg: u8,
    },
    ToNumeric {
        dst_reg: u8,
        value_reg: u8,
    },
    ToInt32 {
        dst_reg: u8,
        value_reg: u8,
    },
    AddEmptyString {
        dst_reg: u8,
        value_reg: u8,
    },
    GetArgumentsPropByVal {
        dst_reg: u8,
        index_reg: u8,
        lazy_loaded_reg: u8,
    },
    GetArgumentsLength {
        dst_reg: u8,
        lazy_loaded_reg: u8,
    },
    ReifyArguments {
        lazy_loaded_reg: u8,
    },
    CreateRegExp {
        dst_reg: u8,
        pattern_string_index: u32,
        flags_string_index: u32,
        regexp_table_index: u32,
    },
    SwitchImm {
        value_reg: u8,
        relative_jump_table_offset: u32,
        relative_default_jump_offset: i32, //address
        min_value: u32,
        max_value: u32,
    },
    StartGenerator,
    ResumeGenerator {
        dst_result_reg: u8,
        is_return: bool,
    },
    CompleteGenerator,
    CreateGenerator {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u16,
    },
    CreateGeneratorLongIndex {
        dst_reg: u8,
        current_environment_reg: u8,
        function_table_index: u32,
    },
    IteratorBegin {
        dst_reg: u8,
        source_reg: u8,
    },
    IteratorNext {
        dst_reg: u8,
        iterator_or_index_reg: u8,
        source_reg: u8,
    },
    IteratorClose {
        iterator_or_index_reg: u8,
        ignore_inner_exception: bool,
    },
    Jmp {
        relative_offset: i8,
    },
    JmpLong {
        relative_offset: i32,
    },
    JmpTrue {
        relative_offset: i8,
        check_value_reg: u8,
    },
    JmpTrueLong {
        relative_offset: i32,
        check_value_reg: u8,
    },
    JmpFalse {
        relative_offset: i8,
        check_value_reg: u8,
    },
    JmpFalseLong {
        relative_offset: i32,
        check_value_reg: u8,
    },
    JmpUndefined {
        relative_offset: i8,
        check_value_reg: u8,
    },
    JmpUndefinedLong {
        relative_offset: i32,
        check_value_reg: u8,
    },
    SaveGenerator {
        relative_offset: i8,
    },
    SaveGeneratorLong {
        relative_offset: i32,
    },
    JLess {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLess {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessEqualN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JLessEqualNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessEqualN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotLessEqualNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreater {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreater {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterEqualN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JGreaterEqualNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterEqualN {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotGreaterEqualNLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JNotEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JStrictEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JStrictEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JStrictNotEqual {
        relative_offset: i8,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    JStrictNotEqualLong {
        relative_offset: i32,
        arg1_value_reg: u8,
        arg2_value_reg: u8,
    },
    Add32 {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Sub32 {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Mul32 {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Divi32 {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Divu32 {
        dst_reg: u8,
        arg1_reg: u8,
        arg2_reg: u8,
    },
    Loadi8 {
        dst_reg: u8,
        _unused_reg: u8,
        heap_index_reg: u8,
    },
    Loadu8 {
        dst_reg: u8,
        _unused_reg: u8,
        heap_index_reg: u8,
    },
    Loadi16 {
        dst_reg: u8,
        _unused_reg: u8,
        heap_index_reg: u8,
    },
    Loadu16 {
        dst_reg: u8,
        _unused_reg: u8,
        heap_index_reg: u8,
    },
    Loadi32 {
        dst_reg: u8,
        _unused_reg: u8,
        heap_index_reg: u8,
    },
    Loadu32 {
        dst_reg: u8,
        _unused_reg: u8,
        heap_index_reg: u8,
    },
    Store8 {
        _unused_reg: u8,
        heap_index_reg: u8,
        value_reg: u8,
    },
    Store16 {
        _unused_reg: u8,
        heap_index_reg: u8,
        value_reg: u8,
    },
    Store32 {
        _unused_reg: u8,
        heap_index_reg: u8,
        value_reg: u8,
    },
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{self:?}")
        // or, alternatively:
        // fmt::Debug::fmt(self, f)
    }
}
