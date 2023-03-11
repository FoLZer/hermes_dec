# hermes_dec

`hermes_dec` is a Rust project that decompiles Hermes bytecode into readable JavaScript code with support for loops and full support of If statements. The project is still heavily in development and may sometimes go into an infinite loop, causing a stack overflow. Currently, only Hermes bytecode version 93 is supported.

The project is divided into a workspace with 4 crates inside: `c_struct_macro`, `hbc_parser_tool`, `help_macros`, and `hermes_dec`. Only `hermes_dec` is the main crate that does all the heavy lifting.

## Building the project

To build the project, navigate to the root directory and run the following command:
```
cargo build --bin hermes_dec [--release]
```
The optional --release flag can be used to build the project in release mode, which optimizes the binary for performance.

## Usage

To use hermes_dec, simply run the built binary, passing the path to the Hermes bytecode file (index.android.bundle in unpacked Android applications(APKs)) as a command-line argument:
```
./hermes_dec path/to/file [additional_arguments]
```
Additional arguments currently available:
- show_functions (This will print all available functions into console)
- disassemble [function_id] [output_path] (this will disassemble function with id "function_id" and output decompiled code to output_path. function_id can be acquired through show_functions (Ids are sequential))

## Contribution
This project is still heavily in development, and any contributions are welcome. Please feel free to open issues or submit pull requests.
