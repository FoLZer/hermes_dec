use quote::{quote, ToTokens};
use syn::{parse_macro_input, Data, DeriveInput};

#[proc_macro_derive(ByteCodeInstructions)]
pub fn construct_bytecode_instructions(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let data = match input.data {
        Data::Enum(data) => data,
        _ => panic!("You can only derive this on enums!"),
    };

    let enum_name = input.ident;
    let get_bytecode_size_tokens = data.variants.iter().enumerate().map(|(i, variant)| {
        let mut size: u8 = 0;
        let i = i as u8;
        match &variant.fields {
            syn::Fields::Named(fields) => {
                for field in &fields.named {
                    match &field.ty {
                        syn::Type::Path(ty) => {
                            let path = ty.path.segments.last().unwrap().ident.to_string();
                            size += match path.as_str() {
                                "u8" => 1,
                                "i8" => 1,
                                "u16" => 2,
                                "i32" => 4,
                                "u32" => 4,
                                "f64" => 8,
                                "bool" => 1,
                                _ => panic!("Field type {path} is unsupported"),
                            }
                        }
                        _ => panic!("Field type {} is unsupported", field.ty.to_token_stream()),
                    }
                }
            }
            syn::Fields::Unnamed(_) => panic!("Unnamed fields are not supported"),
            syn::Fields::Unit => (),
        }
        quote! {
            #i => #size,
        }
    });

    let read_opcode_tokens = data.variants.iter().enumerate().map(|(i, variant)| {
        let i = i as u8;
        let read_fields_tokens = match &variant.fields {
            syn::Fields::Named(fields) => {
                let tokens = fields.named.iter().map(|field| match &field.ty {
                    syn::Type::Path(ty) => {
                        let path = ty.path.segments.last().unwrap().ident.to_string();
                        let read_method = match path.as_str() {
                            "u8" => quote! { reader.read_u8().unwrap() },
                            "i8" => quote! { reader.read_i8().unwrap() },
                            "u16" => quote! { reader.read_u16::<LittleEndian>().unwrap() },
                            "i32" => quote! { reader.read_i32::<LittleEndian>().unwrap() },
                            "u32" => quote! { reader.read_u32::<LittleEndian>().unwrap() },
                            "f64" => quote! { reader.read_f64::<LittleEndian>().unwrap() },
                            "bool" => quote! { reader.read_u8().unwrap() == 0 },
                            _ => panic!("Field type {path} is unsupported"),
                        };
                        let name = field.ident.as_ref().unwrap();
                        quote! {
                            #name: #read_method
                        }
                    }
                    _ => panic!("Field type {} is unsupported", field.ty.to_token_stream()),
                });
                quote! {
                    #(#tokens),*
                }
            }
            syn::Fields::Unnamed(_) => panic!("Unnamed fields are not supported"),
            syn::Fields::Unit => quote! {},
        };
        let variant_name = &variant.ident;
        quote! {
            #i => {
                #enum_name::#variant_name {
                    #read_fields_tokens
                }
            }
        }
    });

    proc_macro::TokenStream::from(quote! {
        impl InstructionSet for #enum_name {
            fn get_bytecode_size(opcode: u8) -> u8 {
                match opcode {
                    #(#get_bytecode_size_tokens)*
                    _ => unimplemented!()
                }
            }

            fn read_opcode<R: Read>(reader: &mut R) -> Instruction {
                let opcode = reader.read_u8().unwrap();
                match opcode {
                    #(#read_opcode_tokens),*
                    _ => panic!("Unhandled opcode: {}", opcode)
                }
            }
        }
    })
}
