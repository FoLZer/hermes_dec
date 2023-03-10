extern crate proc_macro;

use quote::{quote, ToTokens};
use syn::{parse_macro_input, Data, DeriveInput};

#[proc_macro_derive(FromBytes)]
pub fn from_bytes_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the input tokens into a syntax tree representation
    let input = parse_macro_input!(input as DeriveInput);

    // Check that the input is a struct
    let data = match input.data {
        Data::Struct(data) => data,
        _ => panic!("FromBytes can only be derived for structs"),
    };

    // Get the struct name and field types
    let name = input.ident;
    let fields = data.fields;

    let read_fields_bytes = fields.iter().map(|field| {
        let ty = &field.ty;
        let ident = field
            .ident
            .as_ref()
            .expect("All fields must have an identifier");
        if let syn::Type::Path(type_path) = ty {
            if type_path.to_token_stream().to_string() == "bool" {
                quote! {
                    #ident: {
                        let size = std::mem::size_of::<#ty>();
                        let slice = &bytes[offset..(offset + size)];
                        offset += size;
                        safe_transmute::transmute_bool_pedantic(slice).unwrap()[0]
                    }
                }
            } else {
                quote! {
                    #ident: {
                        let size = std::mem::size_of::<#ty>();
                        let slice = &bytes[offset..(offset + size)];
                        offset += size;
                        transmute_field(slice)
                    }
                }
            }
        } else {
            quote! {
                #ident: {
                    let size = std::mem::size_of::<#ty>();
                    let slice = &bytes[offset..(offset + size)];
                    offset += size;
                    transmute_field(slice)
                }
            }
        }
    });

    let read_fields = fields.iter().map(|field| {
        let ty = &field.ty;
        let ident = field
            .ident
            .as_ref()
            .expect("All fields must have an identifier");
        if let syn::Type::Path(type_path) = ty {
            if type_path.to_token_stream().to_string() == "bool" {
                quote! {
                    #ident: {
                        let size = std::mem::size_of::<#ty>();
                        let mut v = vec![0; size];
                        reader.read_exact(&mut v).unwrap();
                        safe_transmute::transmute_bool_pedantic(&v).unwrap()[0]
                    }
                }
            } else {
                quote! {
                    #ident: {
                        let size = std::mem::size_of::<#ty>();
                        let mut v = vec![0; size];
                        reader.read_exact(&mut v).unwrap();
                        transmute_field(&v)
                    }
                }
            }
        } else {
            quote! {
                #ident: {
                    let size = std::mem::size_of::<#ty>();
                    let mut v = vec![0; size];
                    reader.read_exact(&mut v).unwrap();
                    transmute_field(&v)
                }
            }
        }
    });

    /*
    // Generate the field read expressions
    let mut offset = 0;
    let read_exprs = fields.iter().map(|field| {
        let ty = &field.ty;
        let ident = field.ident.as_ref().expect("All fields must have an identifier");
        let field_name = ident.to_string();
        let size = quote! { std::mem::size_of::<#ty>() };
        let slice_expr = quote! { &bytes[#offset..(#offset + #size)] };
        let read_expr = quote! { byteorder::ReadBytesExt::read::<#ty>(&mut #slice_expr.as_ref()).unwrap() };
        offset += quote! { #size }.to_string().parse::<usize>().expect(&format!("Expected size to be a string, got: {}", quote! { #size }.to_string()));
        quote! { #ident: #read_expr }
    });
    */

    // Generate the implementation of the FromBytes trait
    let tokens = quote! {
        impl #name {
            fn from_bytes(bytes: &[u8]) -> Self {
                assert_eq!(bytes.len(), std::mem::size_of::<Self>(), "Input bytes must have the same size as the target struct");

                let mut offset = 0;
                #name {
                    #(#read_fields_bytes),*
                }
            }

            fn from_reader<T: Read>(reader: &mut T) -> Self {
                #name {
                    #(#read_fields),*
                }
            }
        }

        unsafe impl TriviallyTransmutable for #name {}
    };

    // Return the generated implementation as a token stream
    proc_macro::TokenStream::from(tokens)
}
