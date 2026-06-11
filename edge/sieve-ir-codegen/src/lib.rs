//! This crate statically parses a SIEVE IR circuit at compile time and produces a circuit using
//! `sieve-ir-api`, thereby eliminating the runtime overhead of dynamically parsing and interpretting
//! the circuit.
//!

#![deny(missing_docs)]

extern crate proc_macro;

use mac_n_cheese_sieve_parser::{
    ConversionSemantics, FunctionBodyVisitor, Identifier, Number, PluginBinding, RelationVisitor,
    TypeId, TypedCount, TypedWireRange, WireId, WireRange, text_parser::RelationReader,
};
use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::quote;
use std::io::{Read, Seek};
use std::path::PathBuf;
use swanky_field::PrimeFiniteField;
use swanky_serialization::CanonicalSerialize;
use syn::{
    LitStr, Token,
    parse::{Parse, ParseStream},
    parse_macro_input,
};

struct Input {
    struct_name: Ident,
    _comma1: Token![,],
    circuit: LitStr,
}

impl Parse for Input {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        Ok(Input {
            struct_name: input.parse()?,
            _comma1: input.parse()?,
            circuit: input.parse()?,
        })
    }
}

/// Compiles the given file as a SIEVE IR circuit at compile time.
/// The path is relative to the macro invocation.
///
/// The following example creates a struct `Example` whose `execute` function matches the
/// `example.sieve` circuit file:
/// ```ignore
/// compile_sieve_ir!(Example, "../circuits/example.sieve");
/// ```
#[proc_macro]
pub fn compile_sieve_ir(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the input file path.
    let input = parse_macro_input!(input as Input);
    let input_file = input.circuit;

    // Get the `Span` where the macro was called
    let relative_path = proc_macro::Span::call_site()
        .local_file()
        .expect("Failed to get caller's file path");

    // Get the caller's project directory.
    // let manifest_path = std::env::var("CARGO_MANIFEST_DIR").expect("Failed to get caller's project directory");
    // Hack to work with workspaces. https://stackoverflow.com/a/74942075
    let output = std::process::Command::new(env!("CARGO"))
        .arg("locate-project")
        .arg("--workspace")
        .arg("--message-format=plain")
        .output()
        .unwrap()
        .stdout;
    let mut manifest_path = PathBuf::from(std::str::from_utf8(&output).unwrap().trim());
    manifest_path.pop();

    let mut path = manifest_path;
    path.push(relative_path);

    // Remove filename from path.
    if !path.pop() {
        panic!("Failed to remove filename from path");
    }

    // Append input file.
    path.push(input_file.value());

    let circuit = std::fs::read_to_string(path).expect("Failed to read input circuit file");

    // println!("Input circuit:\n{}", circuit);

    codegen_sieve_ir(&circuit, &input.struct_name)
}

/// Compiles the given string as a SIEVE IR circuit at compile time.
///
/// The following example creates a struct `Example` whose `execute` function matches the
/// SIEVE IR circuit given as a string.
/// ```ignore
/// compile_sieve_ir_str!( Example,
///     "version 2.0.0;
///     circuit;
///     @type field 2;
///     @begin
///       ...
///     @end
/// ");
/// ```
#[proc_macro]
pub fn compile_sieve_ir_str(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the input.
    let input = parse_macro_input!(input as Input);

    codegen_sieve_ir(&input.circuit.value(), &input.struct_name)
}

fn codegen_sieve_ir(circuit: &str, struct_name: &Ident) -> proc_macro::TokenStream {
    let parser =
        RelationReader::new(std::io::Cursor::new(circuit)).expect("Invalid SIEVE IR circuit");

    let impls = codegen_impls(parser, struct_name);
    quote! {
        #[derive(Copy, Clone, Debug)]
        pub struct #struct_name;

        #impls
    }
    .into()
}

fn codegen_impls<T: Read + Seek>(
    circuit_parser: RelationReader<T>,
    struct_name: &Ident,
) -> TokenStream {
    // let tys = circuit_parser.header().types.clone();
    // tys.iter().map(|ty| {
    //     codegen_impl(&mut circuit_parser, struct_name, ty)
    // })
    // // TODO: Conversion gates, etc.
    // .collect()
    let ty_constraints = type_constraints(&circuit_parser);

    let mut codegen = Codegen::new(&circuit_parser);
    circuit_parser
        .read(&mut codegen)
        .expect("Parsing circuit failed");

    // JP: Hard coding F2 for now.
    let main = codegen.main;
    quote! {
        impl #struct_name {
            pub fn main<B: #ty_constraints>(&self, backend: &mut B) -> swanky_sieve_ir_api::CircuitResult<()> {
                use swanky_serialization::CanonicalSerialize;
                #main
                Ok(())
            }
        }
        impl swanky_sieve_ir_api::CircuitExecuter<swanky_field_binary::F2> for #struct_name {
            fn execute<B: #ty_constraints>(&self, backend: &mut B) -> swanky_sieve_ir_api::CircuitResult<()> {
                self.main(backend)
            }
        }
        // Parsed circuits never contain higher degree constraints, so executing them on a
        // `HigherDegreeBackend` only exercises the `FieldBackend` gates.
        // JP: Hard coding F2/F128b for now.
        swanky_sieve_ir_api::delegate_higher_degree_executer!(
            swanky_field_binary::F2,
            swanky_field_binary::F128b,
            #struct_name
        );
    }
}

type SIEVEType = mac_n_cheese_sieve_parser::Type;

fn modulus_to_type_var(modulus: &Number) -> TokenStream {
    if *modulus == mac_n_cheese_sieve_parser::Number::from_u64(2) {
        // TODO: Is there a way to reify types?
        quote! {swanky_field_binary::F2}
    } else {
        panic!(
            "SEIVE IR codegen currently only supports F2, not {:?}",
            modulus
        );
    }
}

fn type_to_type_var(ty: &SIEVEType) -> TokenStream {
    match ty {
        SIEVEType::Field { modulus } => modulus_to_type_var(modulus),
        _ => {
            panic!("SEIVE IR codegen does not currently support type: {ty:?}");
        }
    }
}

fn type_constraints<T: Read + Seek>(circuit_parser: &RelationReader<T>) -> TokenStream {
    circuit_parser
        .header()
        .types
        .iter()
        .map(|ty| match ty {
            SIEVEType::Field { modulus } => {
                let ty_var = modulus_to_type_var(modulus);

                quote! {
                    swanky_sieve_ir_api::FieldBackend<#ty_var>,
                }
            }
            _ => {
                panic!("SEIVE IR codegen does not currently support type: {ty:?}");
            }
        })
        .collect()
}

struct Codegen {
    types: Vec<SIEVEType>,
    type_vars: Vec<TokenStream>,
    main: TokenStream,
}

impl Codegen {
    fn new<T: Seek + Read>(circuit_parser: &RelationReader<T>) -> Self {
        let types = circuit_parser.header().types.clone();
        let type_vars = types.iter().map(type_to_type_var).collect();
        Codegen {
            types,
            type_vars,
            main: TokenStream::new(),
        }
    }

    fn to_type_var(&self, tid: TypeId) -> TokenStream {
        self.type_vars[tid as usize].clone()
    }

    fn to_wire_ident(&self, wid: WireId) -> Ident {
        Ident::new(&format!("v{wid}"), Span::call_site())
    }

    fn reify_constant(&self, tid: TypeId, number: Number) -> TokenStream {
        let ty = &self.types[tid as usize];
        match ty {
            SIEVEType::Field { modulus } => {
                if modulus == &mac_n_cheese_sieve_parser::Number::from_u64(2) {
                    let f = swanky_field_binary::F2::try_from_int(number)
                        .expect("Invalid constant for field");
                    let bytes = f.to_bytes();
                    let arr = bytes
                        .into_iter()
                        .map(Literal::u8_suffixed)
                        .collect::<Vec<_>>();
                    quote! {
                        swanky_field_binary::F2::from_bytes(&generic_array::GenericArray::<u8, <swanky_field_binary::F2 as CanonicalSerialize>::ByteReprLen>::from_array([#(#arr,)*])).unwrap()
                    }
                } else {
                    panic!(
                        "SEIVE IR codegen currently only supports F2, not {:?}",
                        modulus
                    );
                }
            }
            _ => {
                panic!("SEIVE IR codegen does not currently support type: {ty:?}");
            }
        }
    }
}

impl FunctionBodyVisitor for Codegen {
    fn new(&mut self, _ty: TypeId, _first: WireId, _last: WireId) -> swanky_error::Result<()> {
        panic!("new is not supported yet");
    }
    fn delete(&mut self, _ty: TypeId, _first: WireId, _last: WireId) -> swanky_error::Result<()> {
        panic!("delete is not supported yet");
    }
    fn add(
        &mut self,
        ty: TypeId,
        dst: WireId,
        left: WireId,
        right: WireId,
    ) -> swanky_error::Result<()> {
        let ty = self.to_type_var(ty);
        let dst = self.to_wire_ident(dst);
        let left = self.to_wire_ident(left);
        let right = self.to_wire_ident(right);
        self.main.extend(quote! {
            let #dst = <B as swanky_sieve_ir_api::FieldBackend<#ty>>::add(backend, &#left, &#right)?;
        });
        Ok(())
    }
    fn mul(
        &mut self,
        ty: TypeId,
        dst: WireId,
        left: WireId,
        right: WireId,
    ) -> swanky_error::Result<()> {
        let ty = self.to_type_var(ty);
        let dst = self.to_wire_ident(dst);
        let left = self.to_wire_ident(left);
        let right = self.to_wire_ident(right);
        self.main.extend(quote! {
            let #dst = <B as swanky_sieve_ir_api::FieldBackend<#ty>>::mul(backend, &#left, &#right)?;
        });
        Ok(())
    }
    fn addc(
        &mut self,
        ty: TypeId,
        dst: WireId,
        left: WireId,
        right: &Number,
    ) -> swanky_error::Result<()> {
        let fty = self.to_type_var(ty);
        let dst = self.to_wire_ident(dst);
        let left = self.to_wire_ident(left);
        let right = self.reify_constant(ty, *right);
        self.main.extend(quote! {
            let #dst = <B as swanky_sieve_ir_api::FieldBackend<#fty>>::addc(backend, &#left, #right)?;
        });
        Ok(())
    }
    fn mulc(
        &mut self,
        _ty: TypeId,
        _dst: WireId,
        _left: WireId,
        _right: &Number,
    ) -> swanky_error::Result<()> {
        panic!("mulc is not supported yet");
    }
    fn copy(
        &mut self,
        _ty: TypeId,
        _dst: WireRange,
        _src: &[WireRange],
    ) -> swanky_error::Result<()> {
        panic!("copy is not supported yet");
    }
    fn constant(&mut self, _ty: TypeId, _dst: WireId, _src: &Number) -> swanky_error::Result<()> {
        panic!("constant is not supported yet");
    }
    fn public_input(&mut self, _ty: TypeId, _dst: WireRange) -> swanky_error::Result<()> {
        panic!("public_input is not supported yet");
    }
    fn private_input(&mut self, ty: TypeId, dst: WireRange) -> swanky_error::Result<()> {
        let ty = self.to_type_var(ty);
        let statements = dst
            .range()
            .map(|wid| {
                let var = self.to_wire_ident(wid);
                quote! {
                    let #var = <B as swanky_sieve_ir_api::FieldBackend<#ty>>::input_private(backend)?;
                }
            })
            .collect::<Vec<_>>();
        self.main.extend(statements);
        Ok(())
    }
    fn assert_zero(&mut self, ty: TypeId, src: WireId) -> swanky_error::Result<()> {
        let fty = self.to_type_var(ty);
        let src = self.to_wire_ident(src);

        self.main.extend(quote! {
            <B as swanky_sieve_ir_api::FieldBackend<#fty>>::assert_zero(backend, &#src)?;
        });
        Ok(())
    }
    fn convert(
        &mut self,
        _dst: TypedWireRange,
        _src: TypedWireRange,
        _semantics: ConversionSemantics,
    ) -> swanky_error::Result<()> {
        panic!("convert is not supported yet");
    }
    fn call(
        &mut self,
        _dst: &[WireRange],
        _name: Identifier,
        _args: &[WireRange],
    ) -> swanky_error::Result<()> {
        panic!("call is not supported yet");
    }
}
impl RelationVisitor for Codegen {
    type FBV<'a> = Codegen;
    fn define_function<BodyCb>(
        &mut self,
        _name: Identifier,
        _outputs: &[TypedCount],
        _inputs: &[TypedCount],
        _body: BodyCb,
    ) -> swanky_error::Result<()>
    where
        for<'a, 'b> BodyCb: FnOnce(&'a mut Self::FBV<'b>) -> swanky_error::Result<()>,
    {
        panic!("define_function is not supported yet");
    }
    fn define_plugin_function(
        &mut self,
        _name: Identifier,
        _outputs: &[TypedCount],
        _inputs: &[TypedCount],
        _body: PluginBinding,
    ) -> swanky_error::Result<()> {
        panic!("define_plugin_function is not supported yet");
    }
}
