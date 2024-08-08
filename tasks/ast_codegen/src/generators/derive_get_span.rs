use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use crate::{
    output,
    schema::{EnumDef, GetGenerics, StructDef, ToType, TypeDef},
    util::ToIdent,
    Generator, GeneratorOutput, LateCtx,
};

use super::{define_generator, generated_header};

define_generator! {
    pub struct DeriveGetSpan;
}

impl Generator for DeriveGetSpan {
    fn name(&self) -> &'static str {
        stringify!(DeriveGetSpan)
    }

    fn generate(&mut self, ctx: &LateCtx) -> GeneratorOutput {
        let trait_name = format_ident!("GetSpan");
        let method_name = format_ident!("span");
        let self_type = quote!(&self);
        let result_type = quote!(Span);
        let result_expr = quote!(self.span);
        let out = derive(&trait_name, &method_name, &self_type, &result_type, &result_expr, ctx);

        GeneratorOutput::Stream((output(crate::AST_CRATE, "derive_get_span.rs"), out))
    }
}

define_generator! {
    pub struct DeriveGetSpanMut;
}

impl Generator for DeriveGetSpanMut {
    fn name(&self) -> &'static str {
        stringify!(DeriveGetSpanMut)
    }

    fn generate(&mut self, ctx: &LateCtx) -> GeneratorOutput {
        let trait_name = format_ident!("GetSpanMut");
        let method_name = format_ident!("span_mut");
        let self_type = quote!(&mut self);
        let result_type = quote!(&mut Span);
        let result_expr = quote!(&mut self.span);
        let out = derive(&trait_name, &method_name, &self_type, &result_type, &result_expr, ctx);

        GeneratorOutput::Stream((output(crate::AST_CRATE, "derive_get_span_mut.rs"), out))
    }
}

fn derive(
    trait_name: &Ident,
    method_name: &Ident,
    self_type: &TokenStream,
    result_type: &TokenStream,
    result_expr: &TokenStream,
    ctx: &LateCtx,
) -> TokenStream {
    let impls: Vec<TokenStream> = ctx
        .schema
        .definitions
        .iter()
        .filter(|def| def.visitable())
        .map(|def| match &def {
            TypeDef::Enum(def) => derive_enum(def, trait_name, method_name, self_type, result_type),
            TypeDef::Struct(def) => {
                derive_struct(def, trait_name, method_name, self_type, result_type, result_expr)
            }
        })
        .collect();

    let header = generated_header!();

    quote! {
        #header
        insert!("#![allow(clippy::match_same_arms)]");
        endl!();

        use oxc_span::{#trait_name, Span};
        endl!();
        use crate::ast::*;
        endl!();

        #(#impls)*
    }
}

fn derive_enum(
    def: &EnumDef,
    trait_name: &Ident,
    method_name: &Ident,
    self_type: &TokenStream,
    result_type: &TokenStream,
) -> TokenStream {
    let target_type = def.to_type();
    let generics = def.generics();

    let matches = def.all_variants().map(|var| {
        let ident = var.ident();
        quote!(Self :: #ident(it) => it.#method_name())
    });

    quote! {
        impl #generics #trait_name for #target_type {
            fn #method_name(#self_type) -> #result_type {
                match self {
                    #(#matches),*
                }
            }
        }
        endl!();
    }
}

fn derive_struct(
    def: &StructDef,
    trait_name: &Ident,
    method_name: &Ident,
    self_type: &TokenStream,
    result_type: &TokenStream,
    result_expr: &TokenStream,
) -> TokenStream {
    let target_type = def.to_type();
    let generics = def.generics();

    let span_field = def.fields.iter().find(|field| field.markers.span);
    let result_expr = if let Some(span_field) = span_field {
        let ident = span_field.name.as_ref().map(ToIdent::to_ident).unwrap();
        quote!(self.#ident.#method_name())
    } else {
        result_expr.clone()
    };

    quote! {
        impl #generics #trait_name for #target_type {
            #[inline]
            fn #method_name(#self_type) -> #result_type {
                #result_expr
            }
        }
        endl!();
    }
}
