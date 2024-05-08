use oxc_ast::{
    ast::{JSXAttributeItem, JSXElementName},
    AstKind,
};
use oxc_diagnostics::{
    miette::{self, Diagnostic},
    thiserror::Error,
};
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;

use crate::{context::LintContext, rule::Rule, AstNode};

#[derive(Debug, Error, Diagnostic)]
#[error("eslint-plugin-next(no-styled-jsx-in-document): `styled-jsx` should not be used in `pages/_document.js`")]
#[diagnostic(severity(warning), help("Possible to fix it please see: https://nextjs.org/docs/messages/no-styled-jsx-in-document#possible-ways-to-fix-it"))]
struct NoStyledJsxInDocumentDiagnostic(#[label] pub Span);

#[derive(Debug, Default, Clone)]
pub struct NoStyledJsxInDocument;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Prevent usage of styled-jsx in pages/_document.js.
    ///
    /// ### Why is this bad?
    ///
    /// Custom CSS like styled-jsx is not allowed in a [Custom Document](https://nextjs.org/docs/pages/building-your-application/routing/custom-document).
    ///
    /// ### Example
    /// ```javascript
    /// ```
    NoStyledJsxInDocument,
    correctness,
);

impl Rule for NoStyledJsxInDocument {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let AstKind::JSXOpeningElement(element) = node.kind() else {
            return;
        };

        if !matches!(&element.name, JSXElementName::Identifier(ident) if ident.name == "style") {
            return;
        }

        // Check only pages/_document.* file
        let full_file_path = ctx.file_path();
        let Some(file_name) = full_file_path.file_name() else {
            return;
        };
        let Some(file_name) = file_name.to_str() else { return };
        if !file_name.starts_with("_document.") {
            return;
        }

        let has_jsx_attribute = element.attributes.iter().any(|attribute| {
					matches!(attribute, JSXAttributeItem::Attribute(attribute) if attribute.is_identifier("jsx"))
				});

        if has_jsx_attribute {
            ctx.diagnostic(NoStyledJsxInDocumentDiagnostic(element.span));
        }
    }
}

#[test]
fn test() {
    use crate::tester::Tester;
    use std::path::PathBuf;

    let pass = vec![
        (
            "import Document, { Html, Head, Main, NextScript } from 'next/document'

			        export class MyDocument extends Document {
			          static async getInitialProps(ctx) {
			            const initialProps = await Document.getInitialProps(ctx)
			            return { ...initialProps }
			          }

			          render() {
			            return (
			              <Html>
			                <Head />
			                <body>
			                  <Main />
			                  <NextScript />
			                </body>
			              </Html>
			            )
			          }
			        }",
            None,
            None,
            Some(PathBuf::from("pages/_document.tsx")),
        ),
        (
            r#"import Document, { Html, Head, Main, NextScript } from 'next/document'

			        export class MyDocument extends Document {
			          static async getInitialProps(ctx) {
			            const initialProps = await Document.getInitialProps(ctx)
			            return { ...initialProps }
			          }

			          render() {
			            return (
			              <Html>
			                <Head />
			                <style>{"                  body{                    color:red;                  }                "}</style>
			                <style {...{nonce: '123' }}></style>
			                <body>
			                  <Main />
			                  <NextScript />
			                </body>
			              </Html>
			            )
			          }
			        }"#,
            None,
            None,
            Some(PathBuf::from("pages/_document.tsx")),
        ),
        (
            "
			          export default function Page() {
			            return (
			              <>
			                <p>Hello world</p>
			                <style jsx>{`
			                  p {
			                    color: orange;
			                  }
			                `}</style>
			              </>
			            )
			          }
			          ",
            None,
            None,
            Some(PathBuf::from("pages/index.jsx")),
        ),
    ];

    let fail = vec![(
        r#"
			            import Document, { Html, Head, Main, NextScript } from 'next/document'

			            export class MyDocument extends Document {
			              static async getInitialProps(ctx) {
			                const initialProps = await Document.getInitialProps(ctx)
			                return { ...initialProps }
			              }

			              render() {
			                return (
			                  <Html>
			                    <Head />
			                    <style jsx>{"                    body{                      color:red;                    }                    "}</style>
			                    <body>
			                      <Main />
			                      <NextScript />
			                    </body>
			                  </Html>
			                )
			              }
			            }"#,
        None,
        None,
        Some(PathBuf::from("pages/_document.jsx")),
    )];

    Tester::new(NoStyledJsxInDocument::NAME, pass, fail).test_and_snapshot();
}