use proc_macro::TokenStream;

/// This attribute will parse the struct that is annotated with `#[policy_carrying]` and automatically implement some
/// necessary interfaces for the given struct. Typically, this attribute should be accompanied with a schema/data over-
/// view that describes the input data format.
/// 
/// # Note
/// 
/// This attribute is yet to be implemented. Currently it does nothing and simply outputs the input token stream.
#[proc_macro_attribute]
pub fn policy_carrying(args: TokenStream, input: TokenStream) -> TokenStream {
    input
}
