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

/// This attribute denotes the starting point of a policy that allows some operations on the data field.
///
/// # Examples
///
/// ```
/// #[policy_carrying(Deny)]
/// pub struct DiagnosisData {
///     /// Which this `allows` attribute added, we know that the data provider allows
///     /// the 3rd-party code to access this field in a read-only way.
///     #[allows(read)]
///     age: u8,
/// }
/// ```
#[proc_macro_attribute]
pub fn allows(args: TokenStream, input: TokenStream) -> TokenStream {
    input
}

/// This attribute denotes the starting point of a policy that denies some operations on the data field.
///
/// # Examples
///
/// ```
/// #[policy_carrying(Allow)]
/// pub struct DiagnosisData {
///     /// Which this `allows` attribute added, we know that the data provider denies
///     /// the 3rd-party code to access this field in a read-only way.
///     #[denies(read)]
///     age: u8,
/// }
/// ```
#[proc_macro_attribute]
pub fn denies(args: TokenStream, input: TokenStream) -> TokenStream {
    input
}
