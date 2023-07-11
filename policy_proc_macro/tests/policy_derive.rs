#[policy_proc_macro::policy_carrying]
struct Foo {
    #[allows(abcd)]
    ok: i32,
}
