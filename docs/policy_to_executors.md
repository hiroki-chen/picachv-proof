# Building Executors from Policy

We want to de-couple the implementation of the data analysis framework and the physical executor set that eventually enforces the policy. Therefore, we move the executors as a seperate pluggable module. By introducing a global manager that keeps track of the active executors, we dispatch the constructed physical plans to thedynamically loadable executors which do the job for us, and the users are completely ignorant of this behavior.

There are, however, several remaining issues left for us to be resolved:

* Rust-to-Rust Foreign Function Interfaces (FFIs) are still unstable. To allow backward compatibility, `abi_stable` can be used, but `std` should be replaced by its standard library.

  Solution: temporarily sacrifice the backward compatibility and make sure that the module and library are built by the same Rust toolchain.
* Trait object pointer is *fat*, meaning that we need to transfer both the pointer to the object and that to the vtable to the caller. This can be done by passing a `*mut Box<dyn Trait>` pointer. Then the owenership is transferred from creator to the caller.

# Layout of an executor library

By default, the data analysis library will try to load the module and find two symbols to create the executors and load the necessary data structures. The first function is called `on_load`, which is called upon the library is loaded. The prototype is

```rust
#[no_mangle]
extern "C" fn on_load(args: *const u8, args_len: usize) -> i32;
```

This function can be regarded as a prelogue function. Any preparation tasks are fulfilled by this function.  Typically, we will want to register data or users when library is initially loaded.

Yet there is another function called `create_executor` whose prototype is

```rust
#[no_mangle]
extern "C" fn create_executor(
    executor_type: u64,
    args: *const u8,
    args_len: usize,
    p_executor: *mut usize,
) -> i64;
```

Similarly, if the policy allows for the use of some aggregation functions (e.g., sum, max, etc.), the library should also implement them in the following form

```rust
#[no_mangle]
extern "C" fn agg_sum(
  args: *const u8,
  args_len: usize,
) -> i64;
```
and note tha the function arguments are serialized using `serde_json` and can be de-serialized back.

This function creates new executors on demand of the data analysis framework when the query is evaluated at the physical level.

## Examples

The `examples` folder contains the sample usage of compiling the executors into a standalong shared library, which can be later loaded by the program. The `executor_lib` implements the minimal set of executors that can be dynamically loaded to the data analysis framework, and `executor_user` is the application that performs the data analysis job.
