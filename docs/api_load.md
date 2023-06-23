# Loading and loading the APIs

We want to de-couple the implementation of the data analysis framework and the data access API set that eventually enforces the policy. Therefore, we move the API as a seperate pluggable module. By introducing a global manager that keeps track of the active API module, we dispatch the requests to the entry function of the API set which does the job for us, and the users are completely ignorant of this behavior.

There are, however, several remaining issues left for us to be resolved:

* If we keep the API set as a Rust trait `trait PolicyApiSet: Send + Sync`, the abi stability is limited to only Rust code that is compiled using the same toolchain, and backward compatilibity also becomes a problem.

