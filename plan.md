# Theoretic Part of the PCD

We may need to prove the following facts (hopefully they can be achieved):

* The generator (or functions that take high-order functions) can indeed emit the policy-compliant APIs. The formal rule may take the form:

  ```txt
  forall t: type, p: params, d: data_structure, DP_GENERATOR(t, p, d) = dp_api ==> PC(dp_api).
  forall t: type, p: params, d: data_structure, MAX_GENERATOR(t, p, d) = max_api ==> PC(dp_api).
  ```

  Question: What does "Policy-Compliant" mean? We need to more explicitly define this property; or we just need to verify that
  
  $$\forall d^{\pi} \in \mathbb{D}^{\Pi}, \vec{f} \gets \mathsf{ApiGen}(d^{\pi}) \Longrightarrow \mathsf{PC}(\pi, \vec{f}).$$
  
  That being said, for all policy-carrying data $d^{\pi}$, given our API generation algorithm $\mathsf{ApiGen}$, it generates a vector of API functions such that $\vec f$ conforms to the policy $\pi$. Thus, "Policy-Compliant" APIs might be a set of properties, like PoBF:

  - The generation of each API is correct and meets the desired property. E.g., $f \gets \mathsf{dp\\_gen}(\tau, \langle \delta, \varepsilon \rangle, \mathsf{max}) \Longrightarrow \mathsf{is\\_dp}(f, \langle \delta, \varepsilon \rangle)$. In other words, "Policy-Compliant" has different meaning for different kinds of APIs.

  - The compositional rule (we want the generated APIs to be modular):

  ```txt
  forall a1: api, a2: api, PC(a1) /\ PC(a2) ==> PC(a1 + a2).
  ```

  I do not think the above rule holds. So a better interpretation of API combination might be involving some states since APIs are not always compliant. As such, the theorem may involve another predicate that contains the state $\sigma$.

* If we use states, we need to model the state transition and the design thereof formally so that the APIs are policy-compliant.

# The data organization

Can model after the `arrow` crate by Apache.

# Implementation of the PCD.

We can generate some annotations on the expansion of the procedural macros, which the theorem prover takes as input and then can reason about the correctness.

* Policy parser: generates Rust structs with annotations.
* Procedural macro + struct implementation: generates concrete APIs.
* Enforcement: integrate to TEEs by
  - exposing the interfaces via another enclave.
  - compiling the structs + annotations with the source code.

# Support of policy computations

There are scenerios where data may come from different sources of owners and then be merged into a single one. In such cases, we need to take care of the `join` operation, provided that data is organized in a table-like structure. Also, chances are high that two pieces of data take the same schema and they should be `union`ed.

Assuming that the schema $\sigma$ of a PCD has the form $\sigma \coloneqq \langle \mathbf{A}^{n} \Rightarrow \{A_i: D_i \mid i \in [n] \}, \pi \rangle$, where $\mathbf{A}^{n}$ is the set of the attributes, and $\pi$ is the policy on that schema, we thus consider the following two situations:

* $\sigma_1 \bowtie \sigma_2 \Rightarrow \mathbf{A}^{n}\_{1} \bowtie \mathbf{A}^{n}\_{2}, \pi_1 \wedge \pi_2$, and
* $\sigma_1 \cup \sigma_2 \Rightarrow \pi_1 \vee \pi_2$.

Core questions:

* How does $\pi$ look like?
* How to define meet $\vee$ and join $\wedge$ operators on policies $\pi \in \Pi$? Can we just encode policies $\Pi$ as a partially ordered and complete lattice $\langle \Pi, \preceq, \vee, \wedge \rangle$?
* When should policies be `join`ed or `union`ed?

# Use Cases

Case Study: Biobank search
* Aggregate: Given length, how many people match this given length.
* Redaction: Given a genome string, what is the maximum length can be accessed (redacted).
* Boolean request: yes/no
* Anonymization should be applied: noise be added to the result.
* Different sources of policies: Should be able to perform computations on policies.

The scheme to search relative genome: (compressed) longest substring genome, longest >= threshold.

# What form does the policy take?

Although we cannot determine the concrete appearance of the policy now, we may figure out what *properties* it should have. We list them below.

* Should allow lazy evaluation, which means the policy is *not* evaluated until data is *used*, where by 'use' we mean that the sensitive operations like sum, max, etc. are performed on these columns.

# TODOs

- [x] Implement the pluggable API set module: use Rust-to-Rust FFI. Caveat: [see here](./docs/api_load.md).
- [ ] Implement aggregation and DP on it.
  - [x] Implement aggregation expression generation.
  - [x] Implement the executor for aggretation.
  - [x] Find a good way to integrate DP into aggregation:
        apply noises on the aggregated results since we return a context from which we can extract many meaningful information about the aggregated group.
  
- [ ] Implement an parser that automatically generates the API layer.
  - [ ] Human-reable policy parser: use `lalrpop`.
    - [ ] Syntax: partially done.
    - [x] AST design.
    - [ ] codegen to Rust: WIP.
    - [ ] procedural macro generation.
  - [ ] Check policy consistency: use SMT solvers?
- [ ] Encode the policy: can we use extended provenance semi-ring.
- [x] Make executors loadable <= compiled from the policy.
  - [x] Implement the manager and dynamic loader.
  - [x] Attach the reference id to the schema.
  - [x] Integrate to `make_physical_plan` function.
- [ ] Deal with null values (which can be annoying).
- [ ] Implement join on two dataframes and their policy aggregation operations.
