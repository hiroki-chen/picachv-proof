# Theoretic Part of the PCD

We may need to prove the following facts (hopefully they can be achieved):

* The generator (or functions that take high-order functions) can indeed emit the policy-compliant APIs. The formal rule may take the form:

  ```txt
  forall t: type, p: params, d: data_structure, DP_GENERATOR(t, p, d) = dp_api ==> PC(dp_api).
  forall t: type, p: params, d: data_structure, MAX_GENERATOR(t, p, d) = max_api ==> PC(dp_api).
  ```

  Question: What does "Policy-Compliant" mean? We need to more explicitly define this property; or we just need to verify that

  $$
  \forall d^{\pi} \in \mathbb{D}^{\Pi}, \vec{f} \gets \mathsf{ApiGen}(d^{\pi}) \Longrightarrow \mathsf{PC}(\pi, \vec{f}).
  $$

  That being said, for all policy-carrying data $d^{\pi}$, given our API generation algorithm $\mathsf{ApiGen}$, it generates a vector of API functions such that $\vec f$ conforms to the policy $\pi$. Thus, "Policy-Compliant" APIs might be a set of properties, like PoBF:

  - The generation of each API is correct and meets the desired property. E.g., $f \gets \mathsf {dp\_max\_gen}(\tau, \langle \delta, \varepsilon \rangle) \Longrightarrow \mathsf{is\_dp}(f, \langle \delta, \varepsilon \rangle)$. In other words, "Policy-Compliant" has different meaning for different kinds of APIs.

  - The compositional rule (we want the generated APIs to be modular):

  ```txt
  forall a1: api, a2: api, PC(a1) /\ PC(a2) ==> PC(a1 + a2).
  ```

  I do not think the above rule holds. So a better interpretation of API combination might be involving some states since APIs are not always compliant. As such, the theorem may involve another predicate that contains the state $\sigma$.

* If we use states, we need to model the state transition and the design thereof formally so that the APIs are policy-compliant.

# Implementation of the PCD.

We can generate some annotations on the expansion of the procedural macros, which the theorem prover takes as input and then can reason about the correctness.

* Policy parser: generates Rust structs with annotations.
* Procedural macro + struct implementation: generates concrete APIs.
* Enforcement: integrate to TEEs by
  - exposing the interfaces via another enclave.
  - compiling the structs + annotations with the source code.

# Use Cases

Case Study: Biobank search
* Aggregate: Given length, how many people match this given length.
* Redaction: Given a genome string, what is the maximum length can be accessed (redacted).
* Boolean request: yes/no
* Anonymization should be applied: noise be added to the result.
* Different sources of policies: Should be able to perform computations on policies.

The scheme to search relative genome: (compressed) longest substring genome, longest >= threshold.
