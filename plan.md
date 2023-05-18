# Theoretic Part of the PCD

We may need to prove the following facts (hopefully they can be achieved):

* The generator (or functions that take high-order functions) can indeed emit the policy-compliant APIs. The formal rule may take the form:

```txt
forall t: type, p: params, d: data_structure, DP_GENERATOR(t, p, d) = dp_api ==> PP(dp_api).
forall t: type, p: params, d: data_structure, MAX_GENERATOR(t, p, d) = max_api ==> PP(dp_api).
```

* The compositional rule (we want the generated APIs to be modular):

```txt
forall a1: api, a2: api, PP(a1) /\ PP(a2) ==> PP(a1 + a2).
```

May involve some states since APIs are not always compliant. As such, the theorem may involve another predicate that contains the state $\sigma$.

* If we use states, we need to model the state transition and the design thereof formally so that the APIs are policy-compliant.

# Implementation of the PCD.

We can generate some annotations on the expansion of the procedural macros, which the theorem prover takes as input and then can reason about the correctness.

# Use Cases

Case Study: Biobank search
* Aggregate: Given length, how many people matches with this given length.
* Redaction: For given genome string, how many maximum length should be accessed (redacted).
* Boolean request: yes/no
* Anonymization should be applied: noise be added to the result.
* Different sources of policies: Merge policies.

The scheme to search relative genome: (compressed) longest substring genome, longest >= threshold.
