# Picachv-Proof

This repository officially hosts the Coq formalism of the $\sf RA^{P}$ language of the Picachv paper. For detailed information, please check our USENIX Security paper.

## Codebase layout

We provide a quick introduction on how this Coq codebase relates to the on-paper formalism.

- `Base`: The formalism of the basic mathemtical objects like lattices, types, ordering systems, etc. to build Picachv's data model as well as operational semantics.
- `Data`: The formalism of the data model (Policies in Section 4. and relational data model in Section 5.).
- `Experimental`: Some experiemental features and/or proofs not yet fully completed (User-Defined Functions and Termination proofs.). For experimental features, we aim to extend Picachv's formal model with the following features in the near future:
  - User-Defined Functions: We outlined the operational semantics for these but working on finalizing them.
  - Termination Proofs: We want to show that Picachv always gives an output.
  - Differential privacy budget control and monitoring.
- `Operational`: The formalism of the $\sf RA^P$ operational semantics and security proofs (The evaluation rules shown in Section 5.).

# LICENCE

The code is subject to Apache 2.0 LICENSE.
