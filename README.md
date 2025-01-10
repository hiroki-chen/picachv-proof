# PCD-Proof

This repository contains formalization for the dataframe data model and relational algebra semantics that captures the privacy policy and mechanically checked proofs of the correctness.

## Codebase layout

We provide a quick introduction on how this Coq codebase relates to the on-paper formalism.

- `Base`: The formalism of the basic mathemtical objects like lattices, types, ordering systems, etc. to build Picachv's data model as well as operational semantics.
- `Data`: The formalism of the data model (Policies in Section 4. and relational data model in Section 5.).
- `Experimental`: Some experiemental features and/or proofs not yet fully completed (User-Defined Functions and Termination proofs.).
- `Operational`: The formalism of the $\sf RA^P$ operational semantics and security proofs (The evaluation rules shown in Section 5.).
## Note

The codebase of Picachv's Coq formalism is still untidy and will be cleaned up as soon as possible. As for now, there might some naming issues and/or inconsistent terms between the Coq code and paper descriptions. We sincerely apologize for any inconvenince and will fix it.
