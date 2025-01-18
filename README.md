# Coq Proof Library for Picachv

This repository officially hosts the Coq formalism of the $\sf RA^{P}$ language of the Picachv paper. For detailed information, please check our USENIX Security paper.

To cite this repository, please use the following bibtex format.

```tex
@inproceedings{chen2025picachv,
  title={Picachv: Formally Verified Data Use Policy Enforcement for Secure Data Analytics},
  author={Chen, Haobin Hiroki and Chen, Hongbo and Sun, Mingshen and Wang, Chenghong and Wang, XiaoFeng},
  booktitle={34th USENIX Security Symposium (USENIX Security 25)},
  year={2025},
  location={Seattle, WA, USA}
}
```

## Codebase layout

We provide a quick introduction on how this Coq codebase relates to the on-paper formalism.

- `Base`: The formalism of the basic mathemtical objects like lattices, types, ordering systems, etc. to build Picachv's data model as well as operational semantics.
- `Data`: The formalism of the data model (Policies in Section 4. and relational data model in Section 5.).
- `Experimental`: Some experiemental features and/or proofs not yet fully completed (User-Defined Functions and Termination proofs.). For experimental features, we aim to extend Picachv's formal model with the following features in the near future:
  - User-Defined Functions: We outlined the operational semantics for these but working on finalizing them.
  - Termination Proofs: We want to show that Picachv always gives an output.
  - Differential privacy budget control and monitoring.
- `Operational`: The formalism of the $\sf RA^P$ operational semantics and security proofs (The evaluation rules shown in Section 5.).

## Installation and Usage

We provide users with a simple wrapper script in Python called `run`. You can easily type check the Coq proofs by using the following command.

```sh
./run --allow_admitted
```

Because there are some experimental features, `admitted` proofs will exist. You may check all the `admitted` proofs under the `theories/Experimental` directory.

# LICENCE

The code is subject to the Apache-2.0 license.
