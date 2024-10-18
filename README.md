# PCD-Proof

This repository contains formalization for the dataframe data model and relational algebra semantics that captures the privacy policy and mechanically checked proofs of the correctness.

Authors:

* Hiroki Chen @ Indiana University ([haobchen@iu.edu](mailto:haobchen@iu.edu))
* Hongbo Chen @ Indiana University ([hc50@iu.edu](mailto:hc50@iu.edu))

## Prerequisites

You should install Coq >= 8.18.0 to ensure that this project compiles.

## Project layout

* `data_model.v`: Coq formalization for basic data models.
* `finite_bags.v`: abstract type class interface for the multiset.
* `expression.v`: Coq formalization for RA expressions.
* `lattice.v`: abstract type class interface for lattice.
* `ordering.v`: defines comparison over Coq's native types and internal data types.
* `prov.v`: contains coq formalization for provenance types.
* `relation.v`: contains Coq formalization on the relation $R$.
* `security.v`: security property proofs.
* `semantics.v`: formalizes the semantics and proves its termination, deterministicism.
* `types.v`: some basic types.
* `util.v`: utility lemmas and theorems, and some useful functions.

## Compile the projects

```sh
$ cd ./theories
$ coq_makefile -f ./_CoqProject -o Makefile
$ make
```

If the code compiles, all the proofs are successfully validated by Coq's type checker.
