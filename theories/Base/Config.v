Require Import Utf8.

Require Import Relation.
Require Import Trace.
Require Import Types.

(*
  `config` is an inductive type that defines a configuration for the query evaluation.
  It is either:
  * `ConfigError` => An error has occurred.
  * `ConfigOut` => The query evaluation is ok and the result is ready to be output. It consists of:
    - `s` => The schema of the output relation.
    - `c` => The output configuration.
*)
Inductive config: Type :=
  | ConfigError: config
  | ConfigOut: relation_wrapped → budget → trace → config
.
