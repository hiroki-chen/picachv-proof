Require Import Coq.Lists.List.
Require Import Unicode.Utf8.

Require Import types.
Require Import data_model.

Inductive prov_type: Set :=
  | prov_trans: simple_transform_func -> prov_type
  | prov_agg: simple_aggregate_func -> prov_type
  | prov_noise: prov_type
  | prov_join: prov_type
.

(*
    This is an auxiliary definition to help us define the prov type to help prove the
    main theorem that involve the "flow" of each sensitive data piece at the cell level.
*)
Inductive prov: Set :=
  | prov_list: prov_type -> list (nat * prov) -> prov
  | prov_none: prov
.

Definition prov_ctx := list (nat * prov).
