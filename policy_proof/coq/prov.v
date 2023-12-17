Require Import Coq.Lists.List.
Require Import Unicode.Utf8.

Require Import types.
Require Import data_model.

Inductive prov_type: Set :=
  | prov_trans: simple_transform_func -> prov_type
  | prov_agg: simple_aggregate_func -> prov_type
  | prov_noise: prov_type
.

Definition prov_type_label (pt: prov_type): (Policy.policy * Policy.policy) :=
  match pt with
  | prov_trans _ => (Policy.policy_transform, Policy.policy_agg)
  | prov_agg _ => (Policy.policy_transform, Policy.policy_agg)
  | prov_noise => (Policy.policy_agg, Policy.policy_noise)
  end.

(*
    This is an auxiliary definition to help us define the prov type to help prove the
    main theorem that involve the "flow" of each sensitive data piece at the cell level.
*)
Inductive prov: Set :=
  | prov_list: prov_type -> list (nat * prov) -> prov
  | prov_none: prov
.

Definition prov_ctx := list (nat * prov).
