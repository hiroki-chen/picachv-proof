Require Import Utf8.

Require Import data_model.
Require Import prov.
Require Import relation.
Require Import types.
Require Import util.

(*
  `config` is an inductive type that defines a configuration for the query evaluation.
  It is either:
  * `config_error` => An error has occurred.
  * `config_ok` => The query evaluation is ok. It consists of:
    - `db` => The database.
    - `Γ` => The policy environment.
    - `β` => The privacy budget.
    - `p` => The provenance context.
  * `config_output` => The query evaluation is ok and the result is ready to be output. It consists of:
    - `s` => The schema of the output relation.
    - `c` => The output configuration.
*)
Inductive config: Type :=
  | config_error: config
  | config_ok: database → Policy.context → budget → prov_ctx -> config
  | config_output: relation_wrapped → config → config
.

Lemma config_output_eq_spec: ∀ r1 r2 c1 c2,
  config_output r1 c1 = config_output r2 c2 ↔ r1 = r2 ∧ c1 = c2.
Proof.
  split; intros.
  - inversion H. subst. auto.
  - destruct H. subst. auto.
Qed.

Definition valid_contexts (Γ: Policy.context) (p: prov_ctx): Prop :=
  let l1 := List.map fst Γ in
  let l2 := List.map fst p in
  sublist _ l1 l2 ∧ sublist _ l2 l1.

Fixpoint config_valid c: Prop :=
  match c with
  | config_error => False
  | config_ok db Γ β p => valid_contexts Γ p
  | config_output _ c' => config_valid c'
  end.

Notation "'⟨' db Γ β p '⟩'":= (config_ok db Γ β p)
  (at level 10, db at next level, Γ at next level, β at next level, p at next level, no associativity).
