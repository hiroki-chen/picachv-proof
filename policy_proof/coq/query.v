Require Import List.
Require Import String.
Require Import Unicode.Utf8.
Require Import Lia.

Require Import types.
Require Import relation.
Require Import formula.
Require Import data_model.
Require Import ordering.
Require Import lattice.
Require Import finite_bags.
Require Import util.

Set Printing Coercions.
Set Printing Implicit.
Set Printing Projections.

Inductive trans_func (ℓ1 ℓ2: Policy.policy): Set :=
  | trans_func_with_label: ∀ bt, transform_func bt → trans_func ℓ1 ℓ2
.

Definition trans_func_denote ℓ1 ℓ2 (f: trans_func ℓ1 ℓ2) : basic_type -> basic_type. Admitted.

Fixpoint schema_to_anf (s: schema): list nat :=
  match s with
    | nil => nil
    | cons t ty' => cons 0 (List.map S (schema_to_anf ty'))
  end.

Inductive project_list: Set :=
  | project_star: project_list
  | project s: list (∀ bt, agg_expression s bt) → project_list
.

Definition groupby_list := (list nat)%type.
Definition agg_list s := (list (∀ bt, agg_expression s bt))%type.

Definition schema_env:= list (nat * schema)%type.
Fixpoint relation_env (se: schema_env): Set :=
  match se with
    | nil => unit
    | (_, s) :: se' => (relation s * relation_env se')%type
  end.

Fixpoint lookup_schema (n: nat) (se: schema_env): schema :=
  match se with
    | nil => nil
    | (n', s) :: se' => if Nat.eqb n n' then s else lookup_schema n se'
  end.

(*
  `env` is a definition for an environment in a given schema `s`. 
  It is a list of tuples, where each tuple consists of a relation, 
  a list of 'selected' attributes, a groupby list, and a list of tuples.

  - The relation is a list of tuples of type `Tuple.tuple s` for determing the concrete relation
    that is used for the expression evaluation.
  - The selected attributes is a list of natural numbers, which are the indices of the attributes
    in the schema that are used for the expression evaluation.
  - The groupby list is a list of natural numbers, which are the indices of the attributes in the
    schema that are used for grouping.
  - The list of tuples is a list of tuples of type `Tuple.tuple s`.

  This environment is used in the context of database query operations.
*)
Definition env_slice (s: schema) := (relation s * list nat * groupby_list * list (Tuple.tuple s))%type.
Definition ℰ (s: schema): Set := list (env_slice s)%type.

Definition env_slice_get_relation {s} (e: env_slice s) : relation s :=
  match e with
    | (r, _, _, _) => r
  end.

Definition env_slice_get_selected {s} (e: env_slice s) : list nat :=
  match e with
    | (_, s, _, _) => s
  end.

Definition env_slice_get_groupby {s} (e: env_slice s) : groupby_list :=
  match e with
    | (_, _, g, _) => g
  end.

Definition env_slice_get_tuples {s} (e: env_slice s) : list (Tuple.tuple s) :=
  match e with
    | (_, _, _, t) => t
  end.

Definition get_env_slice s (e: ℰ s) (non_empty: List.length e > 0) : env_slice s.
  destruct e.
  - simpl in non_empty. lia.
  - exact e.
Defined.

Inductive Operator: Set :=
  | operator_empty: Operator
  | operator_relation: nat → Operator
  | operator_union: Operator → Operator → Operator
  | operator_join: Operator → Operator → Operator
  | operator_project: project_list → Operator → Operator
  | operator_select: ∀ s, formula s → Operator → Operator
  | operator_grouby_having: ∀ s, groupby_list → agg_list s → formula s → Operator → Operator
.

(*
  `Configuration` is a dependent type on a schema that has two constructors.
*)
Inductive config: Set :=
  | config_terminal: config
  | config_error: config
  | config_ok: ∀ s, Policy.context → Configuration.privacy → ℰ s → config
.

Notation "'⟨' s Γ β ℰ '⟩'":= (config_ok s Γ β ℰ)
  (at level 10, s at next level, Γ at next level, β at next level, ℰ at next level,
  no associativity).

(*
  `step_cell` is an inductive type that defines a relation between two configurations except that
  it works on the level of cells. This transition is defined by a notation `c1 >[ f ]> c2` where `f`
  is a function that transforms the cell.
*)
Reserved Notation "c1 '>[' f ']>' c2" (at level 50, no associativity).
Inductive step_cell: ∀ ℓ1 ℓ2, trans_func ℓ1 ℓ2 → config → config → Prop :=
  (* If the environment is empty, then we cannot do anything.  *)
  | E_CTransSkip1:
      ∀ ℓ1 ℓ2 s Γ β e (f: trans_func ℓ1 ℓ2), 
          List.length e = 0 →
          ⟨ s Γ β e ⟩ >[ f ]> ⟨ s Γ β e ⟩
  (* If the environment is not empty but there is no active tuples, we cannot do anything. *)
  | E_CTransSkip2:
      ∀ ℓ1 ℓ2 s Γ β e (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0) tl,
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          List.length tl = 0 → 
          ⟨ s Γ β e ⟩ >[ f ]> ⟨ s Γ β e ⟩
  (* No active labels are found; this should be an error. *)
  | E_CTransError:
      ∀ ℓ1 ℓ2 s Γ β e (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          None = Policy.label_lookup c_idx Γ →
          ⟨ s Γ β e ⟩ >[ f ]> config_error
  (* The label does not flow to the current one. *)
  | E_CTransInvalid:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ β e (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (ℓcur, Some ℓdisc) = Policy.label_lookup c_idx Γ →
          ~ (ℓcur ⊑ ℓ1) →
          ⟨ s Γ β e ⟩ >[ f ]> ⟨ s Γ β e ⟩
  (* This transition is ok. *)
  | E_CTransOk:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e e' (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl tl' (tl_non_empty: List.length tl > 0) t t' c c' c_idx (idx_bound: c_idx < List.length s),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (ℓcur, Some ℓdisc) = Policy.label_lookup c_idx Γ →
          (* udpate the policy environment. *)
          ℓcur ⊑ ℓ1 → Γ' = Policy.update_label c_idx Γ (ℓ2, Some ℓdisc) →
          (* TODO: Update the tuple. *)
          tl' = set_nth tl 0 →
          c = Tuple.nth _ c_idx idx_bound → c' = (trans_func_denote _ _ f) c →
          t' = Tuple.set_nth_type_match _ c_idx c' idx_bound t →
          (* update the environment. *)
          ⟨ s Γ β e ⟩ >[ f ]> ⟨ s Γ' β e' ⟩
where "c1 '>[' f ']>' c2" := (step_cell _ _ f c1 c2).

(* 
  `step_config` is an inductive type representing the transition rules for configurations. 
  It defines how a configuration changes from one state to another by the query.
  The rules are:
  - `E_Error`   : If the configuration is error, it remains error.
  ...
*)
Reserved Notation "c1 '=[' o ']=>' c2" (at level 50, left associativity).
Inductive step_config: Operator → config → config → Prop :=
  (* Empty operator clears the environment. *)
  | E_Empty: ∀ s1 s2 Γ β (e: ℰ s1),
      ⟨ s1 Γ β e ⟩ =[ operator_empty ]=> ⟨ s2 Γ β nil ⟩
  (* If the operator returns an empty environment, we do nothing. *)
  | E_ProjEmpty: ∀ s1 s2 Γ Γ' β β' (e: ℰ s1) (e': ℰ s2) project_list o,
      ⟨ s1 Γ β e ⟩ =[ o ]=> ⟨ s2 Γ' β' e' ⟩ →
      ⟨ s1 Γ β e ⟩ =[ operator_project project_list o ]=> ⟨ s2 Γ' β' nil ⟩
  | E_Proj: ∀ s1 s2 Γ Γ' β β' (e: ℰ s1) (e': ℰ s2) project_list o,
      ⟨ s1 Γ β e ⟩ =[ o ]=> ⟨ s2 Γ' β' e' ⟩ →
      List.length e' > 0 →
      ⟨ s1 Γ β e ⟩ =[ operator_project project_list o]=> ⟨ s2 Γ' β' e' ⟩
where "c1 '=[' o ']=>' c2" := (step_config o c1 c2).
