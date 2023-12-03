Require Import List.
Require Import String.
Require Import Unicode.Utf8.

Require Import types.
Require Import relation.
Require Import formula.
Require Import data_model.
Require Import ordering.
Require Import finite_bags.

Set Printing Coercions.
Set Printing Implicit.
Set Printing Projections.

Inductive trans_func (l1 l2: Policy.policy): Set :=
  | trans_func_with_label: ∀ bt, transform_func bt → trans_func l1 l2
.

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
Definition env (s: schema): Set := list (env_slice s)%type.

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
  | config_ok: ∀ s, Policy.context → Configuration.privacy → env s → config
.

(*
  `step_cell` is an inductive type that defines a relation between two configurations except that
  it works on the level of cells. This transition is defined by a notation `c1 >[ f ]> c2` where `f`
  is a function that transforms the cell.
*)
Reserved Notation "c1 '>[' f ']>' c2" (at level 50, left associativity).
Inductive step_cell: ∀ l1 l2, trans_func l1 l2 → config → config→ Prop :=
  | E_CTransSkip:
      ∀ l1 l2 s ctx priv (e: env s) (f: trans_func l1 l2), 
        List.length e = 0 →
      config_ok s ctx priv e >[ f ]> config_ok s ctx priv e
  (* | E_CTransError: ∀ l1 l2 l s ctx priv (e: env s) (f: trans_func l1 l2), *)

where "c1 '>[' f ']>' c2" := (step_cell _ _ f c1 c2).

Notation "{{ ctx priv env }}":= (config_ok _ ctx priv env) (at level 50, left associativity) .

(* 
  `step_config` is an inductive type representing the transition rules for configurations. 
  It defines how a configuration changes from one state to another by the query.
  The rules are:
  - `E_Error`   : If the configuration is error, it remains error.
  ...
*)
Reserved Notation "c1 '=[' o ']=>' c2" (at level 50).
Inductive step_config: Operator → config → config → Prop :=
  (* Empty operator clears the environment. *)
  | E_Empty: ∀ s1 s2 ctx priv (e: env s1), config_ok s1 ctx priv e =[ operator_empty ]=> config_ok s2 ctx priv nil
  (* If the operator returns an empty environment, we do nothing. *)
  | E_ProjEmpty: ∀ s1 s2 ctx ctx' priv priv' (e: env s1) (e': env s2) project_list o,
      config_ok s1 ctx priv e =[ o ]=> config_ok s2 ctx' priv' e' →
      List.length e' = 0 →
      config_ok s1 ctx priv e =[ operator_project project_list o ]=> config_ok s2 ctx' priv' nil
  | E_Proj: ∀ s1 s2 ctx ctx' priv priv' (e: env s1) (e': env s2) project_list o,
      config_ok s1 ctx priv e =[ o ]=> config_ok s2 ctx' priv' e' →
      List.length e' > 0 →
      config_ok s1 ctx priv e =[ operator_project project_list o]=> config_ok s2 ctx' priv' e'
where "c1 '=[' o ']=>' c2" := (step_config o c1 c2).
