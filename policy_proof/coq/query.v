Require Import List.
Require Import String.

Require Import types.
Require Import relation.
Require Import formula.
Require Import data_model.
Require Import ordering.
Require Import finite_bags.

Set Printing Coercions.
Set Printing Implicit.
Set Printing Projections.


Fixpoint schema_to_anf (s: schema): list nat :=
  match s with
    | nil => nil
    | cons t ty' => cons 0 (List.map S (schema_to_anf ty'))
  end.

Inductive project_list: Set :=
  | project_star: project_list
  | project s: list (forall bt, agg_expression s bt) -> project_list
.

Definition groupby_list := (list nat)%type.
Definition agg_list s := (list (forall bt, agg_expression s bt))%type.

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

(*
  The operator is a dependent type on a schema that has seven constructors.
  Operator: forall s: schema, Set
*)
Inductive Operator: schema -> Set :=
  | operator_empty: forall s, Operator s
  | operator_relation: forall s, nat -> Operator s
  | operator_union: forall s, Operator s -> Operator s -> Operator s
  | operator_join: forall s1 s2, Operator s1 -> Operator s2 -> Operator (s1 ++ s2)
  | operator_project: forall s, project_list -> Operator s -> Operator s
  | operator_select: forall s, formula s -> Operator s -> Operator s
  | operator_grouby_having: forall s, groupby_list -> agg_list s -> formula s -> Operator s -> Operator s
.

Inductive config: Set :=
  | config_terminal: config
  | config_ok: forall s, Policy.context -> Configuration.privacy -> env s -> config
.

Definition hd_option {A: Type} (l: list A): option A :=
  match l with
    | nil => None
    | cons hd _ => Some hd
  end.

Reserved Notation "c1 '=[' o ']=>' c2" (at level 50, left associativity).
(* 
  `step` is an inductive type representing the transition rules for configurations. 
  It defines how a configuration changes from one state to another by the query.
  The rules are:
  - `E_Error`   : If the configuration is error, it remains error.
  ...
*)
Inductive step: forall s, Operator s -> config -> config -> Prop :=
  (* Error state can no longer be forwarded. *)
  | E_Error: forall s (o: Operator s) c, c =[ o ]=> config_terminal
where "c1 '=[' o ']=>' c2" := (step _ o c1 c2).

Lemma cfg_dec: forall (s: schema) (o: Operator s) c1 c2, {c1 =[ o ]=> c2} + {~ c1 =[ o ]=> c2}.
Admitted.

Lemma cfg_eq_dec: forall (c1 c2: config), {c1 = c2} + {c1 <> c2}.
Admitted.
