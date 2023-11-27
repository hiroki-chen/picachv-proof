Require Import List.
Require Import String.

Require Import types.
Require Import relation.
Require Import formula.
Require Import data_model.
Require Import ordering.
Require Import finite_bags.

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

Definition context: Set := list (nat * schema)%type.
Fixpoint env (ctx: context): Set :=
  match ctx with
    | nil => unit
    | (_, s) :: ctx' => relation s * env ctx'
  end%type.

(* TODO: we also need to reason about how schema (type) is changed in the course of operators. *)
Inductive Operator: schema -> Set :=
  | operator_empty: forall s, Operator s
  | operator_relation: forall s, nat -> Operator s
  | operator_union: forall s, Operator s -> Operator s -> Operator s
  | operator_join: forall s1 s2, Operator s1 -> Operator s2 -> Operator (s1 ++ s2)
  | operator_project: forall s, project_list -> Operator s -> Operator s
  | operator_select: forall s, formula s -> Operator s -> Operator s
  | operator_grouby_having: forall s, groupby_list -> agg_list s -> formula s -> Operator s -> Operator s
.

Definition config (ctx: context) := (Policy.context * Configuration.privacy * Operator ((snd (List.hd (0, nil) ctx))) * env ctx)%type.

(**  
  [eval] is a Fixpoint in Coq, which means it is a recursive function. It is used to evaluate a
  query on a given configuration and schema.

  @param c   A configuration of type [config s]. This configuration is a tuple containing a Policy
             context, an environment, a privacy setting, an Operator, and a tuple type.

  @return    The result of the evaluation of the query on the given configuration.
*)
Fixpoint eval (ctx: context) (c: config ctx): option (config ctx) :=
  match get_operator c with
  | operator_empty => None
  (* TODO: IMPLEMENT THIS. *)
  | _ => None 
  end.