Require Import List.
Require Import String.

Require Import types.
Require Import relation.
Require Import formula.
Require Import data_model.

Definition project_list : Set := list simple_atomic_expression%type.

Fixpoint bounded_list (proj: project_list) (ty: Tuple.tuple_type) : Prop :=
  match proj with
    | nil => True
    | h :: t => match h with
                  | simple_atomic_expression_column n => n < List.length ty
                  | _ => True
                end /\ bounded_list t ty
  end.

Inductive Query: schema -> Set :=
  | query_empty: forall s, Query s
  | query_relation: forall s, relation s -> Query s
  | query_union: forall s, Query s -> Query s -> Query s
  | query_join: forall s1 s2, Query s1 -> Query s2 -> Query (s1 ++ s2)
  | query_project:
      forall s (proj: project_list) (bounded: bounded_list proj (schema_denote s)),
        Query s -> Query s
  | query_select:
    forall s (where_exp: simple_formula), Query s -> Query s
  (* TODO: Design `groupby`. *)
  | query_grouby_agg: forall s, Query s -> Query s
  .
