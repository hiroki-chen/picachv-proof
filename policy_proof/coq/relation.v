Require Import Nat.
Require Import List.
Require Import String.

Require Import data_model.
Require Import ordering.
Require Import finite_bags.
Require Import types.

(** 
  [relation_np] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.
  Note: this will make tuple ignorant of the policy.
  @param s   The schema of the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation_np (s: schema) := fbag (Tuple.tuple_np s).

(** 
  [relation] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.

  @param s   The schema of the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation (s: schema) := fbag (Tuple.tuple s).

(**
  [inject_tuple_id_relation] is a function that takes a tuple type [ty], a relation [r] of type [relation_np ty] and an id [id] as arguments and returns a relation of type [relation ty].
  This function is used to inject an id into a relation. This is useful when we want to inject a policy into a relation.
  @param s   The schema of the relation that we want to inject an id into.
  @param r   The relation that we want to inject an id into.
  @param id  The id that we want to inject into the relation.
  @return    A relation of type [relation ty].
*)
Fixpoint inject_tuple_id_relation
  (s: schema)
  (r: relation_np s)
  (id: nat)
: relation s :=
  match r with
  | nil => nil
  | cons t r' =>
  cons (Tuple.inject_tuple_id s t id)
       (inject_tuple_id_relation s r' (id + List.length s))
  end.

Fixpoint extract_as_cell_list s (r: relation s) : list nat :=
  match r with
  | nil => nil
  | cons t r' => (Tuple.extract_as_cell_id s t) ++ (extract_as_cell_list s r')
  end.
