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
  @param ty  The type of the tuples that will be stored in the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation_np (ty: Tuple.tuple_type) := fbag (Tuple.tuple ty).

(** 
  [relation] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.

  @param ty  The type of the tuples that will be stored in the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation (ty: Tuple.tuple_type) := fbag (Tuple.tuple ty).
