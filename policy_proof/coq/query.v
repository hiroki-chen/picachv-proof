Require Import String.

Require Import types.
Require Import policy.

Inductive Query: Type :=
  (* Relation *)
  | QueryRel : string -> Query
  (* Union *)
  | QueryUnion : Query -> Query -> Query
  (* (Natural) Join *)
  | QueryJoin : Query -> Query -> Query
  (* GroupBy and Aggregation *)
  | QueryGroupBy : Query -> Query -> Query
  (* Selection *).

(* TODO: The third one should be the operator. *)
Definition config:= (label_lookup, privacy, unit)%type.
