Require Import Coq.Strings.String.
Require Import types.

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
