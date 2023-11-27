(* TODO: Make cells identifiable with some id. *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Lia.
Require Import Decidable.

Require Import ordering.

(* Logical connections. *)
Inductive LogOp: Type := And | Or.
(* Comparison operators. *)
Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.
(* Binary arithmetic operators. *)
Inductive BinOp: Type := Add | Sub | Mul | Div | Mod.

(* Basic types in our column types. *)
Inductive basic_type: Set :=
  | IntegerType
  | BoolType
  | StringType.

Definition type_matches (lhs rhs: basic_type): bool :=
  match lhs, rhs with
  | IntegerType, IntegerType => true
  | BoolType, BoolType => true
  | StringType, StringType => true
  | _, _ => false
  end.

Definition type_to_coq_type (t: basic_type): Set :=
  match t with
  | IntegerType => nat
  | BoolType => bool
  | StringType => string
  end.

(* A helper instance that allows us to perform ordering, equivalence check on types
   that are wrapped by a another layer called `type_to_coq_type`.

   It is able to:
   * Compare two types.
   * Check if two types are equivalent.

   See the type class definition in `ordering.v` for more details.
 *)
Global Instance can_order (t: basic_type): Ordered (type_to_coq_type t).
  refine (
    match t as t' return Ordered (type_to_coq_type t') with
      | IntegerType => _
      | BoolType => _
      | StringType => _
    end
  ).
Defined.

(* Attributes are themselves string representation of the name. *)
Definition Attribute := basic_type%type.
Definition Symbol := string.
Definition Aggregate := string.

Inductive transform_func : Set.
Inductive aggregate_func : Set.
Inductive func: Set :=
  | transform: transform_func -> func
  | aggregate: aggregate_func -> func
.
Definition func_list: Set := list func%type.

(*
  A distinction is made between the database schema, which specifies the structure
  of the database, and the database instance, which specifies its actual content:
  sets of tuples.
*)

(* A schema is a list of attributes. *)
Definition schema:= (list Attribute).

Fixpoint eqb_list {A: Type} (eqb: A -> A -> bool) (l1 l2: list A): bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1 :: t1, h2 :: t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  end.
