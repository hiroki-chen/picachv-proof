(* TODO: Make cells identifiable with some id. *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Lia.
Require Import Decidable.
Require Import Unicode.Utf8.

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
Definition Attribute := (basic_type * string)%type.
Definition Symbol := string.
Definition Aggregate := string.

Inductive transform_func (bt: basic_type): Set :=
  | tf_id: transform_func bt
  | tf_other: transform_func bt
.

Inductive simple_transform_func: Set :=
  | stf_id: simple_transform_func
  | stf_other: simple_transform_func
.

Inductive aggregate_func (bt: basic_type): Set.
Inductive simple_aggregate_func: Set.
Inductive func: Set :=
  | transform: ∀ bt, transform_func bt → func
  | aggregate: ∀ bt, aggregate_func bt → func
.

Definition func_list: Set := list func%type.

(*
  A distinction is made between the database schema, which specifies the structure
  of the database, and the database instance, which specifies its actual content:
  sets of tuples.
*)

(* A schema is a list of attributes. *)
Definition schema := (list Attribute).
Definition schema_no_name := (list basic_type).

(* Trasforms a schema into a list of pure basic types. *)
Fixpoint schema_to_no_name (s: schema): schema_no_name :=
  match s with
  | nil => nil
  | (t, _) :: s' => t :: schema_to_no_name s'
  end.

Lemma schema_to_no_name_length: ∀ s,
  length (schema_to_no_name s) = length s.
Proof.
  induction s.
  - auto.
  - simpl. destruct a. rewrite <- IHs. auto.
Qed.
