(* TODO: Make cells identifiable with some id. *)
Require Import Arith.
Require Import Bool.
Require Import Decidable.
Require Import Lia.
Require Import List.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import String.
Require Import Unicode.Utf8.

Require Import ordering.

(*
  By its design, privacy budget should be real numbers, but this would introduce undue
  burden for formal verification that we are not prepared to handle. As ℕ is equinume-
  rous to ℚ (in fact, it can be made universal model of computation), we use ℕ to repre-
  sent the real numbers, and this is indeed without loss of generality.
*)
Definition dp_param := (nat * nat)%type.

(*
  budgets are defined for each dataset.
*)
Definition budget := list (nat * dp_param).

(* We assume there is a well-defined mechanism for doing this. *)
Definition calculate_budget (ε1 ε2: budget): budget. Admitted.

(* Note that these operators are not designed to be exhaustive. *)
(* Logical connections. *)
Inductive LogOp: Type := And | Or.
(* Comparison operators. *)
Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.
(* Some example binary arithmetic operators. *)
Inductive BinOp: Type := Add | Sub | Mul | Div | Mod | Concat.
(* Some example unary arithmetic operators. *)
Inductive UnOp: Type :=
  | Identity
  | Redact: nat → UnOp
  | Ascii
  | Strlen
  | Lower
  | Upper
.

Inductive TransOp: Type :=
  | unary_trans_op: UnOp → TransOp
  | binary_trans_op: BinOp → TransOp
.

Inductive AggOp: Type := Max | Min | Sum | Avg | Count.
Inductive NoiseOp: Type :=
  | differential_privacy: dp_param → NoiseOp
.

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

Lemma type_matches_eq: ∀ t1 t2, type_matches t1 t2 = true ↔ t1 = t2.
Proof.
  intros.
  split.
  - destruct t1, t2; simpl; intros; try discriminate; auto.
  - intros. subst. destruct t2; auto.
Qed.

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

Inductive aggregate_func (bt: basic_type): Set.
Inductive simple_aggregate_func: Set.
Inductive func: Set :=
  | transform: ∀ bt, transform_func bt → func
  | aggregate: ∀ bt, aggregate_func bt → func
.

Definition func_list: Set := list func%type.

Inductive unary_func :=
  | unary_function: ∀ ty, (type_to_coq_type ty → type_to_coq_type ty) → unary_func
.

Inductive binary_func :=
  | binary_function: ∀ty, (type_to_coq_type ty → type_to_coq_type ty → type_to_coq_type ty) → binary_func
.

Definition get_unary_type (f: unary_func): basic_type :=
  match f with
  | unary_function ty _ => ty
  end.

Definition get_binary_type (f: binary_func): basic_type :=
  match f with
  | binary_function ty _ => ty
  end.

(*
  A distinction is made between the database schema, which specifies the structure
  of the database, and the database instance, which specifies its actual content:
  sets of tuples.
*)

(* A schema is a list of attributes. *)
Definition schema: Type := (list Attribute).
Definition schema_no_name := (list basic_type).

(* Transforms a schema into a list of pure basic types. *)
Fixpoint schema_to_no_name (s: schema): schema_no_name :=
  match s with
  | nil => nil
  | (t, _) :: s' => t :: schema_to_no_name s'
  end.
Notation "'♭' s" := (schema_to_no_name s) (at level 60).

(* Converts a list of numbers into a list of strings. *)

Lemma schema_to_no_name_length: ∀ s,
  List.length (♭ s) = List.length s.
Proof.
  induction s.
  - auto.
  - simpl. destruct a. rewrite <- IHs. auto.
Qed.

Lemma unop_dec: ∀ (op1 op2: UnOp), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (destruct (eq_nat_dec n n0)); try (right; discriminate); try (left; congruence).
  right. unfold not in *. intros. inversion H. exfalso. auto.
Qed.

Lemma binop_dec: ∀ (op1 op2: BinOp), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (right; discriminate); try (left; congruence).
Qed.

Lemma transop_dec: ∀ (op1 op2: TransOp), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (destruct (unop_dec u u0)); try (destruct (binop_dec b b0));
  try (right; discriminate); try (left; congruence);
  unfold not in *; right; intros; apply n; inversion H; auto.
Qed.

Lemma aggop_dec: ∀ (op1 op2: AggOp), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (right; discriminate); try (left; congruence).
Qed.
