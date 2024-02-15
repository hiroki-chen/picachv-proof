(* TODO: Make cells identifiable with some id. *)
Require Import Ascii.
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

Definition digit_to_string (n: nat): string :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

(* This function is not "syntactically" terminating. We prove this later using `Program Fixpoint`. *)
Program Fixpoint nat_to_string (n: nat) {measure n}: string :=
  (match (n <? 10)%nat as x return (n <? 10)%nat = x → string with
     | true => fun _ => digit_to_string n
     | false => fun pf =>
                  let m := Nat.div n 10 in
                    append (nat_to_string m) (digit_to_string (n - 10 * m))
   end eq_refl).
Next Obligation.
  apply (Nat.div_lt n 10%nat).
  destruct n. unfold Nat.ltb in *. simpl in *.
  discriminate. auto with arith.
  auto with arith.
Defined.

Definition nat_of_string (s: string) : nat :=
  let fix aux acc s :=
      match s with
      | String "0" rst => aux (10 * acc) rst
      | String "1" rst => aux (1 + 10 * acc) rst
      | String "2" rst => aux (2 + 10 * acc) rst
      | String "3" rst => aux (3 + 10 * acc) rst
      | String "4" rst => aux (4 + 10 * acc) rst
      | String "5" rst => aux (5 + 10 * acc) rst
      | String "6" rst => aux (6 + 10 * acc) rst
      | String "7" rst => aux (7 + 10 * acc) rst
      | String "8" rst => aux (8 + 10 * acc) rst
      | String "9" rst => aux (9 + 10 * acc) rst
      | _ => acc
      end
  in aux 0 s.

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
Inductive BinArithOp: Type := Add | Sub | Mul | Div | Mod | Concat.
(* Some example unary arithmetic operators. *)
Inductive UnOp: Type :=
  | Identity
  | Redact: nat → UnOp
  | Ascii
  | Strlen
  | Lower
  | Upper
  | Not
.

Inductive BinOp: Type :=
  | Logical: LogOp → BinOp
  | Comparison: ComOp → BinOp
  | Arithmetic: BinArithOp → BinOp
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
  | StringType
  .

(*
  For brevity, we assume that the noise generator for ensuring privacy is an "oracle" in a sense that
  for any given budget it always generates a noise value. Verifying differential privacy is a separate
  concern and is not addressed here.
 *)
Inductive noise_gen: Type :=
  (* The constructor which takes a certain value of budget and the raw value.  *)
  | noise: ∀ (A: Type), budget → A → A → noise_gen
.

Lemma basic_type_eq_dec: ∀ (t1 t2: basic_type), {t1 = t2} + {t1 ≠ t2}.
Proof.
  intros.
  destruct t1, t2; try (right; discriminate); try (left; congruence).
Qed.

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

(* Try to cast between types. *)
Definition try_cast (t1 t2: basic_type): type_to_coq_type t1 → option (type_to_coq_type t2) :=
  match t1 as t1', t2 as t2'
    return t1 = t1' → t2 = t2' → type_to_coq_type t1' → option (type_to_coq_type t2') with
  | IntegerType, IntegerType => fun _ _ x => Some x
  | IntegerType, StringType => fun _ _ x => Some (nat_to_string x)
  | IntegerType, BoolType => fun _ _ x => if (x =? 0)%nat then Some false else Some true
  | BoolType, BoolType => fun _ _ x => Some x
  | BoolType, IntegerType => fun _ _ x => if x then Some 1 else Some 0
  | BoolType, StringType => fun _ _ x => if x then (Some "true"%string) else (Some "false"%string)
  | StringType, StringType => fun _ _ x => Some x
  | StringType, IntegerType => fun _ _ x => Some (nat_of_string x)
  (* Meaningless. *)
  | StringType, BoolType => fun _ _ _ => None
  end eq_refl eq_refl.

Definition value_eq (t1 t2: basic_type) (v1: type_to_coq_type t1) (v2: type_to_coq_type t2) : bool :=
  match t1, t2 return type_to_coq_type t1 → type_to_coq_type t2 → bool with
  | IntegerType, IntegerType => Nat.eqb
  | BoolType, BoolType => Bool.eqb
  | StringType, StringType => String.eqb
  | _, _ => λ _ _, false
  end v1 v2.

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

(*
  Attributes consist of a type and their unique identifiers.

  We avoid using strings as identifiers because they are:
  1. Not generic enough.
  2. May be duplicate (in the sense of string equality) and we want to avoid that.
*)
Definition Attribute := (basic_type * nat)%type.

Lemma attribute_eq_dec: ∀ (a1 a2: Attribute), {a1 = a2} + {a1 ≠ a2}.
Proof.
  intros.
  destruct a1, a2.
  destruct (basic_type_eq_dec b b0).
  - destruct (eq_dec n n0).
    + left. subst. auto.
    + right. unfold not. intros. inversion H. auto.
  - right. unfold not. intros. inversion H. auto.
Qed.

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
  (* UnOp is the "sort" signature of the function because function itself is opaque. *)
  | unary_function: UnOp → ∀ ty, (type_to_coq_type ty → type_to_coq_type ty) → unary_func
.

Inductive binary_func :=
  (* BinOp is the "sort" signature of the function because function itself is opaque. *)
  | binary_function: BinOp → ∀ ty,
      (type_to_coq_type ty → type_to_coq_type ty → type_to_coq_type ty) → binary_func
.

Inductive agg_func :=
  (* AggOp is the "sort" signature of the function because function itself is opaque. *)
  | aggregate_function: AggOp → ∀ ty1 ty2,
      (type_to_coq_type ty1 → type_to_coq_type ty2 → type_to_coq_type ty1) → agg_func
.

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
  - destruct l, l0; try (right; discriminate); try (left; congruence).
  - destruct c, c0; try (right; discriminate); try (left; congruence).
  - destruct b, b0; try (right; discriminate); try (left; congruence).
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
