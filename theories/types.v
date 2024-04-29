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

(* Basic types in our column types. *)
Inductive basic_type: Set :=
  | IntegerType
  | BoolType
  | StringType
  .

Definition type_to_coq_type (t: basic_type): Set :=
  match t with
  | IntegerType => nat
  | BoolType => bool
  | StringType => string
  end.


(*
  By its design, privacy budget should be real numbers, but this would introduce undue
  burden for formal verification that we are not prepared to handle. As ℕ is equinume-
  rous to ℚ (in fact, it can be made universal model of computation), we use ℕ to repre-
  sent the real numbers, and this is indeed without loss of generality.
*)
Definition dp_param := (nat * nat)%type.

Definition budget := nat%type.

(* We assume there is a well-defined mechanism for doing this. *)
Definition calculate_budget (ε1 ε2: budget): budget. Admitted.

(* Note that these operators are not designed to be exhaustive. *)
(* Logical connections. *)
Inductive log_op: Type := And | Or.
(* Comparison operators. *)
Inductive com_op: Type := Gt | Lt | Ge | Le | Eq | Neq.
(* Some example binary arithmetic operators. *)
Inductive bin_arith_op: Type := Add | Sub | Mul | Div | Mod | Concat.
(* Some example unary arithmetic operators. *)
Inductive un_op: Type :=
  | Identity
  | Redact: nat → un_op
  | Ascii
  | Strlen
  | Lower
  | Upper
  | Not
.

Inductive bin_op: Type :=
  | Logical: log_op → bin_op
  | Comparison: com_op → bin_op
  | Arithmetic: bin_arith_op → bin_op
.

Inductive trans_op: Type :=
  | UnaryTransOp: un_op → trans_op
  | BinaryTransOp: ∀ bt, bin_op → type_to_coq_type bt → trans_op
  | OtherTransOp: trans_op
.

Inductive agg_op: Type := Max | Min | Sum | Avg | Count.
Inductive noise_op: Type :=
  | differential_privacy: dp_param → noise_op
.

(*
  For brevity, we assume that the noise generator for ensuring privacy is an "oracle" in a sense that
  for any given DP param it always generates a noise value. Verifying differential privacy is a separate
  concern and is not addressed here.
 *)
Inductive noise_gen: Type :=
  (* The constructor which takes a certain value of DP requirement and the raw value.  *)
  | NoiseGen: dp_param → (∀ (A: Type), A → A) → noise_gen
.

Lemma basic_type_eq_dec: ∀ (t1 t2: basic_type), {t1 = t2} + {t1 ≠ t2}.
Proof.
  intros.
  destruct t1, t2; try (right; discriminate); try (left; congruence).
Qed.

Definition log_op_eqb op1 op2: bool :=
  match op1, op2 with
  | And, And => true
  | Or, Or => true
  | _, _ => false
  end.

Definition com_op_eqb op1 op2: bool :=
  match op1, op2 with
  | Gt, Gt => true
  | Lt, Lt => true
  | Ge, Ge => true
  | Le, Le => true
  | Eq, Eq => true
  | Neq, Neq => true
  | _, _ => false
  end.

Definition bin_arith_op_eqb op1 op2: bool :=
  match op1, op2 with
  | Add, Add => true
  | Sub, Sub => true
  | Mul, Mul => true
  | Div, Div => true
  | Mod, Mod => true
  | Concat, Concat => true
  | _, _ => false
  end.


Definition un_op_eqb op1 op2: bool :=
  match op1, op2 with
  | Identity, Identity => true
  | Redact n1, Redact n2 => n1 =? n2
  | Ascii, Ascii => true
  | Strlen, Strlen => true
  | Lower, Lower => true
  | Upper, Upper => true
  | Not, Not => true
  | _, _ => false
  end.

Definition bin_op_eqb op1 op2: bool :=
  match op1, op2 with
  | Logical l1, Logical l2 => log_op_eqb l1 l2
  | Comparison c1, Comparison c2 => com_op_eqb c1 c2
  | Arithmetic a1, Arithmetic a2 => bin_arith_op_eqb a1 a2
  | _, _ => false
  end.

Definition agg_op_eqb op1 op2: bool :=
  match op1, op2 with
  | Max, Max => true
  | Min, Min => true
  | Sum, Sum => true
  | Avg, Avg => true
  | Count, Count => true
  | _, _ => false
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

Definition trans_op_eqb (op1 op2: trans_op): bool.
  refine (match op1, op2 with
  | UnaryTransOp op1, UnaryTransOp op2 => un_op_eqb op1 op2
  | BinaryTransOp bt1 v1 op1, BinaryTransOp bt2 v2 op2 => _
  | OtherTransOp, OtherTransOp => true
  | _, _ => false
  end).
  destruct (basic_type_eq_dec bt1 bt2).
  - destruct (bin_op_eqb v1 v2).
    + subst. destruct bt2; simpl in *.
      * destruct (Nat.eqb op1 op2).
        -- exact true.
        -- exact false.
      * destruct (Bool.eqb op1 op2).
        -- exact true.
        -- exact false.
      * destruct (String.eqb op1 op2).
        -- exact true.
        -- exact false.
    + exact false.
  - destruct (try_cast bt1 bt2 op1).
    + rename op2 into lhs. rename t into rhs. destruct bt2; simpl in *.
      * destruct (Nat.eqb lhs rhs).
        -- exact true.
        -- exact false.
      * destruct (Bool.eqb lhs rhs).
        -- exact true.
        -- exact false.
      * destruct (String.eqb lhs rhs).
        -- exact true.
        -- exact false.
    + exact false.
Defined.

Definition noise_op_eqb op1 op2: bool :=
  match op1, op2 with
  | differential_privacy (ε1, δ1), differential_privacy (ε2, δ2) => (ε1 =? ε2) && (δ1 =? δ2)
  end.

Definition type_matches (lhs rhs: basic_type): bool :=
  match lhs, rhs with
  | IntegerType, IntegerType => true
  | BoolType, BoolType => true
  | StringType, StringType => true
  | _, _ => false
  end.


Definition type_coerce (t1 t2: basic_type): basic_type :=
  match t1, t2 with
  | IntegerType, IntegerType => IntegerType
  | IntegerType, StringType => StringType
  | IntegerType, BoolType => IntegerType
  | BoolType, BoolType => BoolType
  | BoolType, IntegerType => IntegerType
  | BoolType, StringType => StringType
  | StringType, StringType => StringType
  | StringType, IntegerType => StringType
  | StringType, BoolType => StringType
  end.

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
Definition attribute := (basic_type * nat)%type.

Lemma attribute_eq_dec: ∀ (a1 a2: attribute), {a1 = a2} + {a1 ≠ a2}.
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
  (* un_op is the "sort" signature of the function because function itself is opaque. *)
  | UnaryFunc: un_op → ∀ ty1 ty2, (type_to_coq_type ty1 → type_to_coq_type ty2) → unary_func
.

Inductive binary_func :=
  (* bin_op is the "sort" signature of the function because function itself is opaque. *)
  | BinFunc: bin_op → ∀ ty1 ty2 ty3,
      (type_to_coq_type ty1 → type_to_coq_type ty2 → type_to_coq_type ty3) → binary_func
.

Inductive agg_func :=
  (* agg_op is the "sort" signature of the function because function itself is opaque. *)
  (*
    agg := op × (τ2 → τ1 → τ2) → τ2 → 𝒩
                 ^^^^^^^^^^^^    ^^
                   folder      initial value
    where
      τ1 is the type of the input column.
      τ2 is the type of the output value.
  *)
  | AggFunc: agg_op → ∀ ty1 ty2,
      (type_to_coq_type ty2 → type_to_coq_type ty1 → type_to_coq_type ty2)
        → type_to_coq_type ty2 → option noise_gen → agg_func
.

Definition agg_with_noise f: Prop :=
  match f with
  | AggFunc _ _ _ _ _ n =>
    match n with
    | Some _ => True
    | None => False
    end
  end.

(*
  A distinction is made between the database schema, which specifies the structure
  of the database, and the database instance, which specifies its actual content:
  sets of tuples.
*)

(* A schema is a list of attributes. *)
Definition schema: Type := (list attribute).
Definition schema_no_name := (list basic_type).

(* Transforms a schema into a list of pure basic types. *)
Fixpoint schema_to_no_name (s: schema): schema_no_name :=
  match s with
  | nil => nil
  | (t, _) :: s' => t :: schema_to_no_name s'
  end.
Notation "'♭' s" := (schema_to_no_name s) (at level 60).

(* Converts a list of numbers into a list of strings. *)

Section Facts.

Lemma schema_to_no_name_length: ∀ s,
  List.length (♭ s) = List.length s.
Proof.
  induction s.
  - auto.
  - simpl. destruct a. rewrite <- IHs. auto.
Qed.

Lemma unop_dec: ∀ (op1 op2: un_op), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (destruct (eq_nat_dec n n0)); try (right; discriminate); try (left; congruence).
  right. unfold not in *. intros. inversion H. exfalso. auto.
Qed.

Lemma binop_dec: ∀ (op1 op2: bin_op), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (right; discriminate); try (left; congruence).
  - destruct l, l0; try (right; discriminate); try (left; congruence).
  - destruct c, c0; try (right; discriminate); try (left; congruence).
  - destruct b, b0; try (right; discriminate); try (left; congruence).
Qed.

Lemma transop_dec: ∀ (op1 op2: trans_op), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (destruct (unop_dec u u0)); try (destruct (binop_dec b b0));
  try (right; discriminate); try (left; congruence).
  unfold not in *; right; subst.
Admitted.

Lemma aggop_dec: ∀ (op1 op2: agg_op), {op1 = op2} + {op1 ≠ op2}.
Proof.
  intros.
  destruct op1, op2; try (right; discriminate); try (left; congruence).
Qed.

Lemma un_op_eq_eqb: ∀ op1 op2, un_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto.
  - f_equal. apply Nat.eqb_eq in H. auto.
  - inversion H. apply Nat.eqb_refl.
Qed.

Lemma log_op_eq_eqb: ∀ op1 op2, log_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto.
Qed.

Lemma com_op_eq_eqb: ∀ op1 op2, com_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto.
Qed.

Lemma bin_arith_op_eq_eqb: ∀ op1 op2, bin_arith_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto.
Qed.

Lemma bin_op_eq_eqb: ∀ op1 op2, bin_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto.
  - f_equal. apply log_op_eq_eqb. auto.
  - apply log_op_eq_eqb. inversion H. auto.
  - f_equal. apply com_op_eq_eqb. auto.
  - apply com_op_eq_eqb. inversion H. auto.
  - f_equal. apply bin_arith_op_eq_eqb. auto.
  - apply bin_arith_op_eq_eqb. inversion H. auto.
Qed.

Lemma agg_op_eq_eqb: ∀ op1 op2, agg_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto.
Qed.

Lemma noise_op_eq_eqb: ∀ op1 op2, noise_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto; destruct d; destruct d0.
  - apply andb_true_iff in H. destruct H. apply Nat.eqb_eq in H. apply Nat.eqb_eq in H0. auto. subst. auto.
  - apply andb_true_iff. split; apply Nat.eqb_eq; inversion H; auto.
Qed.

Lemma trans_op_eq_eqb: ∀ op1 op2, trans_op_eqb op1 op2 = true ↔ op1 = op2.
Proof.
  (* intros.
  destruct op1, op2; simpl; split; intros; try discriminate; auto;
  inversion H;
  try solve [apply un_op_eq_eqb in H; subst; simpl; auto | apply bin_op_eq_eqb in H; subst; auto].
  - destruct u0; simpl; auto. apply Nat.eqb_refl.
  - destruct b0; simpl; auto.
    + apply log_op_eq_eqb. auto.
    + apply com_op_eq_eqb. auto.
    + apply bin_arith_op_eq_eqb. auto. *)
Admitted.

Lemma type_matches_eq: ∀ t1 t2, type_matches t1 t2 = true ↔ t1 = t2.
Proof.
  intros.
  split.
  - destruct t1, t2; simpl; intros; try discriminate; auto.
  - intros. subst. destruct t2; auto.
Qed.

Lemma trans_op_eq_dec: ∀ (op1 op2: trans_op),
  {op1 = op2} + {op1 ≠ op2}.
Proof.
  destruct op1; destruct op2;
  try (destruct u, u0); try (destruct b, b0);
  try (destruct (Nat.eq_dec n n0));
  try (destruct l, l0);
  try (destruct c, c0);
  try (destruct b, b0);
  try solve [(left; simpl; subst; auto) | (right; red; simpl; intros; discriminate)].
  right. unfold not in *. intros. apply n1.
  inversion H. reflexivity.
Admitted.

Lemma agg_op_eq_dec: ∀ (op1 op2: agg_op),
  {op1 = op2} + {op1 ≠ op2}.
Proof.
  destruct op1; destruct op2;
  solve [(left; simpl; subst; auto) | (right; red; simpl; intros; discriminate)].
Admitted.

End Facts.
