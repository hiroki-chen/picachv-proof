Require Import List.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import ordering.
Require Import types.

Inductive atomic_expression (ty: Tuple.tuple_type) : basic_type → Set :=
  (* v *)
  | atomic_expression_const:
      ∀ bt (c: type_to_coq_type bt), atomic_expression ty bt
  (* a *)
  | atomic_expression_column:
      ∀ n (extract: n < length ty), atomic_expression ty (Tuple.nth_np ty n extract)
  (* f(list e) *)
  | atomic_expression_func:
      ∀ bt (c: type_to_coq_type bt),
        transform_func bt → list (atomic_expression ty bt) → atomic_expression ty bt
.

Inductive agg_expression (ty: Tuple.tuple_type) (bt: basic_type): Set :=
  (* e *)
  | agg_atomic_expression: atomic_expression ty bt → agg_expression ty bt
  (* agg(e) *)
  | agg_aggregate: aggregate_func bt → atomic_expression ty bt → agg_expression ty bt
  (* f(A) *)
  | agg_function: transform_func bt → list (agg_expression ty bt)  → agg_expression ty bt
.

Inductive simple_atomic_expression: Set :=
  (* v *)
  | simple_atomic_expression_const:
      ∀ (bt: basic_type), type_to_coq_type bt → simple_atomic_expression
  (* a *)
  | simple_atomic_expression_column:
      ∀ (n: nat), simple_atomic_expression
  (*
    Without loss of generality, we assume functions only take either:
    1. One argument, or
    2. Two arguments.

    This is because we can always transform a function with more than two arguments
    into a function with two arguments by *currying*.

    For example, we can transform `f(a, b, c)` into `f'(a, f''(b, c))`, although we
    do not actually do this in the code; we assume someone else has done this for us.

    The reason why we do not curry binary functions is because we do not want to check
    if `op` is consistent with the number of arguments; this would incur a lot of undue
    complexity.
  *)
  | simple_atomic_expression_func_unary:
      UnOp → simple_atomic_expression → simple_atomic_expression
  | simple_atomic_expression_func_binary:
      BinOp → simple_atomic_expression → simple_atomic_expression → simple_atomic_expression
  .

Definition stf_id := simple_atomic_expression_func_unary Identity.
Definition simple_agg_expression := (AggOp * nat)%type.
Inductive predicate (ty: Tuple.tuple_type) (bt: basic_type): Type :=
  | predicate_true: predicate ty bt
  | predicate_false: predicate ty bt
  | predicate_com: ComOp → agg_expression ty bt → agg_expression ty bt→ predicate ty bt
  | predicate_not: predicate ty bt → predicate ty bt
.

Inductive simple_predicate: Set :=
  | simple_predicate_true: simple_predicate
  | simple_predicate_false: simple_predicate
  (* cell ? basic_type *)
  | simple_predicate_com: ComOp → simple_atomic_expression → simple_atomic_expression → simple_predicate
  | simple_predicate_not: simple_predicate → simple_predicate
.

Inductive formula (ty: Tuple.tuple_type) :=
  | formula_con: LogOp → formula ty → formula ty → formula ty
  | formula_predicate: ∀ bt, predicate ty bt → formula ty
.

Inductive simple_formula :=
  | simple_formula_con: LogOp → simple_formula → simple_formula → simple_formula
  | simple_formula_predicate: simple_predicate → simple_formula
.

Definition atomic_expression_denote (ty: Tuple.tuple_type) (t: basic_type) (a: atomic_expression ty t):
  Tuple.tuple ty → type_to_coq_type t.
Proof.
  refine (
    match a in atomic_expression _ t' return Tuple.tuple ty → type_to_coq_type t' with
      | atomic_expression_const _ _ v => fun _ => v
      | atomic_expression_column _ _ v  => fun x => _
      | atomic_expression_func _ _ _ f args => fun x => _
    end
  ).
  pose (Tuple.nth_col_tuple_np ty n v x).
  simpl in t0.
  exact (fst t0).
  exact t0.
Defined.

Fixpoint agg_denote (ty: Tuple.tuple_type) (t: basic_type) (a: agg_expression ty t):
  Tuple.tuple ty → type_to_coq_type t.
Proof.
  refine (
    match a in agg_expression _ _ return Tuple.tuple ty → type_to_coq_type _ with
      | agg_atomic_expression _ _ a => fun x => atomic_expression_denote ty t a x
      | agg_aggregate _ _ f a => fun x => _
      | agg_function _ _ f args => fun x => _
    end
  ).
  - exact (atomic_expression_denote ty t a x).
  - apply (List.map (fun arg => agg_denote ty t arg x)) in args.
    induction args.
    (* Should never happen? *)
    + destruct t.
      * simpl. exact 0.
      * simpl. exact false.
      * simpl. exact String.EmptyString.
    + exact IHargs.
Defined.

Fixpoint predicate_denote (bt: basic_type) (ty: Tuple.tuple_type) (p: predicate ty bt):
  Tuple.tuple ty → bool.
  intros. destruct p as [ | |op lhs rhs| ].
  - exact true.
  - exact false.
  - rename H into tp. destruct op.
  (* Determined by the operator type. *)
  (* Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.*)
  (* We are actually doing a match between `lt lhs rhs` and `com_op`. *)
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact false.
      * exact false.
      * exact true.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact true.
      * exact false.
      * exact false.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact false.
      * exact true.
      * exact true.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact true.
      * exact true.
      * exact false.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact false.
      * exact true.
      * exact false.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact true.
      * exact false.
      * exact true.
  - rename H into tp. exact (negb (predicate_denote bt ty p tp)).
Defined.
(* 
Fixpoint simple_predicate_denote (bt: basic_type) (p: simple_predicate bt): type_to_coq_type bt → bool.
  intros. destruct p.
  - exact true.
  - exact false.
  (* Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.*)
  - destruct c. destruct (cmp lhs rhs).
      * exact false.
      * exact false.
      * exact true.

      * exact true.
      * exact false.
      * exact false.

      * exact false.
      * exact true.
      * exact true.

      * exact true.
      * exact true.
      * exact false.

      * exact false.
      * exact true.
      * exact false.

      * exact true.
      * exact false.
      * exact true.
  - exact (negb (simple_predicate_denote bt p H)).
Defined. *)

Fixpoint formula_denote (ty: Tuple.tuple_type) (f: formula ty) {struct f}: Tuple.tuple ty → bool :=
match f with
  | formula_predicate _ c pred => predicate_denote c ty pred
  | formula_con _ op lhs rhs =>
    match op with
      | And => fun t => andb (formula_denote ty lhs t) (formula_denote ty rhs t)
      | Or => fun t => orb (formula_denote ty lhs t) (formula_denote ty rhs t)
    end
end.

Fixpoint bounded_list' (l: list simple_atomic_expression) (ty: Tuple.tuple_type) : Prop :=
  match l with
    | h :: t => match h with
                  | simple_atomic_expression_column n => n < List.length ty
                  | _ => True
                end ∧ bounded_list' t ty
    | _ => False
  end.

Require Import String.
Require Import List.
Require Import Lia.
(* Some tests. *)
Example example_formula: formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty BoolType (predicate_true Tuple.example_tuple_ty BoolType)).
Example example_formula': formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty IntegerType
      (predicate_com Tuple.example_tuple_ty IntegerType Eq
        (agg_atomic_expression Tuple.example_tuple_ty IntegerType
          (atomic_expression_const Tuple.example_tuple_ty IntegerType 1))
        (agg_atomic_expression Tuple.example_tuple_ty IntegerType
          (atomic_expression_const Tuple.example_tuple_ty IntegerType 1))
      )
    ).

Example can_index: 0 < length Tuple.example_tuple_ty.
Proof.
  simpl. lia.
Qed.
Example example_formula'': formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty StringType
      (predicate_com Tuple.example_tuple_ty StringType Eq
        (agg_atomic_expression Tuple.example_tuple_ty StringType
          (atomic_expression_column Tuple.example_tuple_ty 0 can_index))
        (agg_atomic_expression Tuple.example_tuple_ty StringType
          (atomic_expression_const Tuple.example_tuple_ty StringType "233"%string))
      )
    ).

(* fun _ : Tuple.tuple Tuple.example_tuple_ty => true *)
Compute ((formula_denote Tuple.example_tuple_ty example_formula) Tuple.example_tuple_lhs).
(* fun _ : Tuple.tuple Tuple.example_tuple_ty => false *)
Definition foo: bool := ((formula_denote Tuple.example_tuple_ty example_formula') Tuple.example_tuple_lhs).
Lemma foo_is_true: foo = true.
Proof.
  unfold foo.
  simpl.
  destruct (cmp 1 1).
  - apply order_is_irreflexive in l. contradiction.
  - destruct (nat_dec 1 1).
    destruct s. inversion l. inversion H0.
    reflexivity. inversion l.
    inversion H0.
  - apply order_is_irreflexive in l. contradiction.
Qed.

Definition foo': bool := ((formula_denote Tuple.example_tuple_ty example_formula'') Tuple.example_tuple_lhs).
Lemma foo'_is_false: foo' = false.
Proof.
  unfold foo'.
  simpl.
  destruct (nat_dec _ _).
  destruct s.
  - reflexivity.
  - inversion e.
  - reflexivity.
Qed.
