Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import policy.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Lia.

(* A setoid is a set (X, ~) with an equivalence relation. *)
(* We can derive three properties from an equivalence class:
  1. Reflexivity.
  2. Symmetry.
  3. Transitivity.
*)
Require Import SetoidClass.
Require Import RelationClasses.

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

(* Attributes are themselves string representation of the name. *)
Definition Attribute := (basic_type * string)%type.
Definition Symbol := string.
Definition Aggregate := string.

Inductive transform_func : Set.
Inductive aggregate_func : Set.
Inductive func: Set :=
  | transform: transform_func -> func
  | aggregate: aggregate_func -> func
.
Definition func_list: Set := list func%type.

Module Cell.

(* A cell that does not carry policies. *)
Definition clean_cell: Set := basic_type % type.
(* A cell that carries policies . *)
Definition cell: Set := (clean_cell * policy) % type.
Definition cell_denote (c: cell): Set := (type_to_coq_type (fst c) * policy) % type.

(* Cast the type of the cell, if needed. *)

End Cell.

Module Schema.

(* A distinction is made between the database schema, which specifies the structure
of the database, and the database instance, which specifies its actual content:
sets of tuples. *)

(* A schema is a list of attributes. *)
Definition schema: Set := (list Attribute)%type.

End Schema.

Module Tuple.

(* A tuple is a list of cells of different values. *)
Definition tuple_type: Set := (list Cell.cell)%type.

(* A tuple is, in essence, an interpretation of abstract values to their
concrete values. Thus it is a dependent type of `tuple_type`. We also
make it a recursive type, so that we can build types of arbitrary length. *)
Fixpoint tuple (ty: tuple_type): Set :=
  match ty with
  | nil => unit
  | (bt, _) :: t' => (type_to_coq_type bt * policy) * tuple t'
  end%type.

Definition example_tuple_ty : tuple_type := (StringType, policy_bot) :: (BoolType, policy_bot) :: nil.
Definition example_tuple: tuple example_tuple_ty := (("abcd"%string, policy_bot), ((true, policy_bot), tt)).
Definition example_tuple_ty' : tuple_type := (IntegerType, policy_bot) :: nil.
Definition example_tuple' : tuple example_tuple_ty' := ((1, policy_bot), tt).
Definition example_tuple'' : tuple (example_tuple_ty' ++ example_tuple_ty) := 
  ((1, policy_bot),
    (("abcd"%string, policy_bot),
      ((true, policy_bot),
        tt))).

(* Cast the type of the tuple, if needed. *)
Lemma tuple_cast: forall (ty1 ty2: tuple_type) (f: tuple_type -> Set),
  f ty1 -> ty1 = ty2 -> f ty2.
Proof.
  intros.
  rewrite H0 in H.
  auto. 
Qed.

(* A tuple type is a list of basic types. *)
Fixpoint tuple_type_eq (ty1 ty2: tuple_type) : bool :=
  match ty1, ty2 with
    | nil, nil => true
    | (bt1, _) :: t1', (bt2, _) :: t2' => andb (type_matches bt1 bt2) (tuple_type_eq t1' t2')
    | _, _ => false
  end.

(* Useful for joining two databases tuple-wise. *)
Definition tuple_concat (ty1 ty2: tuple_type)
  (lhs: tuple ty1) (rhs: tuple ty2): tuple (ty1 ++ ty2).
Proof.
  intros.
  induction ty1; auto.
    (* Just use existing component to construct the given type. *)
    simpl in *. destruct a; destruct lhs; constructor; auto.
Defined.

(* A tuple must equal *)
Fixpoint tuple_eq (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return (forall (lhs rhs: tuple ty), Prop) with
    | nil => fun _ _ => True
    | (h, p) :: tl => fun lhs rhs => 
      (fst lhs) = (fst rhs) /\ (snd lhs) = (snd rhs) /\ tuple_eq tl (snd lhs) (snd rhs)
  end. 

Definition tuple_eq_eqv (ty: tuple_type): Equivalence (tuple_eq ty).
Proof.
  (* Note that `Equivalence` is a class. *)
  split. 
  - induction ty; simpl; auto.
    destruct a. destruct c; simpl in *; auto.
  - induction ty; simpl; auto. destruct a.
    destruct c; simpl; split; destruct H; try rewrite H; intuition.
  - unfold Transitive. intros. induction ty.
    + auto.
    + destruct a. destruct c;
      simpl in *; intuition; try rewrite H1; try rewrite H; try rewrite H0; try rewrite H4; auto.
Qed.

Definition nth: forall (ty: tuple_type) (n: nat) (extract: n < length ty), Cell.cell.
refine
(fix nth' (ty: tuple_type) (n: nat):
  n < length ty -> Cell.cell :=
     match ty as ty' , n as n' return ty = ty' -> n = n' -> n' < length ty' -> Cell.cell with
      | x :: y , 0 => fun _ _ _ => x
      | x :: y , S n' => fun _ _ _ => nth' y n' _
      | _ , _ => fun _ _ _ => False_rec _ _
    end (refl_equal _) (refl_equal _)).
Proof.
  - simpl in *. lia.
  - simpl in *. lia.
Defined.

Definition nth_col_tuple:
  forall (ty: tuple_type) (n : nat), forall (extract: n < length ty),
    tuple ty -> tuple ((nth ty n extract) :: nil).
refine (
  fix nth_col_tuple' (ty: tuple_type) (n : nat):
    forall (extract: n < length ty), tuple ty -> tuple ((nth ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple ((nth ty' n' extract) :: nil) with
        | (bt, p) :: l', 0 => fun _ _ _ t => ((fst t), tt)
        | (bt, p) :: l', S n' => fun _ _ _ t => nth_col_tuple' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. lia.
Defined.

Definition tuple_is_setoid (ty: tuple_type): Setoid (tuple ty).
Proof.
  exists (tuple_eq ty).
  apply tuple_eq_eqv.
Qed.

Definition example_tuple_lhs : tuple example_tuple_ty := (("abcd"%string, policy_bot), ((true, policy_bot), tt)).
Definition example_tuple_rhs : tuple example_tuple_ty := (("abcd"%string, policy_bot), ((true, policy_bot), tt)).

Example example_tuple_eq: tuple_eq example_tuple_ty example_tuple_lhs example_tuple_lhs.
Proof.
  simpl. repeat split.
Qed.

End Tuple.

Module Formula.

Inductive atomic_expression (t: Tuple.tuple_type) : Cell.cell -> Set :=
  (* v *)
  | atomic_expression_const:
      forall (c: Cell.cell) (c': type_to_coq_type (fst c)), atomic_expression t c
  (* a *)
  | atomic_column:
      forall (n: nat) (extract: n < length t), atomic_expression t (Tuple.nth t n extract)
.

Inductive predicate (t: Tuple.tuple_type) (c: Cell.cell): Type :=
  | predicate_true: predicate t c
  | predicate_false: predicate t c
  | predicate_expression: atomic_expression t c -> predicate t c
  | predicate_com: ComOp -> predicate t c -> predicate t c -> predicate t c
  | predicate_not: predicate t c -> predicate t c
.

Inductive formula (t: Tuple.tuple_type): Type :=
  | formula_con: LogOp -> formula t -> formula t -> formula t
  | formula_predicate: forall c, predicate t c -> formula t
.

End Formula.
