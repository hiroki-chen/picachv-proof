Set Printing All.

Require Import String.
Require Import List.
Require Import Bool.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Lia.
Require Import Decidable.

Require Import ordering.
Require Import policy.

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
Instance can_order (t: basic_type): Ordered (type_to_coq_type t).
Admitted.

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

Definition cell_inject_policy (c: clean_cell) (p: policy): cell := (c, p).

End Cell.

Module Schema.

(*
  A distinction is made between the database schema, which specifies the structure
  of the database, and the database instance, which specifies its actual content:
  sets of tuples.
*)

(* A schema is a list of attributes. *)
Definition schema: Set := (list Attribute)%type.

End Schema.

Module Tuple.

(* A tuple is a list of cells of different values. *)
Definition tuple_type: Set := (list Cell.cell)%type.
Definition tuple_type_np: Set := (list Cell.clean_cell)%type.

(* A tuple is, in essence, an interpretation of abstract values to their
concrete values. Thus it is a dependent type of `tuple_type`. We also
make it a recursive type, so that we can build types of arbitrary length. *)
Fixpoint tuple (ty: tuple_type): Set :=
  match ty with
  | nil => unit
  | (bt, _) :: t' => (type_to_coq_type bt * policy) * tuple t'
  end%type.

Fixpoint tuple_np (ty: tuple_type_np): Set :=
  match ty with
    | nil => unit
    | bt :: t' => (type_to_coq_type bt) * tuple_np t'
  end%type.

(* todo. *)
Definition inject_policy (p: list policy) (ty: tuple_type_np) (length_match: length p = length ty): tuple_type.
Admitted.

(* Revoves policies. *)
Definition extract_types (ty: tuple_type): tuple_type_np.
Admitted.

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
Defined.

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
  
Definition nth_col_tuple: forall (ty: tuple_type) (n : nat) (extract: n < length ty), tuple ty -> tuple ((nth ty n extract) :: nil).
refine (
  fix nth_col_tuple' (ty: tuple_type) (n : nat): forall (extract: n < length ty),
    tuple ty -> tuple ((nth ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple ((nth ty' n' extract) :: nil) with
        | (bt, p) :: l', 0 => fun _ _ _ t => ((fst t), tt)
        | (bt, p) :: l', S n' => fun _ _ _ t => nth_col_tuple' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. lia.
Defined.

(* Without `policy` extracted! *)
Definition nth_np: forall (ty: tuple_type) (n: nat) (extract: n < length ty), basic_type.
  intros.
  exact (fst (nth ty n extract)).
Defined.

(* Without `policy` extracted! *)
Definition nth_col_tuple_np: forall (ty: tuple_type) (n : nat) (extract: n < length ty), tuple ty -> tuple_np ((nth_np ty n extract) :: nil).
refine (
  fix nth_col_tuple_np' (ty: tuple_type) (n : nat): forall (extract: n < length ty),
    tuple ty -> tuple_np ((nth_np ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple_np ((nth_np ty' n' extract) :: nil) with
        | (bt, p) :: l', 0 => fun _ _ _ t => ((fst (fst t)), tt)
        | (bt, p) :: l', S n' => fun _ _ _ t => nth_col_tuple_np' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
simpl in *. lia.
Defined.

Definition tuple_is_setoid (ty: tuple_type): Setoid (tuple ty).
Proof.
  exists (tuple_eq ty).
  apply tuple_eq_eqv.
Defined.

Definition example_tuple_lhs : tuple example_tuple_ty := (("abcd"%string, policy_bot), ((true, policy_bot), tt)).
Definition example_tuple_rhs : tuple example_tuple_ty := (("abcd"%string, policy_bot), ((true, policy_bot), tt)).

Example example_tuple_eq: tuple_eq example_tuple_ty example_tuple_lhs example_tuple_lhs.
Proof.
  simpl. repeat split.
Qed.

End Tuple.

Module Formula.

Inductive atomic_expression (ty: Tuple.tuple_type) : basic_type -> Set :=
  (* v *)
  | atomic_expression_const:
      forall bt (c : type_to_coq_type bt), atomic_expression ty bt
  (* a *)
  | atomic_expression_column:
      forall n (extract: n < length ty), atomic_expression ty (Tuple.nth_np ty n extract)
.

Inductive predicate (ty: Tuple.tuple_type) (t: basic_type): Type :=
  | predicate_true: predicate ty t
  | predicate_false: predicate ty t
  | predicate_com: ComOp -> atomic_expression ty t -> atomic_expression ty t -> predicate ty t
  | predicate_not: predicate ty t -> predicate ty t
.

Inductive formula (ty: Tuple.tuple_type) :=
  | formula_con: LogOp -> formula ty -> formula ty -> formula ty
  | formula_predicate: forall bt, predicate ty bt -> formula ty
.

Definition atomic_expression_denote (ty: Tuple.tuple_type) (t: basic_type) (a: atomic_expression ty t):
  Tuple.tuple ty -> type_to_coq_type t.
Proof.
  refine (
    match a in atomic_expression _ t' return Tuple.tuple ty -> type_to_coq_type t' with
      | atomic_expression_const _ _ v => fun _ => v
      | atomic_expression_column _ _ v  => fun x => _
    end
  ).
  pose (Tuple.nth_col_tuple_np ty n v x).
  simpl in t0.
  exact (fst t0).
Defined.

Fixpoint predicate_denote (bt: basic_type) (ty: Tuple.tuple_type) (p: predicate ty bt):
  Tuple.tuple ty -> bool.
  intros. destruct p as [ | |op lhs rhs| ].
  - exact true.
  - exact false.
  - rename H into tp. destruct op.
  (* Determined by the operator type. *)
  (* Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.*)
  (* We are actually doing a match between `lt lhs rhs` and `com_op`. *)
    + destruct (cmp (atomic_expression_denote ty bt lhs tp) (atomic_expression_denote ty bt rhs tp)).
      * exact false.
      * exact false.
      * exact true.
    + destruct (cmp (atomic_expression_denote ty bt lhs tp) (atomic_expression_denote ty bt rhs tp)).
      * exact true.
      * exact false.
      * exact false.
    + destruct (cmp (atomic_expression_denote ty bt lhs tp) (atomic_expression_denote ty bt rhs tp)).
      * exact false.
      * exact true.
      * exact true.
    + destruct (cmp (atomic_expression_denote ty bt lhs tp) (atomic_expression_denote ty bt rhs tp)).
      * exact true.
      * exact true.
      * exact false.
    + destruct (cmp (atomic_expression_denote ty bt lhs tp) (atomic_expression_denote ty bt rhs tp)).
      * exact false.
      * exact true.
      * exact false.
    + destruct (cmp (atomic_expression_denote ty bt lhs tp) (atomic_expression_denote ty bt rhs tp)).
      * exact true.
      * exact false.
      * exact true.
  - rename H into tp. exact (negb (predicate_denote bt ty p tp)).
Defined.

Fixpoint formula_denote (ty: Tuple.tuple_type) (f: formula ty) {struct f}: Tuple.tuple ty -> bool :=
match f with
  | formula_predicate _ c pred => predicate_denote c ty pred
  | formula_con _ op lhs rhs =>
    match op with
      | And => fun t => andb (formula_denote ty lhs t) (formula_denote ty rhs t)
      | Or => fun t => orb (formula_denote ty lhs t) (formula_denote ty rhs t)
    end
end.


(* Some tests. *)
Example example_formula: formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty BoolType (predicate_true Tuple.example_tuple_ty BoolType)).
Example example_formula': formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty IntegerType
      (predicate_com Tuple.example_tuple_ty IntegerType Eq
        (atomic_expression_const Tuple.example_tuple_ty IntegerType 1)
        (atomic_expression_const Tuple.example_tuple_ty IntegerType 1)
      )
    ).

Example can_index: 0 < length Tuple.example_tuple_ty.
Proof.
  simpl. lia.
Qed.
Example example_formula'': formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty StringType
      (predicate_com Tuple.example_tuple_ty StringType Eq
        (atomic_expression_column Tuple.example_tuple_ty 0 can_index)
        (atomic_expression_const Tuple.example_tuple_ty StringType "233"%string)
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
  - reflexivity.
  - apply order_is_irreflexive in l. contradiction.
Qed.

Axiom abcd: forall lhs rhs: string, lhs = rhs -> Equivalence.equiv lhs rhs.

Definition foo': bool := ((formula_denote Tuple.example_tuple_ty example_formula'') Tuple.example_tuple_lhs).
Lemma foo'_is_false: foo' = false.
Proof.
  refine (
    match foo' as foo'' return foo' = foo'' -> foo'' = false with
      | true => fun _ => False_rec _ _
      | false => fun _ => refl_equal false
    end (refl_equal foo')
  ).

  unfold foo' in e.
  simpl in e.
  destruct (cmp "abcd"%string "233"%string).
  - inversion e. 

Admitted.
End Formula.
