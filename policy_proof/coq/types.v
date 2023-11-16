Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import policy.

(* A setoid is a set (X, ~) with an equivalence relation. *)
(* We can derive three properties from an equivalence class:
  1. Reflexivity.
  2. Symmetry.
  3. Transitivity.
*)
Require Import SetoidClass.
Require Import RelationClasses.

Inductive Conjuction: Type := And | Or.
Inductive Comparison: Type := Gt | Lt | Ge | Le | Eq | Neq.
Inductive BinaryOp: Type := Add | Sub | Mul | Div | Mod.

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
Definition transform_list := list transform_func%type.
Definition aggregate_list := list transform_func%type.

(* Something that will appear in `where` or filter. *)
Inductive predicate (domain: Type): Type :=
  (* Constant true *)
  | predicate_true: predicate domain
  | predicate_false: predicate domain
  (* Negation *)
  | predicate_not: predicate domain -> predicate domain
  (* A conjuction *)
  | predicate_conj: Conjuction -> predicate domain -> predicate domain -> predicate domain
.

Definition true_to_coq_true (domain: Type) (p: predicate domain): bool :=
  match p with
  | predicate_true _ => true
  | _ => false
  end.

Definition coq_true_to_true (domain: Type) (b: bool): predicate domain :=
  match b with
  | true => predicate_true domain
  | false => predicate_not domain (predicate_true domain)
  end.

Module Cell.

(* A cell that does not carry policies. *)
Definition clean_cell: Set := basic_type % type.
(* A cell that carries policies . *)
Definition cell: Set := (clean_cell * policy) % type.

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

Definition example_tuple_ty : tuple_type := (StringType, policy_empty) :: (BoolType, policy_empty) :: nil.
Definition example_tuple: tuple example_tuple_ty := (("abcd"%string, policy_empty), ((true, policy_empty), tt)).
Definition example_tuple_ty' : tuple_type := (IntegerType, policy_empty) :: nil.
Definition example_tuple' : tuple example_tuple_ty' := ((1, policy_empty), tt).
Definition example_tuple'' : tuple (example_tuple_ty' ++ example_tuple_ty) := 
  ((1, policy_empty),
    (("abcd"%string, policy_empty),
      ((true, policy_empty),
        tt))).

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

Definition tuple_is_setoid (ty: tuple_type): Setoid (tuple ty).
Proof.
  exists (tuple_eq ty).
  apply tuple_eq_eqv.
Qed.

Definition example_tuple_lhs : tuple example_tuple_ty := (("abcd"%string, policy_empty), ((true, policy_empty), tt)).
Definition example_tuple_rhs : tuple example_tuple_ty := (("abcd"%string, policy_empty), ((true, policy_empty), tt)).

Example example_tuple_eq: tuple_eq example_tuple_ty example_tuple_lhs example_tuple_lhs.
Proof.
  simpl. repeat split.
Qed.

End Tuple.
