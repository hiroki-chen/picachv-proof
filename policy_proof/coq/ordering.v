Require Import SetoidDec.
Require Import SetoidClass.
Require Import OrderedType.
Require Import Equivalence.
Require Import Lia.
Require Import Compare_dec.

Class Ordered (A: Set) := {
  eq :: Setoid A;

  lt: A -> A -> Prop;
  trans :: Transitive lt;
  neq: forall lhs rhs: A, lt lhs rhs -> lhs =/= rhs;
  cmp: forall lhs rhs: A, Compare lt equiv lhs rhs;
}.


Definition nat_dec : forall (a b: nat), {a < b} + {a = b} + {b < a}.
 intros. pose (lt_eq_lt_dec a b).
 destruct s; auto; destruct s; auto.
Qed.

Definition nat_eq (a b: nat): Prop := a = b.
Definition nat_lt (a b: nat): Prop := a < b.
Definition nat_trans: Transitive nat_lt.
Proof.
  unfold Transitive.
  intros.
  unfold nat_lt in *.
  lia.
Qed.

Global Instance nat_ordered: Ordered nat.
refine (
  @Build_Ordered nat (eq_setoid nat) nat_lt nat_trans _ _
).
  unfold nat_lt, Transitive, complement;
  intros; simpl in *; try lia.
  intros.
  destruct (nat_dec lhs rhs). destruct s.
  - apply LT. auto.
  - apply EQ. auto.
  - apply GT. auto.
Defined.

Definition bool_eq (lhs rhs: bool): Prop := lhs = rhs.
Definition bool_lt (lhs rhs: bool): Prop := lhs = false /\ rhs = true.
Definition bool_trans : Transitive bool_lt.
  unfold Transitive. intros.
  unfold bool_lt in *. intuition.
Defined.

Global Instance bool_ordered: Ordered bool.
refine (
  @Build_Ordered bool (eq_setoid bool) bool_lt bool_trans _ _
).
  unfold bool_lt; unfold bool_eq.
  - intuition. subst.
    simpl. unfold complement. intros. inversion H.
  - intros. destruct lhs; destruct rhs; simpl.
    + apply EQ. unfold equiv. auto.
    + apply GT. unfold bool_lt. auto.
    + apply LT. unfold bool_lt. auto.
    + apply EQ. unfold equiv. auto.
Defined.
