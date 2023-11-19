Require Import SetoidDec.
Require Import SetoidClass.
Require Import OrderedType.
Require Import Equivalence.
Require Import Lia.
Require Import Ascii.
Require Import String.
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

Definition to_lower (a' : ascii) : ascii :=
  let a := nat_of_ascii a' in
  if le_lt_dec a (nat_of_ascii "z"%char) then
    if le_lt_dec (nat_of_ascii "a"%char) a then
      ascii_of_nat (a - nat_of_ascii "a"%char + nat_of_ascii "A")
    else a'
  else a'.

Definition char_eq (lhs rhs: ascii): Prop :=
  (nat_of_ascii (to_lower lhs)) = (nat_of_ascii (to_lower rhs)).
Definition char_lt (lhs rhs: ascii): Prop :=
  (nat_of_ascii (to_lower lhs)) < (nat_of_ascii (to_lower rhs)).
Definition char_trans: Transitive char_lt.
  unfold Transitive.
  intros. unfold char_lt in *. lia.
Defined.

Instance char_eq_setoid : Setoid ascii.
refine (@Build_Setoid _ char_eq _).
  econstructor.
  - unfold Reflexive. intros. unfold char_eq. auto.
  - unfold Symmetric. intros. unfold char_eq in *. auto.
  - unfold Transitive. intros. unfold char_eq in *. lia.
Defined.

Global Instance char_ordered: Ordered ascii.
refine (
  @Build_Ordered ascii char_eq_setoid char_lt char_trans _ _
).
  intros. simpl.
  - unfold char_lt in H. unfold complement. intros.
    rewrite H0 in H. lia.
    (* Directly destrucing on ascii itself is not doable. *)
  - intros. destruct (nat_dec (nat_of_ascii (to_lower lhs)) (nat_of_ascii (to_lower rhs))).
    + destruct s.
      * apply LT. unfold char_lt. auto.
      * apply EQ. unfold equiv. simpl. unfold char_eq. auto.
    + apply GT. unfold char_lt. auto.
Defined.

Definition string_eq (lhs rhs: string): Prop := lhs = rhs.
Definition string_lt (lhs rhs: string): Prop :=
  String.compare lhs rhs = Lt.
