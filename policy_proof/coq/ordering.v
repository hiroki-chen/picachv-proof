Require Import SetoidDec.
Require Import SetoidClass.
Require Import Decidable.
Require Import OrderedType.
Require Import Equivalence.
Require Import Lia.
Require Import Ascii.
Require Import String.
Require Import Compare_dec.

(*
   Working on user-defined structures that behave like setoids require some special rewriting techniques.
   These structures are often equipped with ad-hoc equivalence relations meant to behave as equalities.
   See also: https://coq.inria.fr/refman/addendum/generalized-rewriting.html
*)
(* Strict order. *)
Class Ordered (A: Set) := {
  eq :: Setoid A;

  lt: A -> A -> Prop;
  trans :: Transitive lt;
  neq: forall lhs rhs: A, lt lhs rhs -> lhs =/= rhs;
  cmp: forall lhs rhs: A, Compare lt equiv lhs rhs;
}.

Definition le {A: Set} {ord: Ordered A} (lhs rhs: A):= lt lhs rhs \/ lhs == rhs.

Theorem order_is_irreflexive: forall {A: Set} {ord: Ordered A} (a: A),
  ~ lt a a.
Proof.
  intros. unfold "~". intros.
  apply neq in H. auto with *.
Qed.
 
Global Instance order_antisym {A: Set} {ord: Ordered A}: Asymmetric lt.
Proof.
  repeat red. intros. 
  rewrite H0 in H.
  apply order_is_irreflexive in H. assumption.
Qed.

Lemma le_dec {A: Set} {ord: Ordered A} (lhs rhs: A): decidable (le lhs rhs).
Proof.
  red. destruct (cmp lhs rhs); unfold le in *.
  - left. left. assumption.
  - left. right. assumption.
  - right. unfold not. intros. destruct H.
    + apply asymmetry in l; assumption.
    + apply neq in l. auto with *.
Qed.

Global Instance eq_dec {A: Set} {ord: Ordered A}: EqDec eq.
  red.
  intros. destruct (cmp x y); intuition.
  - right. apply neq. assumption.
  - right. symmetry. apply neq. assumption.
Defined.

Global Instance eq_dec_setoid {A: Set} {ord: Ordered A}: DecidableSetoid eq.
  red. intros.
  unfold Decidable.decidable. unfold complement.
  destruct (equiv_dec x y).
  left. assumption.
  right. unfold not. intros. intuition.
Defined.

(*
    This instance ensures that the 'lt' relation is proper with respect to the equivalence relation 'equiv'. 
    In other words, if two elements are equivalent to two others (under 'equiv'), then the truth of 'lt' should be preserved between the pairs.

    With this instance defined, we can use the 'rewrite' tactic to rewrite 'lt' relations.
*)
Global Instance ord_lt_proper_eq {A: Set} {ord: Ordered A}:
  Proper (equiv ==> equiv ==> iff) lt.
Proof.
  repeat red. intros.
  red in H, H0. split; intros.
  - destruct (cmp y y0); intuition; try red in e.
    + assert (x == x0). eapply transitivity. eauto. symmetry in e. eapply transitivity; eauto.
      symmetry in e. eauto. symmetry in H0. assumption.
      apply neq in H1. intuition auto with *.
    + destruct (cmp x y0). 
      assert (lt x y) by (eapply transitivity; eauto). apply neq in H2. auto with *.
      red in e. rewrite H in e. apply neq in l. auto with *.
      assert (lt y0 x0) by (eapply transitivity; eauto). apply neq in H2. auto with *.
  - destruct (cmp x x0); intuition; try red in e.
    + rewrite H in e. rewrite H0 in e. apply neq in H1. auto with *.
    + destruct (cmp y x0).
      assert (lt y x) by (eapply transitivity; eauto). apply neq in H2. auto with *.
      red in e. rewrite H0 in e. apply neq in H1. auto with *.
      assert (lt x0 y0) by (eapply transitivity; eauto). apply neq in H2. auto with *.
Qed.
Hint Resolve ord_lt_proper_eq.

Global Instance le_proper_eq {A: Set} {ord: Ordered A}:
  Proper (equiv ==> equiv ==> iff) le.
Proof.
  repeat red. intros. split; intros; unfold le in *; unfold equiv in *.
  - destruct H1.
    + left. rewrite <- H, <- H0. assumption.
    + right. rewrite <- H, <- H0. assumption.
  - destruct H1.
    + left. rewrite H, H0. assumption.
    + right. rewrite H, H0. assumption.
Qed.

Global Instance le_proper_lt {A: Set} {ord: Ordered A}:
  Proper (lt --> lt ++> impl) le.
Proof.
  repeat red. intros; unfold flip in H.
  unfold le in *.
  destruct H1.
  - left. eapply transitivity; eauto; eapply transitivity; eauto.
  - rewrite <- H1 in H0. left. eapply transitivity; eauto.
Qed.

Global Instance lt_proper_le {A: Set} {ord: Ordered A}:
  Proper (le --> le ++> impl) lt.
Proof.
  unfold Proper, respectful, flip, impl, le. intros.
  destruct H0; destruct H.
  - eapply transitivity; eauto; eapply transitivity; eauto.
  - rewrite <- H in H1. eapply transitivity; eauto.
  - rewrite H0 in H1. eapply transitivity; eauto.
  - rewrite H0 in H1. rewrite <- H in H1. assumption.
Qed.

(* Now we can apply rewrite on `lt`. *)
Example rewrite_lt: forall {A: Set} {ord: Ordered A} (a b c d: A),
  a == b -> c == d -> lt a c -> lt b d.
Proof.
  intros. rewrite H, H0 in H1. assumption.
Qed.

Global Instance order_irreflexive: forall {A: Set} {ord: Ordered A} (a: A),
  Irreflexive lt.
  intros. unfold Irreflexive. unfold complement. unfold Reflexive. intros.
  apply order_is_irreflexive in H. assumption.
Qed.

Definition nat_dec : forall (a b: nat), {a < b} + {a = b} + {b < a}.
Proof.
 intros. pose (lt_eq_lt_dec a b).
 destruct s; auto; destruct s; auto.
Qed.

Definition nat_eq (a b: nat): Prop := a = b.
Definition nat_lt (a b: nat): Prop := a < b.
Global Instance nat_lt_trans: Transitive nat_lt.
  unfold Transitive.
  intros.
  unfold nat_lt in *.
  lia.
Defined.

Global Instance nat_ordered: Ordered nat.
refine (
  @Build_Ordered nat (eq_setoid nat) nat_lt nat_lt_trans _ _
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
Global Instance bool_trans : Transitive bool_lt.
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


Example rewrite_lt': forall (a b c d: bool),
  a == b -> c == d -> lt a c -> lt b d.
Proof.
  intros. rewrite H, H0 in H1. assumption.
Qed.

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
Definition char_lt_trans: Transitive char_lt.
  unfold Transitive.
  intros. unfold char_lt in *. lia.
Defined.

Global Instance char_eq_setoid : Setoid ascii.
refine (@Build_Setoid _ char_eq _).
  econstructor.
  - unfold Reflexive. intros. unfold char_eq. auto.
  - unfold Symmetric. intros. unfold char_eq in *. auto.
  - unfold Transitive. intros. unfold char_eq in *. lia.
Defined.

Global Instance char_ordered: Ordered ascii.
refine (
  @Build_Ordered ascii char_eq_setoid char_lt char_lt_trans _ _
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

(* Using String.eq makes everything obsecure and hard to prove. *)
Fixpoint string_eq (lhs rhs: string): Prop := 
  match lhs, rhs with
    | EmptyString, EmptyString => True
    | String l lhs', String r rhs' => char_eq l r /\ string_eq lhs' rhs'
    | _, _ => False
  end.

Fixpoint string_lt (lhs rhs: string): Prop := 
  match lhs, rhs with
    | EmptyString, String _ _ => True
    | String l lhs', String r rhs' => char_lt l r \/ (char_eq l r /\ string_lt lhs' rhs')
    | _, _ => False
  end.

Global Instance string_eq_trans: Transitive string_eq.
  unfold Transitive.
  (* Intros y z makes y, z dependent but they should remain universal. *)
  induction x; destruct y; destruct z; try auto with *.
  simpl in *.
  intros. destruct H. destruct H0.
  split.
  - unfold char_eq in *. lia.
  - specialize (IHx _ _ H1 H2). trivial.
Defined.

Global Instance string_lt_trans: Transitive string_lt.
  unfold Transitive.
  induction x; destruct y; destruct z; try auto with *; simpl in *; intros;
    try destruct H0; try destruct H.
  - left. unfold char_lt in *. lia.
  - left. destruct H. unfold char_eq in *. unfold char_lt in *. rewrite <- H in H0. assumption.
  - left. destruct H0. unfold char_eq in *. unfold char_lt in *. rewrite H0 in H. assumption.
  - destruct H, H0. right. split.
    + unfold char_eq in *. lia.
    + specialize (IHx _ _ H1 H2). assumption.
Defined.

Lemma string_eq_two_parts: forall (lhs rhs: string) (a b: ascii),
  String a lhs = String b rhs -> a = b /\ lhs = rhs.
Proof.
  induction a.
  intros. split. inversion H. auto.
  inversion H. reflexivity.
Qed.
Hint Resolve string_eq_two_parts.

Lemma ord_dec {A: Set} {O: Ordered A} : forall (lhs rhs: A), decidable (lt lhs rhs).
Proof.
  intros. red. destruct (cmp lhs rhs).
  - left. assumption.
  - red in e. right. unfold not. intros. apply neq in H. intuition.
  - right. unfold not. intros. assert (lt lhs lhs) by (eapply transitivity in l; eauto).
    apply order_is_irreflexive in H0. assumption.
Qed.
(* Hint Resolve ord_dec. *)

Definition string_eq_setoid: Setoid string.
refine (@Build_Setoid _ string_eq _).
  constructor.
  - unfold Reflexive. unfold string_eq. induction x.
    + auto.
    + intuition auto with *.
  -  unfold string_eq. unfold Symmetric. induction x; destruct y; intuition auto with *.
    unfold char_eq. auto. specialize (IHx _ H1). auto.
  - unfold string_eq. unfold Transitive.
    induction x; destruct y; destruct z; intuition auto with *.
    + unfold char_eq in *. lia.
    + specialize (IHx y z H2). apply IHx. assumption.
Defined.

Global Instance string_eq_equiv: Equivalence string_eq.
  apply string_eq_setoid.
Defined.

Global Instance string_ordered: Ordered string.
refine (
  @Build_Ordered string string_eq_setoid string_lt string_lt_trans _ _
);
  simpl; unfold complement.
  - induction lhs; destruct rhs. intros; intuition auto with *. intros. inversion H0.
    + intros. inversion H0.
    + induction a; destruct a0. simpl. intros. unfold char_lt in *. unfold char_eq in *.
      destruct H, H0. lia. destruct H. specialize (IHlhs rhs). apply IHlhs; assumption.
  - induction lhs; destruct rhs; intros.
    + apply EQ. unfold equiv. simpl. auto.
    + apply LT. unfold string_lt. simpl. auto.
    + apply GT. unfold string_lt. simpl. auto.
    + pose char_ordered. destruct (cmp a a0).
      * apply LT. simpl in *. left. assumption.
      * destruct (IHlhs rhs).
        -- apply LT. simpl in *. right. split. assumption. assumption.
        -- apply EQ. simpl in *. split. assumption. assumption.
        -- apply GT. simpl in *. right. split. unfold equiv in *. unfold char_eq in *. lia. assumption.
      * apply GT. simpl in *. left. assumption.
Defined.

Global Instance string_lt_eq_proper: Proper (equiv ==> equiv ==> iff) string_lt.
Admitted.
Global Instance string_lt_antisym: Asymmetric string_lt.
Admitted.


Definition unit_eq (_ _: unit) : Prop := True.
Definition unit_lt (_ _: unit) : Prop := False.

Global Instance unit_lt_trans : Transitive unit_lt.
  unfold Transitive. unfold unit_lt. intros. contradiction.
Defined.

Global Instance unit_ordered: Ordered unit.
refine (
  @Build_Ordered unit (eq_setoid unit) unit_lt unit_lt_trans _ _
).
  unfold unit_lt. unfold complement. intros. contradiction.
  intros. destruct lhs; destruct rhs; simpl; auto.
  apply EQ. unfold equiv. reflexivity.
Defined.
