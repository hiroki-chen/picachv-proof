Require Import Setoid Coq.Classes.Morphisms Basics List PeanoNat Coq.Logic.FinFun Psatz Coq.Sorting.Mergesort Coq.Structures.Orders Coq.Logic.FinFun Coq.Program.Equality.

Reserved Notation "X '⊓' Y" (at level 39, left associativity).
Reserved Notation "X '⊔' Y" (at level 40, left associativity).
Reserved Notation " x '===' y " (at level 70, no associativity).
Reserved Notation " x '=/=' y " (at level 70, no associativity).
Reserved Notation "⊤".
Reserved Notation "⊥".
Reserved Notation "X '⊑' Y" (at level 70, no associativity).

Class lattice (A : Set) :=
  Lattice {
      join: A -> A -> A where "X '⊔' Y" := (join X Y);
      meet: A -> A -> A where "X '⊓' Y" := (meet X Y);
      top: A where "⊤" := @top;
      bot: A where "⊥" := @bot;
      eq: A -> A -> Prop where "x '===' y" := (eq x y)
        and "x '=/=' y" := (complement eq x y)
        and "X '⊑' Y" := (X ⊔ Y === Y);
      eq_equiv :: Equivalence eq;
      meet_symmetry: forall a b : A, a ⊓ b === b ⊓ a;
      join_symmetry: forall a b   : A,  a ⊔ b === b ⊔ a;
      join_assoc   : forall a b c : A,  a ⊔ (b ⊔ c) === (a ⊔ b) ⊔ c;
      join_absorp : forall a b   : A,  a ⊔ (a ⊓ b) === a;
      meet_assoc   : forall a b c : A,  a ⊓ (b ⊓ c) === (a ⊓ b) ⊓ c;
      meet_absorp : forall a b   : A,  a ⊓ (a ⊔ b) === a;
      join_bot: forall a     : A, bot ⊔ a === a;
      join_top: forall a     : A, ⊤ ⊔ a === ⊤;
                               meet_bot: forall a     : A, bot ⊓ a === bot;
      meet_top: forall a     : A, ⊤ ⊓ a === a;
      join_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊔ y1 === x2 ⊔ y2;
      meet_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊓ y1 === x2 ⊓ y2;
      flowsto_compat_right: forall x y z, x === y -> z ⊑ y -> z ⊑ x;
      flowsto_compat_left: forall x y z, x === y -> y ⊑ z -> x ⊑ z
    }.

Notation "X '⊓' Y" := (meet X Y)(at level 39, left associativity).
Notation "X '⊔' Y" := (join X Y) (at level 40, left associativity).
Notation "x '===' y" := (eq x y) (at level 70, no associativity).
Notation "x '=/=' y" := (complement eq x y) (at level 70, no associativity).
Notation "⊤" := top.
Notation "⊥" := bot.

Definition flowsto {A : Set} `{lattice A} (a b : A): Prop := a ⊔ b === b.
Notation "X '⊑' Y" := (flowsto X Y) (at level 70, no associativity).

Arguments flowsto _ _ : simpl nomatch.
Arguments join _ _ : simpl nomatch.
Arguments meet _ _ : simpl nomatch.

Hint Resolve meet_symmetry join_symmetry join_assoc meet_assoc meet_absorp join_absorp join_top join_bot meet_top meet_bot eq_equiv.

Section LatticeProperties.
  Context {A : Set} `{lattice A}.

  Global Add Parametric Relation : A eq
      reflexivity proved by (@Equivalence_Reflexive A eq eq_equiv)
      symmetry proved by (@Equivalence_Symmetric A eq eq_equiv)
      transitivity proved by (@Equivalence_Transitive A eq eq_equiv)
        as eq_rel.
  Hint Resolve eq_rel : typeclass_instances.

  Class Morphism2 (f : A -> A -> A) :=
    {
      compat2: forall (x1 y1 x2 y2 : A), x1 === x2 -> y1 === y2 -> f x1 y1 === f x2 y2
    }.
  
  Class MorphismR (f : A -> A -> Prop) :=
    {
      compatR: forall (x1 y1 x2 y2 : A), x1 === x2 -> y1 === y2 -> f x1 y1 <-> f x2 y2
    }.


Global Instance eq_rewrite2_Proper (f : A -> A -> A) `{Morphism2 f}:
  Proper (eq ==> eq ==> eq) f.
Proof.
  intros x1 y1 H_eq1 x2 y2 H_eq2.
  eapply compat2; eassumption.
Qed.
Hint Resolve eq_rewrite2_Proper : typeclass_instances.

Global Instance eq_rewrite3_Proper (f : A -> A -> Prop) `{MorphismR f}:
  Proper (eq ==> eq ==> flip impl) f.
Proof.
  intros x1 y1 H_eq1 x2 y2 H_eq2.
  unfold flip.
  intro.
  eapply compatR; eassumption.
Qed.
Hint Resolve eq_rewrite3_Proper : typeclass_instances.


Global Instance join_inst: Morphism2 join := { compat2 := join_compat }.
Global Instance meet_inst: Morphism2 meet := { compat2 := meet_compat }.
Hint Resolve join_inst : typeclass_instances.
Hint Resolve meet_inst : typeclass_instances.

Lemma join_idem: forall a, a ⊔ a === a.
Proof.
  intros. rewrite <- (meet_absorp a a) at 2. auto.
Qed.
Hint Resolve join_idem.

Lemma meet_idem: forall a, a ⊓ a === a.
Proof.
  intros. rewrite <- (join_absorp a a) at 2. auto.
Qed.
Hint Resolve meet_idem.

Global Instance flowsto_trans: Transitive flowsto.
  unfold Transitive. intros.
  unfold flowsto in *.  rewrite <- H1. rewrite <- H0.
  assert (x ⊔ (x ⊔ y ⊔ z) === (x ⊔ x) ⊔ y ⊔ z).
  - rewrite <- join_assoc. auto. rewrite H1. rewrite <- join_assoc. rewrite join_idem.
    rewrite join_assoc. rewrite H1. rewrite join_idem. reflexivity.
  - rewrite H2. rewrite join_idem. reflexivity.
Defined.
End LatticeProperties.
