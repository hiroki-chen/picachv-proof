Require Import List.
Require Import Unicode.Utf8.

Definition hd_option {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | cons h _ => Some h
  end.

Fixpoint eqb_list {A: Type} (eqb: A → A → bool) (l1 l2: list A): bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1 :: t1, h2 :: t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  end.

Theorem eqb_list_refl :
  ∀ (A : Type) (eqb : A → A → bool),
    (∀ a, eqb a a = true) → ∀ l, eqb_list eqb l l = true.
Proof.
  intros.
  induction l.
  - trivial.
  - simpl.  specialize (H a). rewrite H. apply IHl.
Qed.
