Require Import List.
Require Import Lia.
Require Import Unicode.Utf8.

Definition hd_option {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | cons h _ => Some h
  end.

Definition hd_ok {A: Type} (l: list A) (non_empty: length l > 0) : A.
  destruct l.
  - simpl in non_empty. lia.
  - exact a.
Defined.

Fixpoint zip_lists {A B: Type} (l1: list A) (l2: list B): list (A * B) :=
  match l1, l2 with
  | nil, _ => nil
  | _, nil => nil
  | h1 :: t1, h2 :: t2 => (h1, h2) :: zip_lists t1 t2
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

Fixpoint set_nth {A: Type} (l: list A) (n: nat) (a: A): list A :=
  match l, n with
  | nil, _ => nil
  | h :: t, 0 => a :: t
  | h :: t, S n' => h :: set_nth t n' a
  end.

Theorem eq_length_list_zip_preserves_length :
  ∀ (A B: Type) (l1: list A) (l2: list B),
    length l1 = length l2 → length (zip_lists l1 l2) = length l1.
Proof.
  induction l1.
  - intros. destruct l2. trivial. inversion H.
  - intros. destruct l2. inversion H. simpl. apply eq_S.
    apply IHl1. inversion H. trivial.
Qed.

Fixpoint lookup {A: Type} (n: nat) (l: list (nat * A)) : option A :=
  match l with
  | nil => None
  | (n', a) :: t => if Nat.eqb n n' then Some a else lookup n t
  end.

Theorem list_has_head_gt_zero:
  ∀ (A: Type) (a: A) (l l': list A),
    l = (a :: l') → length l > 0.
Proof.
  intros. rewrite H. simpl. lia.
Qed.
