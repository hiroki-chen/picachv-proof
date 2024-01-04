Require Import Lia.
Require Import List.
Require Import String.
Require Import Unicode.Utf8.

Definition hd_option {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | cons h _ => Some h
  end.

Definition hd_ok {A: Type} (l: list A) (non_empty: List.length l > 0) : A.
  destruct l.
  - simpl in non_empty. lia.
  - exact a.
Defined.

Definition sublist A ℓ ℓ' := ∀ (a: A), In a ℓ → In a ℓ'.

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

Fixpoint lookup {A: Type} (n: nat) (l: list (nat * A)) : option A :=
  match l with
  | nil => None
  | (n', a) :: t => if Nat.eqb n n' then Some a else lookup n t
  end.

Fixpoint update {A: Type} (l: list (nat * A)) (n: nat) (a: A) : list (nat * A) :=
  match l with
  | nil => nil
  | (n', a') :: t => if Nat.eqb n n' then (n, a) :: t else (n', a') :: update t n a
  end.

(*
  This function merges two lists of (nat * A) pairs. The first list is the new
  list, and the second list is the old list. The function returns a new list.

  The function works as follows:
  - If the new list is empty, then the old list is returned.
  - If the old list is empty, then the new list is returned.
  - If the element of the new list is not in the old list, then the element is
    added to the old list.
  - If the element of the new list is in the old list, then the element is
    replaced in the old list.
*) 
Fixpoint merge {A: Type} (new old: list (nat * A)) : list (nat * A) :=
  match new with
  | nil => old
  | (n, a) :: t =>
    match lookup n old with
    | None => (n, a) :: merge t old
    | Some _ => merge t (update old n a)
    end
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

Definition nth {A: Type} (l: list A) (n: nat): n < List.length l → A.
refine (
  (fix nth l n :=
    match l as l', n as n' return l = l' → n = n' → n' < List.length l → A with
    | nil, _ => _
    | h :: t, 0 => _
    | h :: t, S n' => _
    end eq_refl eq_refl) l n
).
  - intros. subst. simpl in H1. lia.
  - intros. exact h.
  - intros. subst. apply nth with t n'. simpl in H1. lia.
Defined.

Fixpoint set_nth {A: Type} (l: list A) (n: nat) (a: A): list A :=
  match l, n with
  | nil, _ => nil
  | h :: t, 0 => a :: t
  | h :: t, S n' => h :: set_nth t n' a
  end.

Fixpoint list_of_length_n {A: Type} (n: nat) (a: A): list A :=
  match n with
  | 0 => nil
  | S n' => a :: list_of_length_n n' a
  end.

(*
  Coq cannot guess if `n / 10` and `n mod 10` will terminate;
  we use binary representation for the time being.
*)
Fixpoint nat_to_str (n: nat): String.string :=
  match n with
  | O => "0"%string
  | S n' => append (nat_to_str n') "1"%string
  end.

Fixpoint rev_string (s: string): string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => append (rev_string s') (String c EmptyString)
  end.

Fixpoint redact_string_helper (s: string) (n: nat): string :=
  match n with
  | O => s
  | S n' =>
    match s with
    | EmptyString => EmptyString
    | String _ s' => append "*"%string (redact_string_helper s' n')
    end
  end.

Definition redact_string (s: string) (n: nat) (rev: bool): string :=
  match rev with
  | true => rev_string (redact_string_helper (rev_string s) n)
  | false => redact_string_helper s n
  end.

Example redact_string_example: redact_string "hello" 3 false = "***lo"%string.
Proof. trivial. Qed.

Example redact_string_example2: redact_string "hello" 3 true = "he***"%string.
Proof. trivial. Qed.

Theorem eq_length_list_zip_preserves_length :
  ∀ (A B: Type) (l1: list A) (l2: list B),
    List.length l1 = List.length l2 → List.length (zip_lists l1 l2) = List.length l1.
Proof.
  induction l1.
  - intros. destruct l2. trivial. inversion H.
  - intros. destruct l2. inversion H. simpl. apply eq_S.
    apply IHl1. inversion H. trivial.
Qed.

Theorem list_has_head_gt_zero:
  ∀ (A: Type) (a: A) (l l': list A),
    l = (a :: l') → List.length l > 0.
Proof.
  intros. rewrite H. simpl. lia.
Qed.

(*
  This theorem states that if a list is a sublist of another list, then if a given
  property holds for an element of the sublist, then the property holds for the
  element of the list.
*)
Theorem sublist_holds: ∀ (A: Type) (ℙ: A → Prop) (ℓ ℓ': list A),
  sublist A ℓ ℓ' →
  (∀ a, In a ℓ' → ℙ a) →
  (∀ a, In a ℓ → ℙ a).
Proof.
  unfold sublist. intros.
  apply H0. apply H. assumption.
Qed.

(*
  [filter_true] is a theorem that states that filtering a list with a predicate that always returns true
  will result in the same list.
*)
Theorem filter_true: ∀ (A: Type) (ℓ: list A),
  List.filter (λ _, true) ℓ = ℓ.
Proof.
  intros. induction ℓ.
  - trivial.
  - simpl. rewrite IHℓ. trivial.
Qed.

(*
  [filter_false] is a theorem that states that filtering a list with a predicate that always returns false results in an empty list.
*)
Theorem filter_false: ∀ (A: Type) (ℓ: list A),
  List.filter (λ _, false) ℓ = nil.
Proof.
  intros. induction ℓ.
  - trivial.
  - simpl. rewrite IHℓ. trivial.
Qed.

(* This is needed since we need to let Coq reduce `app_assoc'`. *)
Lemma app_assoc': ∀ A (l1 l2 l3: list A),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Defined.
