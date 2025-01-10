Require Import Arith.
Require Import Decidable.
Require Import Lia.
Require Import List.
Require Import ListSet.
Require Import RelationClasses.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import String.
Require Import Unicode.Utf8.

Axiom cheating : forall A, A.

Tactic Notation "cheat" := apply cheating.

CoInductive Stream : Set :=
  | Cons : nat -> Stream -> Stream
.

Definition hd (x: Stream) := let (a, _) := x in a.
Definition tl (x: Stream) := let (_, s) := x in s.

CoFixpoint rand (seed n1 n2 : nat) : Stream :=
    let seed' := seed mod n2 in Cons seed' (rand (seed' * n1) n1 n2).

Definition stream: Stream := rand 11 4 514.

(* For simplicity, let us assume that new_id's will never have duplicates. *)
Fixpoint new_id (s: Stream) (times: nat) :=
  match times with
  | 0 => hd s
  | S n => new_id (tl s) n
  end.

Definition ctx (A: Type) := list (nat * A).

(*
  The type `=` accepts only homogeneous equality proofs. This is a problem when we 
  are dealing with dependent types that are heterogeneously equal. Thus we cannot
  directly use `=` to pose some predicates on dependent types.

  One way to do this is to define some transport which corresponds to the Leibniz
  principle: from `x = y` we derive `P x -> P y` for any `P`.

  Reference:
  * https://stackoverflow.com/questions/59593179/coq-type-mismatch-on-dependent-lists-which-could-be-solved-by-a-proof
*)
Definition transport {A: Type} {x y: A} (e: x = y) {P: A → Type} (t: P x) : P y :=
  match e with
  | eq_refl => t
  end.

Notation "x '♯' eq" := (transport x eq) (at level 70).

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

Fixpoint label_lookup {A: Type} (Γ: ctx A) (id: nat): option A :=
  match Γ with
    | nil => None
    | (id', p) :: l' =>
        if Nat.eqb id id' then Some p else label_lookup l' id
  end.

Fixpoint next_available_id {A: Type} (Γ: ctx A) (n: nat): nat :=
  match Γ with
    | nil => n
    | (id, _) :: l' => S (next_available_id l' (max id n))
  end.

Fixpoint update_label {A: Type} (Γ: ctx A) (id: nat) (p: A): ctx A :=
  match Γ with
    | nil => nil
    | (id', p') :: l' =>
        if Nat.eqb id id'
          then 
            let new_id := next_available_id Γ 0 in
              (id', p') :: l' ++ ((new_id, p) :: nil)
          else (id', p') :: update_label l' id p
  end.

(* 
Lemma update_valid: ∀ {A: Type} id (context: ctx A) p p',
  label_lookup context id = Some p →
  label_lookup (update_label context id p') id = Some p'.
Proof.
  induction context.
  - simpl in *. intros. inversion H.
  - destruct a as [ [n b] p].
    + simpl in *. destruct (Nat.eqb id n) eqn: Heq.
      * intros. simpl. rewrite Heq. reflexivity.
      * intros. simpl in *. rewrite Heq. specialize IHcontext with (p := p0) (p' := p').
        apply IHcontext. assumption.
Qed. *)

Definition id_of_length {A: Type} (Γ: ctx A) (len: nat): list nat :=
  let next_id := next_available_id Γ 0 in
    (fix id_of_length (len: nat) (next_id: nat): list nat :=
      match len with
        | O => nil
        | S len' => next_id :: id_of_length len' (S next_id)
      end) len next_id.

Theorem eqb_list_refl :
  ∀ (A : Type) (eqb : A → A → bool),
    (∀ a, eqb a a = true) → ∀ l, eqb_list eqb l l = true.
Proof.
  intros.
  induction l.
  - trivial.
  - simpl.  specialize (H a). rewrite H. apply IHl.
Qed.

Fixpoint bounded_list {A: Type} (l: list A) (idx: list nat): Prop :=
  match idx with
  | nil => True
  | h :: t => h < List.length l ∧ bounded_list l t
  end.

Lemma bounded_list_dec: ∀ (A: Type) (l: list A) (idx: list nat),
  {bounded_list l idx} + {~bounded_list l idx}.
Proof.
  induction idx.
  - left. simpl. trivial.
  - destruct (Compare_dec.lt_dec a (Datatypes.length l)).
    + destruct IHidx.
      * left. simpl. split; assumption.
      * right. red. intros. destruct H. apply n. assumption.
    + right. red. intros. destruct H. apply n. assumption.
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

Definition ntypes {A: Type} (l: list A) (idx: list nat): bounded_list l idx → list A.
  induction idx; intros.
  - exact nil.
  - simpl in *. destruct H.
    pose (cur := nth l a H).
    pose (rest := IHidx H0).
    exact (cur :: rest).
Defined.

Fixpoint find_index {A B: Type} (f: A → B → bool) (l: list A) (elem: B) (cur: nat): option nat :=
  match l with
  | nil => None
  | h :: t => if f h elem then Some cur else find_index f t elem (S cur)
  end.

Fixpoint find' {A B: Type} (f: A → B → bool) (l: list A) (elem: B): option A :=
  match l with
  | nil => None
  | h :: t => if f h elem then Some h else find' f t elem
  end.


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

Fixpoint mark_updated {A: Type} (l: list (nat * bool * A)) (id: list nat): option (list (nat * bool * A)) :=
  match l with
  | nil => Some nil
  | (n, b, a) :: t =>
    match existsb (Nat.eqb n) id with
    | true => match mark_updated t id with
              | None => None
              | Some t' => Some ((n, true, a) :: t')
              end
    | false => None
    end
  end.

Definition unwrap_or_default {A: Type} (o: option A) (default: A): A :=
  match o with
  | Some a => a
  | None => default
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

Fixpoint unique_env {A: Type} (l: ctx A): Prop :=
  match l with
  | nil => True
  | (n, _) :: t =>
    if existsb (fun x => Nat.eqb (fst x) n) t then
      False
    else
      unique_env t
  end.

Fixpoint foldl {A B: Type} (f: A → B → A) (a: A) (l: list B): A :=
  match l with
  | nil => a
  | b :: l' => foldl f (f a b) l'
  end.

Fixpoint dedup {A: Type} (l: ctx A) :=
    match l with
    | nil => nil
    | hd :: tl =>
      if existsb (fun x => Nat.eqb (fst x) (fst hd)) tl then
        dedup tl
      else
        hd :: dedup tl
    end.

Lemma existsb_dedup: ∀ (A: Type) (l: ctx A) (a: nat * A),
  existsb (fun x => fst x =? fst a) l = false → existsb (fun x => fst x =? fst a) (dedup l) = false.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl in *. destruct a, a0.
    apply Bool.orb_false_iff in H. destruct H.
    simpl. apply IHl in H0.
    destruct (existsb (λ x : nat * A, fst x =? n) l).
    + simpl in *. rewrite H0. reflexivity.
    + simpl in *. apply Bool.orb_false_iff. split.
      * apply H.
      * apply H0.
Qed.

Lemma dedup_correct: ∀ (A: Type) (l: ctx A),
  unique_env (dedup l).
Proof.
  induction l.
  - simpl. trivial.
  - simpl. destruct (existsb (λ x : nat * A, fst x =? fst a) l) eqn: H.
    + apply IHl.
    + simpl. destruct a. apply existsb_dedup in H. simpl in H. rewrite H. apply IHl.
Qed.

Definition merge_env {A: Type} (lhs rhs: ctx A) : ctx A := dedup (lhs ++ rhs).
Notation "l1 '⊍' l2" := (merge_env l1 l2) (at level 70).

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

Theorem elem_find_index_bounded:
∀ {A B: Type} (f: A → B → bool) (l: list A) (elem: B) (start: nat) (n: nat),
  find_index f l elem start = Some n → n < List.length l + start.
Proof.
  induction l; intros.
  - inversion H.
  - simpl in *.
    destruct (f a elem) eqn: Hf.
    + inversion H. lia.
    + apply IHl in H. lia.
Qed.

Theorem elem_find_index_bounded_zero:
∀ {A B: Type} (f: A → B → bool) (l: list A) (elem: B) (n: nat),
  find_index f l elem 0 = Some n → n < List.length l.
Proof.
  intros. apply elem_find_index_bounded in H. lia.
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

Definition set_eq {A: Type} (ℓ ℓ': set A) : Prop :=
  ∀ a, (set_In a ℓ → set_In a ℓ') ∧ (set_In a ℓ' → set_In a ℓ).

Definition subset {A: Type} (s1 s2: set A) : Prop :=
  ∀ a, set_In a s1 → set_In a s2.
Notation "s1 '⊆' s2" := (subset s1 s2) (at level 70).

Definition subset_neq {A: Type} (s1 s2: set A) : Prop :=
  s1 ⊆ s2 ∧ ~(set_eq s1 s2).
Notation "s1 '⊂' s2" := (subset_neq s1 s2) (at level 70).

Lemma subset_dec: ∀ {A: Type} (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ': set A),
  {subset ℓ ℓ'} + {~(subset ℓ ℓ')}.
Proof.
  intros.
  specialize Forall_dec with (A := A) (P := λ a, set_In a ℓ');
  specialize Forall_dec with (A := A) (P := λ a, set_In a ℓ); intros.
  specialize set_In_dec with (A := A) (x := ℓ);
  specialize set_In_dec with (A := A) (x := ℓ'); intros.
  intuition.
  unfold subset, set_In in *.
  destruct (X2 ℓ); destruct (X0 ℓ').
  - left. intros. assert (∀ x, In x ℓ → In x ℓ') by (apply Forall_forall; assumption). intuition.
  - left. intros. assert (∀ x, In x ℓ → In x ℓ') by (apply Forall_forall; assumption). intuition.
  - right. intros. apply f. apply Forall_forall. intros. specialize H with x. intuition.
  - right. intros. apply f. apply Forall_forall. intros. specialize H with x. intuition.
Qed.

Lemma set_eq_dec: ∀ {A: Type} (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ': set A),
  {set_eq ℓ ℓ'} + {~(set_eq ℓ ℓ')}.
Proof.
  intros.
  (* Check Forall_dec.  *)
  specialize Forall_dec with (A := A) (P := λ a, set_In a ℓ');
  specialize Forall_dec with (A := A) (P := λ a, set_In a ℓ); intros.
  specialize set_In_dec with (A := A) (x := ℓ);
  specialize set_In_dec with (A := A) (x := ℓ'); intros.
  intuition.

  unfold set_eq, set_In in *.
  destruct (X2 ℓ); destruct (X0 ℓ').
  - left. intros. split; intros.
    + assert (∀ x, In x ℓ → In x ℓ') by (apply Forall_forall; assumption). 
      intuition.
    + assert (∀ x, In x ℓ' → In x ℓ) by (apply Forall_forall; assumption).
      intuition.
  - right. intros. apply f0. 
    apply Forall_forall. intros.
    specialize H with x. destruct H.
    intuition.
  - right. intros. apply f. 
    apply Forall_forall. intros.
    specialize H with x. destruct H.
    intuition.
  - right. intros. apply f. 
    apply Forall_forall. intros.
    specialize H with x. destruct H.
    intuition.
Qed.

Lemma list_eq_dec: ∀ {A: Type} (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ': list A),
  {ℓ = ℓ'} + {ℓ ≠ ℓ'}.
Proof.
  induction ℓ.
  - intros. destruct ℓ'.
    + left. trivial.
    + right. intros. red. intuition. discriminate.
  - intros. destruct ℓ'.
    + right. intros. red. intuition. discriminate.
    + destruct (dec a a0).
      * subst. destruct (IHℓ ℓ').
        -- left. subst. trivial.
        -- right. red. intros. inversion H. intuition.
      * right. red. intros. inversion H. intuition.
Qed.

Lemma subset_neq_implies_neq: ∀ (A: Type) (s1 s2: set A),
  s1 ⊂ s2 → ~(set_eq s1 s2).
Proof.
  unfold subset_neq. intros. intuition.
Qed.

Global Instance set_eq_equiv: ∀ A: Type, Equivalence (@set_eq A).
Proof.
  intros.
  split.
  - unfold Reflexive. intros. unfold set_eq. intros. split; intros; assumption.
  - unfold Symmetric. intros. unfold set_eq in *. intros. specialize H with a.
    intuition.
  - unfold Transitive. intros. unfold set_eq in *. intros.
    specialize H with a. specialize H0 with a.
    intuition.
Defined.

Lemma set_inter_nil: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ: set A),
  set_eq (set_inter dec ℓ nil) nil.
Proof.
  unfold set_eq. intros.
  induction ℓ.
  - simpl. split; auto.
  - intuition.
Qed.
Hint Resolve set_inter_nil: core.

Lemma set_inter_comm_in: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ': set A) (a: A),
  set_In a (set_inter dec ℓ ℓ') ↔ set_In a (set_inter dec ℓ' ℓ).
Proof.
  intros. split; intros.
  - apply set_inter_elim in H. destruct H. apply set_inter_intro; assumption.
  - apply set_inter_elim in H. destruct H. apply set_inter_intro; assumption.
Qed.
Hint Resolve set_inter_comm_in: core.

Lemma set_inter_comm_eq: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}),
  ∀ ℓ ℓ', set_eq (set_inter dec ℓ ℓ') (set_inter dec ℓ' ℓ).
Proof.
  intros. split; intros.
  - apply set_inter_comm_in. assumption.
  - apply set_inter_comm_in. assumption.
Qed.

Lemma set_inter_refl_in: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ: set A),
  set_eq (set_inter dec ℓ ℓ) ℓ.
Proof.
  intros. split; intros.
  - apply set_inter_elim in H. destruct H. assumption.
  - apply set_inter_intro; assumption.
Qed.
Hint Resolve set_inter_refl_in: core.

Lemma set_inter_assoc_in: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ' ℓ'': set A),
  set_eq (set_inter dec ℓ (set_inter dec ℓ' ℓ'')) (set_inter dec (set_inter dec ℓ ℓ') ℓ'').
Proof.
  intros. split; intros.
  - apply set_inter_elim in H. destruct H. apply set_inter_elim in H0. destruct H0.
    apply set_inter_intro.
    + apply set_inter_intro; assumption.
    + assumption.
  - apply set_inter_elim in H. destruct H. apply set_inter_elim in H. destruct H.
    apply set_inter_intro.
    + assumption.
    + apply set_inter_intro; assumption.
Qed.
Hint Resolve set_inter_assoc_in: core.

Lemma set_union_comm_in: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ': set A),
  set_eq (set_union dec ℓ ℓ') (set_union dec ℓ' ℓ).
Proof.
  intros. split; intros.
  - apply set_union_elim in H. destruct H; apply set_union_intro; intuition.
  - apply set_union_elim in H. destruct H; apply set_union_intro; intuition.
Qed.
Hint Resolve set_union_comm_in: core.

Lemma set_union_comm_eq: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}),
  ∀ ℓ ℓ', set_eq (set_union dec ℓ ℓ') (set_union dec ℓ' ℓ).
Proof.
  intros. split; intros.
  - apply set_union_comm_in. assumption.
  - apply set_union_comm_in. assumption.
Qed.

Lemma set_union_refl_in: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ: set A),
  set_eq (set_union dec ℓ ℓ) ℓ.
Proof.
  intros. split; intros.
  - apply set_union_elim in H. destruct H; assumption.
  - apply set_union_intro. intuition.
Qed.
Hint Resolve set_union_refl_in: core.

Lemma set_union_assoc_in: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (ℓ ℓ' ℓ'': set A),
  set_eq (set_union dec ℓ (set_union dec ℓ' ℓ'')) (set_union dec (set_union dec ℓ ℓ') ℓ'').
Proof.
  intros. split; intros.
  - apply set_union_elim in H. destruct H.
    + apply set_union_intro. left. apply set_union_intro. left. assumption.
    + apply set_union_elim in H. destruct H.
      * apply set_union_intro. left. apply set_union_intro. right. assumption.
      * apply set_union_intro. right. assumption.
  - apply set_union_elim in H. destruct H.
    + apply set_union_elim in H. destruct H.
      * apply set_union_intro. left. assumption.
      * apply set_union_intro. right. apply set_union_intro. left. assumption.
    + apply set_union_intro. right. apply set_union_intro. right. assumption.
Qed.
Hint Resolve set_union_assoc_in: core.

Global Instance set_eq_proper {A: Type} (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}):
  Proper (equiv ==> equiv ==> equiv) (set_eq (A:=A)).
Proof.
  repeat red. intros.
  split; intros.
  - rewrite <- H, <- H0. assumption.
  - rewrite H, H0. assumption.
Qed.

Lemma set_inter_subset: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (s1 s2: set A),
  set_eq (set_inter dec s1 s2) s1 ↔ s1 ⊆ s2.
Proof.
  intros. split; intros.
  - unfold subset, set_eq in *. intros. specialize H with a. destruct H.
    apply H1 in H0. apply set_inter_elim in H0.
    destruct H0. assumption.
  - unfold subset, set_eq in *. intros.
    split.
    + intros. apply set_inter_elim in H0. destruct H0. assumption.
    + intros. apply set_inter_intro; try assumption. apply H. assumption.
Qed.

Lemma set_union_subset: ∀ (A: Type) (dec: ∀ (a1 a2: A), {a1 = a2} + {a1 ≠ a2}) (s1 s2: set A),
  set_eq (set_union dec s1 s2) s1 ↔ s2 ⊆ s1.
Proof.
  intros. split; intros.
  - unfold subset, set_eq in *. intros. specialize H with a. destruct H.
    apply H. apply set_union_intro. right. assumption.
  - unfold subset, set_eq in *. intros.
    split.
    + intros. apply set_union_elim in H0. destruct H0.
      * assumption.
      * apply H in H0. assumption.
    + intros. apply set_union_intro. left. assumption.
Qed.

Global Instance subset_transitive {A: Type}: Transitive (@subset A).
Proof.
  unfold Transitive, subset. intros.
  apply H in H1. apply H0 in H1. assumption.
Qed.

Global Instance subset_neq_transitive {A: Type}: Transitive (@subset_neq A).
Proof.
  repeat red. unfold subset_neq, subset, set_eq in *. split; intros;
  destruct H, H0; unfold not in *.
  - apply H0. apply H. assumption.
  - intros. apply H2. intros. split; intuition.
    specialize H with a. specialize H0 with a. specialize H3 with a.
    intuition.
Qed.

