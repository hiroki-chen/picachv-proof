Require Import Arith.
Require Import Lia.
Require Import List.
Require Import RelationClasses.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import String.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import finite_bags.
Require Import ordering.
Require Import trace.
Require Import types.
Require Import util.

(** 
  [relation_np] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.
  Note: this will make tuple ignorant of the policy.
  @param s   The schema of the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation_np (s: schema) := fbag (Tuple.tuple_np (♭ s)).

(** 
  [relation] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.

  @param s   The schema of the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation (s: schema) := fbag (Tuple.tuple (♭ s)).
Hint Unfold relation: core.

Inductive relation_wrapped: Type :=
  | RelationWrapped: ∀ s, relation s → relation_wrapped
.

(* Experimental: a columnar data store. *)
Fixpoint dataframe (s: schema): Type :=
  match s with
  | nil => unit
  | (bt, _) :: t => (fbag (type_to_coq_type bt * nat) * dataframe t)%type
  end.

Definition db_entry s := (Tuple.tuple_np (♭ s) * Policy.policy_store (♭ s))%type.

(*
  [database] represents an abstract database that consists of a collection of relations. This type is defined inductively
  because schemas are different, in which case we cannot use a list (type should be the smae) to represent a database.
*)
Inductive database: Type :=
  | database_empty: database
  (*
    A database entry that stores a list of tuples as relations; this is for assigning
    new UUIDs to each cell.
  *)
  | database_relation:
      ∀ s, list (db_entry s) → budget → database → database
.

Fixpoint db_size (db: database): nat :=
  match db with
    | database_empty => 0
    | database_relation _ _ _ db' => S (db_size db')
  end.

Lemma schema_concat_eq: ∀ s1 s2,
  ♭ (s1 ++ s2) = ♭ s1 ++ ♭ s2.
Proof.
  intros.
  induction s1.
  + reflexivity.
  + destruct a.
    simpl. rewrite IHs1. reflexivity.

(*
  Note that we do not `Qed` here since we do not want to make this lemma opaque so that Coq cannot automatically
  simplify the at the type level of relation.
*)
Defined.

Lemma nth_type_eq: ∀ s n (ok: n < List.length s) (ok': n < List.length (♭ s)),
  ♭ ((nth s n ok) :: nil) = Tuple.nth (♭ s) n ok' :: nil.
Proof.
  induction s; intros.
  - simpl in ok. inversion ok.
  - destruct a. simpl in ok, ok'.
    destruct n.
    + simpl. reflexivity.
    + simpl. apply IHs.
Defined.
  
Lemma schema_to_no_name_eq: ∀ s1 s2,
  s1 = s2 → ♭ s1 = ♭ s2.
Proof.
  intros. subst. reflexivity.
Defined.

Lemma schema_to_no_name_len: ∀ s,
  List.length (♭ s) = List.length s.
Proof.
  intros. induction s.
  - reflexivity.
  - destruct a. simpl. rewrite IHs. reflexivity.
Defined.


Fixpoint extract_as_cell_list s (r: relation s) : list nat :=
  match r with
  | nil => nil
  | cons t r' => (Tuple.extract_as_cell_id (♭ s) t) ++
                 (extract_as_cell_list s r')
  end.

(*
  @param s The schema, which is a list of attributes.
  @param r The relation, which is a list of tuples.
  @param n The index of the column to extract.
  @return The extracted column.

  [extract_column] is a function that takes a schema [s], a relation [r], and a natural number [n], and returns a list of elements that are at index [n] in each tuple in the relation.

  The function works by iterating over the relation. For each tuple in the relation, it extracts the element at index [n] using the [Tuple.extract_column] function and adds it to the result list. If the relation is empty, it returns an empty list.
*)
Fixpoint extract_column s (r: relation s) (n: nat):
  ∀ (ok: n < List.length s), relation ((nth s n ok) :: nil).
refine (
  match r with
  | nil => fun _ => nil
  | cons t r' => _
  end
).
  intros ok.
  assert (H': n < List.length (♭ s)).
  { rewrite schema_to_no_name_len. assumption. }
  pose (Tuple.nth_col_tuple (♭ s) n H' t) as cur.
  pose (extract_column s r' n ok) as rest.
  specialize nth_type_eq with (s := s) (n := n) (ok := ok) (ok' := H'). intros.
  rewrite <- H in cur.
  exact (cons cur rest). 
Defined.

(* Extracts a single column as a list. *)
Definition extract_column_as_list s (r: relation s) (n: nat):
  ∀ (ok: n < List.length s), list (type_to_coq_type (fst (nth s n ok)) * nat).
  intros.
  pose (extract_column s r n ok) as col.
  induction col.
  - exact nil.
  - destruct (nth s n ok). simpl in a.
    apply fst in a.
    exact (a :: IHcol).
Defined.

(*
  [cartesian_product_helper] is a recursive function that takes two schemas [s1] and [s2], a tuple [t] of type [Tuple.tuple (♭ s1)], and a relation [r] of type [relation s2]. It returns a relation of type [relation (s1 ++ s2)].

  The function recursively processes the relation [r] and performs a Cartesian product operation between the tuple [t] and each tuple in [r]. It concatenates the resulting tuples with the tuple [t] and returns the resulting relation.
*)
Fixpoint cartesian_product_helper (s1 s2: schema) (t: Tuple.tuple (♭ s1)) (r: relation s2) : relation (s1 ++ s2).
refine (
  match r with
  | nil => nil
  | cons t' r' => _
  end
).
  pose (Tuple.tuple_concat _ _ t t') as hd.
  pose (cartesian_product_helper s1 s2 t r') as tl.
  (* Tell Coq that the types are the same. *)
  rewrite <- schema_concat_eq in hd.
  exact (cons hd tl).
Defined.

(*
  @param s1 The first schema, which is a list of tuples where each tuple contains a type and a name.
  @param s2 The second schema, which is a list of tuples where each tuple contains a type and a name.
  @return A list of strings representing the names of the attributes that are in both schemas.

  [natural_join_list] is a function that takes two schemas [s1] and [s2], and returns a list of attribute names that are in both schemas.

  The function works by iterating over the first schema [s1]. For each attribute in [s1], it checks if the attribute's name is in the second schema [s2]. If it is, the attribute's name is not added to the result list and the function moves to the next attribute in [s1]. If it's not, the function moves to the next attribute in [s1] without adding anything to the result list.
*)
Fixpoint natural_join_list (s1 s2: schema): list nat :=
  match s1 with
  | nil => nil
  | (ty, name) :: s1' =>
    if List.existsb (fun x => (snd x) =? name) s2 then
      name :: natural_join_list s1' s2
    else natural_join_list s1' s2
  end.

(*
  This function computes the *cartesian* product of two relations.
*)
Definition relation_product s1 s2 (r1: relation s1) (r2: relation s2) : relation (s1 ++ s2).
  destruct s1; destruct s2.
  - exact nil.
  - exact nil.
  - exact nil.
  - induction r1.
    + exact nil.
    + exact (cartesian_product_helper _ _ a1 r2 ++ IHr1).
Defined.

Fixpoint extract_columns s (r: relation s) (l: list nat):
  ∀ (bounded: bounded_list s l), relation (ntypes s l bounded).
  destruct l; intros.
  - exact nil.
  - simpl in bounded. destruct bounded.
    pose (extract_column s r n l0) as cur.
    pose (extract_columns s r l b) as rest.
    simpl.
    exact (relation_product _ _ cur rest).
Defined.

(*
  This function `stitches` two relations together but does not perform cartesian product.

  For example, consider the following two relations:

  r1 = [[ 1, 2, 3 ]] :: [[ 4, 5, 6 ]] :: nil
  r2 = [[ 7, 8, 9 ]] :: [[ 10, 11, 12 ]] :: nil

  Then, the result of `relation_stitch r1 r2` is:

  [[ 1, 2, 3, 7, 8, 9 ]] :: [[ 4, 5, 6, 10, 11, 12 ]] :: nil
*)
Fixpoint relation_stitch s1 s2 (r1: relation s1) (r2: relation s2) : relation (s1 ++ s2).
  destruct s1; destruct s2.
  - exact nil.
  - exact nil.
  - exact nil.
  - induction r1; induction r2.
    + exact nil.
    + exact nil.
    + exact nil.
    + pose (Tuple.tuple_concat _ _ a1 a2) as hd.
      rewrite <- schema_concat_eq in hd.
      exact (cons hd (relation_stitch _ _ r1 r2)).
Defined.

Global Instance relation_proper:
  Proper (equiv ==> equiv) (relation).
Proof.
  repeat red. intros.
  induction x; destruct y.
  - reflexivity.
  - inversion H.
  - inversion H.
  - unfold relation. unfold fbag.
    simpl. destruct a, a0. simpl in *. inversion H. subst. auto.
Qed.

Global Instance relation_product_proper s1 s2:
  Proper (equiv ==> equiv ==> equiv) (@relation_product s1 s2).
Proof.
  repeat red. intros.
  induction s1; destruct s2.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - destruct a. destruct a0. 
    destruct x; destruct y.
    + simpl. auto.
    + inversion H.
    + inversion H.
    +
Admitted.

(*
  @param s A schema, which is a list of attributes.
  @param join_by A list of attribute names to join by.
  @param n The starting index.
  @return A list of tuples. Each tuple contains a natural number (the index) and an attribute from the schema that matches an attribute name in the [join_by] list.

  [join_list_to_index] is a function that takes a schema [s], a list of ids [join_by], and a natural number [n], and returns a list of tuples. Each tuple contains a natural number and an attribute.

  The function works by iterating over the schema. For each attribute in the schema, it checks if the attribute's name is in the [join_by] list. If it is, it adds a tuple containing the current index [n] and the attribute to the result list. If it's not, it simply moves to the next attribute, incrementing the index [n].
*)
Fixpoint join_list_to_index (s: schema) (join_by: list nat) (n: nat): list (nat * attribute) :=
  match s with
  | nil => nil
  | h :: t =>
    if List.existsb (fun x => x =? (snd h)) join_by then
      (n, h) :: join_list_to_index t join_by (n + 1)
    else join_list_to_index t join_by (n + 1)
  end.

Lemma join_list_to_index_nil1: ∀ s n,
  join_list_to_index s nil n = nil.
Proof.
  induction s.
  - reflexivity.
  - simpl. auto.
Qed.

Lemma join_list_to_index_nil2: ∀ join_by n,
  join_list_to_index nil join_by n = nil.
Proof.
  induction join_by.
  - auto.
  - intros. simpl. specialize IHjoin_by with (n := n + 1). auto.
Qed.
Hint Resolve join_list_to_index_nil1 join_list_to_index_nil2: core.

(*
  [join_list_to_index_bounded] is a lemma that states that for any list [s], join function [join_by], 
  indices [x] and [y], and a natural number [n], if the pair [(x, y)] is in the result of applying 
  [join_list_to_index] function on [s] with [join_by] and [n], then [x] is less than [n + length s].

  The proof of this lemma is done by induction on the list [s]. In the base case, when [s] is empty, 
  the assumption is contradicted. In the inductive case, we consider the head of the list [s] as a pair 
  [(a, b)]. If [a] is in the list [join_by], then we have two cases: either [(x, y)] is equal to [(a, b)], 
  in which case the inequality holds trivially, or [(x, y)] is in the rest of the list, in which case 
  we apply the induction hypothesis on the tail of the list. If [a] is not in the list [join_by], then 
  we also apply the induction hypothesis on the tail of the list.

  Finally, the inequality is proven using the [lia] tactic, which is able to handle linear integer 
  arithmetic.
*)
Lemma join_list_to_index_bounded: ∀ s join_by x n,
  List.In x (join_list_to_index s join_by n) → fst x < n + List.length s.
Proof.
  induction s.
  - intros. simpl in H. contradiction.
  - simpl in *. destruct a. intros. destruct x as [x y]. simpl in H.
    destruct (existsb (λ x, (x =? n)) join_by).
    + simpl in *. destruct H.
      * inversion H. subst. lia.
      * specialize IHs with (join_by := join_by) (x := (x, y)) (n := n0 + 1). apply IHs in H. simpl in *. lia.
    + specialize IHs with (join_by := join_by) (x := (x, y)) (n := n0 + 1). apply IHs in H. simpl in *. lia.
Qed.
Hint Resolve join_list_to_index_bounded: core.

Lemma join_list_to_index_bounded': ∀ index s join_by n,
  index = join_list_to_index s join_by n →
  ∀ x, List.In x index → fst x < n + List.length s.
Proof.
  intros. subst. apply join_list_to_index_bounded in H0. assumption.
Qed.
Hint Resolve join_list_to_index_bounded': core.

(*
  @param lhs The first list of tuples, where each tuple contains two natural numbers and an attribute.
  @param rhs The second list of tuples, where each tuple contains two natural numbers and an attribute.
  @return A list of tuples. Each tuple contains two pairs of natural numbers and an attribute.

  [find_common] is a function that takes two lists of tuples [lhs] and [rhs], and returns a list of tuples that are common to both lists.

  The function works by iterating over the first list [lhs]. For each tuple in [lhs], it checks if there is a tuple in the second list [rhs] that has the same attribute name and type. If there is, it adds a new tuple to the result list that contains the pair of natural numbers from both tuples and the common attribute. If there isn't, it simply moves to the next tuple in [lhs].
*)
Fixpoint find_common (lhs rhs: list (nat * attribute)): list ((nat * nat) * attribute) :=
  match lhs with
  | nil => nil
  | h :: t =>
    match find (fun x => andb (Nat.eqb (snd (snd h)) (snd (snd x)))
                              (type_matches (fst (snd h)) (fst (snd x)))) rhs with
    | Some x => ((fst h, fst x), snd h) :: find_common t rhs
    | None => find_common t rhs
    end
  end.

Lemma find_common_nil_r: ∀lhs, find_common lhs nil = nil.
Proof.
  intuition; induction lhs; auto.
Qed.

Lemma find_common_nil_l: ∀rhs, find_common nil rhs = nil.
Proof.
  intuition; induction rhs; auto. 
Qed.
Hint Resolve find_common_nil_l: core.

(*
  @param lhs A list of tuples, each containing two elements.
  @param rhs A list of tuples, each containing two elements.
  @param x The first element of the tuple from the common list.
  @param y The second element of the tuple from the common list.
  @param z The third element of the tuple from the common list.
  @return A proposition that asserts if a tuple (x, y, z) is in the common list of lhs and rhs, then
  (x, z) is in lhs and (y, z) is in rhs.

  This proposition asserts a condition about the relationship between two lists of tuples [lhs] and
  [rhs] and a common list derived from them. If a tuple (x, y, z) is in the common list, then the
  tuple (x, z) must be in the list [lhs] and the tuple (y, z) must be in the list [rhs].
*)
Lemma find_common_in_lhs_or_rhs: ∀ lhs rhs x y z,
  List.In (x, y, z) (find_common lhs rhs) →
  List.In (x, z) lhs ∧ List.In (y, z) rhs.
Proof.
  induction lhs.
  - simpl. intros. contradiction.
  - destruct rhs as [|a0 rhs].
    + rewrite find_common_nil_r. simpl. intros. contradiction.
    + simpl. split.
      * destruct a. destruct a0. simpl in H.
        destruct (((snd a =? snd a0) && type_matches (fst a) (fst a0))%bool).
        -- inversion H. inversion H0. left. reflexivity.
           right. apply IHlhs with (x := x) (y := y) (z := z) in H0. destruct H0. assumption.
        -- destruct (find (λ x, ((snd a =? snd (snd x)) &&
                     type_matches (fst a) (fst (snd x)))%bool) rhs).
           ++ inversion H. inversion H0. left. reflexivity.
              right. apply IHlhs with (x := x) (y := y) (z := z) in H0. destruct H0. assumption.
           ++ specialize IHlhs with (rhs := ((n0, a0) :: rhs)).
              apply IHlhs with (x := x) (y := y) (z := z) in H. destruct H. right. assumption.
      * destruct a. destruct a0. simpl in H.
        destruct (((snd a =? snd a0) && type_matches (fst a) (fst a0))%bool) eqn: H'.
          -- inversion H.
             ++ inversion H0. left. subst. apply Bool.andb_true_iff in H'. destruct H'.
                apply Nat.eqb_eq in H1. apply type_matches_eq in H2.
                apply pair_equal_spec. split; auto. apply injective_projections; auto.
             ++ apply IHlhs with (rhs := (n0, a0) :: rhs) (x := x) (y := y) (z := z). assumption.
          -- destruct (find (λ x, ((snd a =? snd (snd x)) &&
                       type_matches (fst a) (fst (snd x)))%bool) rhs) eqn: H''.
          (* Adding the hypothesis `H''` is important for the proof since we can
             reason about how `p` is obtained by which we substitute some terms.
          *)
            ** apply find_some in H''.  destruct H''.
               apply Bool.andb_true_iff in H1. destruct H1.
                apply Nat.eqb_eq in H1. apply type_matches_eq in H2.
                assert (a = (snd p)).
                { destruct a. destruct p. simpl. destruct p. apply pair_equal_spec. split; auto. }
                destruct p. subst. simpl in H. clear H1. clear H2.
                destruct H.
                --- right. inversion H. subst. assumption.
                --- apply IHlhs with (rhs := (n0, a0) :: rhs) (x := x) (y := y) (z := z). assumption.
            ** apply IHlhs with (rhs := (n0, a0) :: rhs) (x := x) (y := y) (z := z). assumption.
Defined.

(*
  [prop_find_common_holds] states that if for every attribute [a] in [lhs], [ℙ1 a] holds,
  and for every attribute [a] in [rhs], [ℙ2 a] holds, then for every triple [(x, y, z)]
  in the result of [find_common lhs rhs], either [ℙ1 (x, z)] or [ℙ2 (y, z)] holds.
*)
Lemma prop_find_common_holds: ∀ lhs rhs (ℙ1 ℙ2: (nat * attribute) → Prop),
  (∀ a, List.In a lhs → ℙ1 a) ∧ (∀ a, List.In a rhs → ℙ2 a) →
  ∀ x y z, List.In (x, y, z) (find_common lhs rhs) → ℙ1 (x, z) ∧ ℙ2 (y, z).
Proof.
  intros. destruct H.
  specialize find_common_in_lhs_or_rhs with (lhs := lhs) (rhs := rhs) (x := x) (y := y) (z := z).
  intros. apply H2 in H0. clear H2.
  destruct H0. split.
  - specialize H with (a := (x, z)). apply H. assumption.
  - specialize H1 with (a := (y, z)). apply H1. assumption.
Defined.

Lemma find_common_bounded: ∀ s1 s2 n join_by lhs rhs ℓ x y z,
  lhs = join_list_to_index s1 join_by n → rhs = join_list_to_index s2 join_by n →
  List.In (x, y, z) ℓ → sublist _ ℓ (find_common lhs rhs) → 
  x < n + List.length s1 ∧ y < n + List.length s2.
Proof.
  intros. subst.
  unfold sublist in H2.
  specialize H2 with (a := (x, y, z)). apply H2 in H1.
  specialize prop_find_common_holds with
    (lhs := (join_list_to_index s1 join_by n))
    (rhs :=  (join_list_to_index s2 join_by n))
    (ℙ1 := fun x => fst x < n + List.length s1)
    (ℙ2 := fun x => fst x < n + List.length s2).
  specialize join_list_to_index_bounded with (s := s1) (join_by := join_by) (n := n).
  specialize join_list_to_index_bounded with (s := s2) (join_by := join_by) (n := n).
  intros.
  simpl in *. pose (H3 (conj H0 H)).
  specialize a with (x := x) (y := y) (z := z).
  apply a. assumption.
Defined.

Definition check_value s1 s2
  (common_join_list: list ((nat * nat) * attribute)) (join_by: list nat)
  (proof: ∀ elem, List.In elem common_join_list →
    List.In elem (find_common (join_list_to_index s1 join_by 0) 
      (join_list_to_index s2 join_by 0)))
  (lhs: Tuple.tuple (♭ s1)) (rhs: Tuple.tuple (♭ s2)): bool.
refine (
  (fix check_value common_join_list proof :=
  match common_join_list with
  | nil => true
  | _ =>
    _
  end) common_join_list proof
).
  destruct common_join_list as [|h t] eqn: H.
  - exact true.
  - destruct h as [(n1, n2) attr].
  specialize find_common_bounded with (s1 := s1) (s2 := s2) (n := 0) (join_by := join_by)
    (lhs := (join_list_to_index s1 join_by 0)) (rhs := (join_list_to_index s2 join_by 0))
    (x := n1) (y := n2) (z := attr). unfold sublist.
  intros.
  simpl in H. 
  (* This is to obtain the proof that indices are bounded. *)
  assert (n1 < Datatypes.length s1 ∧ n2 < Datatypes.length s2).
    { apply (H0 common_join_list); auto. subst. apply in_eq. rewrite H. auto. }
  destruct H1 as [extract1 extract2].
  (* Preserves length. *)
  rewrite <- schema_to_no_name_length in extract1, extract2.
  (* We now obtain the values from two tuples. *)
  pose (Tuple.nth_col_tuple _ n1 extract1 lhs) as tp1.
  pose (Tuple.nth_col_tuple _ n2 extract2 rhs) as tp2.
  simpl in tp1, tp2. repeat apply fst in tp1, tp2.
  (* Perform case analysis on types and equality. *)
  destruct (Tuple.nth (♭ s1) n1 extract1);
  destruct (Tuple.nth (♭ s2) n2 extract2); simpl in tp1, tp2.
  + destruct (tp1 =? tp2) eqn: H'.
    * specialize check_value with (common_join_list := t).
      apply check_value.
      intros. specialize proof with elem. apply proof.
      apply (in_cons (n1, n2, attr)) in H1. assumption.
    * exact false.
  + exact false. (* Type mismatch. *)
  + exact false. (* Type mismatch. *)
  + exact false. (* Type mismatch. *)
  + destruct (Bool.eqb tp1 tp2) eqn: H'.
    * specialize check_value with (common_join_list := t).
      apply check_value.
      intros. specialize proof with elem. apply proof.
      apply (in_cons (n1, n2, attr)) in H1. assumption.
    * exact false.
  + exact false. (* Type mismatch. *)
  + exact false. (* Type mismatch. *)
  + exact false. (* Type mismatch. *)
  + destruct (String.eqb tp1 tp2) eqn: H'.
    * specialize check_value with (common_join_list := t).
      apply check_value.
      intros. specialize proof with elem. apply proof.
      apply (in_cons (n1, n2, attr)) in H1. assumption.
    * exact false.
Defined.

Fixpoint remove_common (s: schema) (common: list nat) (n: nat): schema :=
  match s with
  | nil => nil
  | h :: t =>
    if List.existsb (fun x => x =? n) common then
      remove_common t common (n + 1)
    else h :: remove_common t common (n + 1)
  end.

Fixpoint get_common (s: schema) (common: list nat) (n: nat): schema :=
  match s with
  | nil => nil
  | h :: t =>
    if List.existsb (fun x => x =? n) common then
      h :: get_common t common (n + 1)
    else get_common t common (n + 1)
  end.

Lemma remove_common_nil: ∀ s n, remove_common s nil n = s.
Proof.
  induction s.
  - reflexivity.
  - intros. simpl. destruct (existsb (λ x : nat, (x =? n)%nat) nil) eqn: H.
    + simpl in H. inversion H.
    + simpl in H. rewrite IHs. reflexivity.
Qed.

Lemma get_common_nil: ∀ s n, get_common s nil n = nil.
Proof.
  induction s.
  - reflexivity.
  - intros. simpl. destruct (existsb (λ x : nat, (x =? n)%nat) nil) eqn: H.
    + simpl in H. inversion H.
    + simpl in H. rewrite IHs. reflexivity.
Qed.

(*
  This function computes the schema of the joined result of two relations provided a join list.
*)
Definition output_schema_join_by s1 s2 (join_by: list nat): schema :=
  let lhs := join_list_to_index s1 join_by 0 in
    let rhs := join_list_to_index s2 join_by 0 in
      let common_join_list := find_common lhs rhs in
        let index_lhs := List.map (fun x => fst (fst x)) common_join_list in
          let index_rhs := List.map (fun x => snd (fst x)) common_join_list in
            (remove_common s1 index_lhs 0) ++
            (get_common s1 index_lhs 0) ++
            (remove_common s2 index_rhs 0).

(*
  This function removes the common columns from the two schemas specified by the `common`
  list that contains the indices of the common columns that need to be removed.
*)
Definition remove_common_part s (tp: Tuple.tuple (♭ s)) (n: nat)
 (common: list nat): Tuple.tuple (♭ (remove_common s common n)).
refine (
  (fix remove_common_part s tp n :=
    (* Pose s = s' for the ease of knowing the structure of `s`. *)
    match s as s' return s = s' → Tuple.tuple (♭ (remove_common s common n)) with
    | nil => fun _ => _ 
    | h :: t => _
    end eq_refl) s tp n
).
  - subst. exact tt.
  - intros. subst.
    destruct h. simpl in *. specialize remove_common_part with (s := t).
    destruct tp. pose (remove_common_part t0) as rest.
    destruct (existsb (λ x : nat, (x =? n)%nat) common).
    + exact (rest (n + 1)).
    + simpl. exact (p, rest (n + 1)).
Defined.

Definition get_common_part s (tp: Tuple.tuple (♭ s)) (n: nat)
 (common: list nat): Tuple.tuple (♭ (get_common s common n)).
refine (
  (fix get_common_part s tp n :=
    (* Pose s = s' for the ease of knowing the structure of `s`. *)
    match s as s' return s = s' → Tuple.tuple (♭ (get_common s common n)) with
    | nil => fun _ => _ 
    | h :: t => _
    end eq_refl) s tp n
).
  - subst. exact tt.
  - intros. subst.
    destruct h. simpl in *. specialize get_common_part with (s := t).
    destruct tp. pose (get_common_part t0) as rest.
    destruct (existsb (λ x : nat, (x =? n)%nat) common).
    + simpl. exact (p, rest (n + 1)).
    + exact (rest (n + 1)).
Defined.

Lemma join_type_eq: ∀ s1 s2 join_by lhs rhs index_lhs index_rhs common_join_list,
  lhs = join_list_to_index s1 join_by 0 → rhs = join_list_to_index s2 join_by 0 →
  common_join_list = find_common lhs rhs →
  index_lhs = List.map (fun x => fst (fst x)) common_join_list →
  index_rhs = List.map (fun x => snd (fst x)) common_join_list →
  (♭ (remove_common s1 index_lhs 0) ++
  ♭ (get_common s1 index_lhs 0) ++
  ♭ (remove_common s2 index_rhs 0)) =
  ♭ (output_schema_join_by s1 s2 join_by).
Proof.
  intros. subst.
  repeat rewrite app_assoc'. repeat rewrite <- schema_concat_eq. apply schema_to_no_name_eq.
  unfold output_schema_join_by. rewrite <- app_assoc'. reflexivity.
Defined.

(*
  @param s1 The schema of the left-hand side relation.
  @param s2 The schema of the right-hand side relation.
  @param join_by The list of column names to join by.
  @param lhs The left-hand side tuple.
  @param rhs The right-hand side tuple.
  @return An optional tuple containing the resulting tuple after the join operation and a list of triples where
          the first element is the id of the cell joined on the left-hand side, the second element is the id of
          the cell joined on the right-hand side, and the third element is the merged new id.

  The `tuple_concat_by` function performs a join operation on two tuples `lhs` and `rhs` based on the list of column
  names `join_by`. The schemas of the tuples are `s1` and `s2` respectively. If the join operation can be successfully
  applied, the function returns `Some` with a tuple containing the resulting tuple after the join operation and two
  lists of natural numbers. The two lists of natural numbers represent the indices of the columns from `lhs` and `rhs`
  that are included in the resulting tuple. If the join operation cannot be applied (for example, if a column name in 
  join_by` does not exist in either `lhs` or `rhs`), the function returns `None`.
*)
Definition tuple_concat_by s1 s2 join_by
  (lhs: Tuple.tuple (schema_to_no_name s1))
  (rhs: Tuple.tuple (schema_to_no_name s2))
  : option (Tuple.tuple (schema_to_no_name (output_schema_join_by s1 s2 join_by)) *
           (list nat * list nat * list nat)).
  destruct s1; destruct s2.
  - exact None.
  - exact None.
  - exact None.
  - (*
      Concatenating two tuples that share the same value on columns in the given join list.
      If the two tuples do not share the same value on columns in the given join list, then
      return `None`; otherwise, return `Some` of the concatenated tuple.

      To this end, we need to:
      1. Find the indices of the columns in the join list in the two tuples.
      2. Check if the values of the columns in the join list are the same.
      3. If the values of the columns in the join list are the same, then concatenate the two tuples.
    *)

    pose (lhs_join_list := join_list_to_index (a :: s1) join_by 0).
    pose (rhs_join_list := join_list_to_index (a0 :: s2) join_by 0).
    pose (common_join_list := find_common lhs_join_list rhs_join_list).

    (* Check value. *)
    pose (check_value (a :: s1) (a0 :: s2) common_join_list join_by) as check_value.
    assert (∀ elem : nat * nat * attribute, In elem common_join_list →
      In elem (find_common (join_list_to_index (a :: s1) join_by 0)
                           (join_list_to_index (a0 :: s2) join_by 0)))
                           by auto.
    specialize check_value with (proof := H) (lhs := lhs) (rhs := rhs).

    (* Check if the values of the columns in the join list are the same. *)
    refine (
      match check_value with
      | false => None
      | true => _
      end
    ).
  
    (* Now we need to join the two tuples. *)
    pose (index_lhs := List.map (fun x => fst (fst x)) common_join_list).
    pose (index_rhs := List.map (fun x => snd (fst x)) common_join_list).

    (* In the next step, we need to:
       1. Remove unneeded columns of `rhs`.
       2. Concatenate `lhs` and `rhs`.
       3. Prove that the output types are equivalent.

       Note that since tuples are dependently typed, we may also need helper functions
       to determine the output type.
    *)
    pose (remove_common_part _ lhs 0 index_lhs) as lhs'.
    pose (remove_common_part _ rhs 0 index_rhs) as rhs'.
    pose (get_common_part _ lhs 0 index_lhs) as comlhs.
    pose (get_common_part _ rhs 0 index_rhs) as comrhs.

    pose (new_id stream 114) as new_id.
    pose (Tuple.inject_new_id _ comlhs new_id) as com.
    pose (Tuple.extract_as_cell_id _ com) as comid.

    (* Find the shared part. *)
    pose (Tuple.tuple_concat _ _ lhs' com) as tmp.
    pose (Tuple.tuple_concat _ _ tmp rhs') as result.
    specialize join_type_eq with
      (s1 := (a :: s1)) (s2 := (a0 :: s2)) (join_by := join_by)
      (lhs := lhs_join_list) (rhs := rhs_join_list)
      (index_lhs := index_lhs) (index_rhs := index_rhs) (common_join_list := common_join_list).
    intros.
    assert (schema_to_no_name (remove_common (a :: s1) index_lhs 0) ++
            schema_to_no_name (get_common (a :: s1) index_lhs 0) ++
            schema_to_no_name (remove_common (a0 :: s2) index_rhs 0) =
    schema_to_no_name (output_schema_join_by (a :: s1) (a0 :: s2) join_by))
      by auto.
    rewrite <- H1. rewrite app_assoc'.

    pose (Tuple.tuple_as_cell_ids _ comlhs) as cell_id_lhs.
    pose (Tuple.tuple_as_cell_ids _ comrhs) as cell_id_rhs.

    exact (Some (result, (cell_id_lhs, cell_id_rhs, comid))).
Defined.

Inductive join_policy_and_trace:
  list nat → list nat → list nat →
  Policy.context → Policy.context →
  trace → trace →
  option (Policy.context * trace) → Prop :=
  | join_policy_and_trace_nil_l: ∀ l com Γ1 Γ2 tr1 tr2,
      join_policy_and_trace nil l com Γ1 Γ2 tr1 tr2 (Some ((merge_env Γ1 Γ2), merge_env tr1 tr2))
  | join_policy_and_trace_nil_r: ∀ l com Γ1 Γ2 tr1 tr2,
      join_policy_and_trace l nil com Γ1 Γ2 tr1 tr2 (Some ((merge_env Γ1 Γ2), merge_env tr1 tr2))
  | join_policy_and_trace_no_com: ∀ l1 l2 Γ1 Γ2 tr1 tr2,
      join_policy_and_trace l1 l2 nil Γ1 Γ2 tr1 tr2 (Some ((merge_env Γ1 Γ2), merge_env tr1 tr2))
  | join_policy_and_trace_cons_err: ∀ l1 l2 com Γ1 Γ2 tr1 tr2 hd1 hd2 tl1 tl2,
      l1 = hd1 :: tl1 →
      l2 = hd2 :: tl2 →
      label_lookup Γ1 hd1 = None ∨ label_lookup Γ2 hd2 = None ∨
      label_lookup tr1 hd1 = None ∨ label_lookup tr2 hd2 = None →
      join_policy_and_trace l1 l2 com Γ1 Γ2 tr1 tr2 None
  | join_policy_and_trace_cons_ok:
      ∀ l1 l2 com Γ1 Γ2 Γ tr1 tr2 tr
        hd1 hd2 hd3 hd4 hd5
        tl1 tl2 tl3 tl4 tl5
        p1 p2 pjoin
        tr1' tr2'
        ,
      l1 = hd1 :: tl1 →
      l2 = hd2 :: tl2 →
      com = hd3 :: tl3 →
      tr1 = hd4 :: tl4 →
      tr2 = hd5 :: tl5 →
      label_lookup Γ1 hd1 = Some p1 →
      label_lookup Γ2 hd2 = Some p2 →
      label_lookup tr1 hd1 = Some tr1' →
      label_lookup tr2 hd2 = Some tr2' →
      p1 ∪ p2 = pjoin →
      join_policy_and_trace tl1 tl2 tl3 Γ1 Γ2 tl4 tl5 (Some (Γ, tr)) →
      let tr_join := TrBranch prov_join pjoin tr1' tr2' in
      join_policy_and_trace l1 l2 com Γ1 Γ2 tr1 tr2 (Some ((hd3, pjoin) :: Γ, (hd3, tr_join) :: tr))
.

(* Coq cannot do "nested loop"; this performs one-time pass over rhs. *)
Inductive relation_join_by_prv_helper: ∀ s1 s2 join_by, Tuple.tuple (♭ s1) → relation s2 →
  Policy.context → Policy.context → budget → budget → trace → trace →
  option (relation (output_schema_join_by s1 s2 join_by) * Policy.context * budget * trace) → Prop :=
  | E_JoinEmpty: ∀ s1 s2 join_by t Γ1 Γ2 Γ_out ε1 ε2 ε_out p1 p2 p_out,
      Γ_out = merge_env Γ1 Γ2 →
      ε_out = calculate_budget ε1 ε2 →
      p_out = merge_env p1 p2 →
      relation_join_by_prv_helper s1 s2 join_by t nil Γ1 Γ2 ε1 ε2 p1 p2
      (Some (nil, Γ_out, ε_out, p_out))
  | E_JoinConsError1: ∀ s1 s2 join_by t1 t2 r tl Γ1 Γ2 ε1 ε2 p1 p2,
      r = t2 :: tl →
      None = tuple_concat_by s1 s2 join_by t1 t2 →
      relation_join_by_prv_helper s1 s2 join_by t1 r Γ1 Γ2 ε1 ε2 p1 p2 None
  | E_JoinConsError2: ∀ s1 s2 join_by t1 t2 t' r tl Γ1 Γ2 ε1 ε2 p1 p2
                        index_lhs index_rhs comid,
      r = t2 :: tl →
      Some(t', (index_lhs, index_rhs, comid)) = tuple_concat_by s1 s2 join_by t1 t2 →
      join_policy_and_trace index_lhs index_rhs comid Γ1 Γ2 p1 p2 None →
      relation_join_by_prv_helper s1 s2 join_by t1 r Γ1 Γ2 ε1 ε2 p1 p2 None
  | E_JoinConsError3: ∀ s1 s2 join_by t1 t2 t' r tl Γ1 Γ2
                    Γ_merged
                    ε1 ε2 ε_merged
                    p1 p2 p_merged
                    index_lhs index_rhs comid,
      r = t2 :: tl →
      Some(t', (index_lhs, index_rhs, comid)) = tuple_concat_by s1 s2 join_by t1 t2 →
      join_policy_and_trace index_lhs index_rhs comid Γ1 Γ2 p1 p2 (Some (Γ_merged, p_merged)) →
      ε_merged = calculate_budget ε1 ε2 →
      relation_join_by_prv_helper s1 s2 join_by t1 tl Γ1 Γ2 ε1 ε2 p1 p2 None →
      relation_join_by_prv_helper s1 s2 join_by t1 r Γ1 Γ2 ε1 ε2 p1 p2 None
  | E_JoinConsOk: ∀ s1 s2 join_by t1 t2 t' r r_cons tl Γ1 Γ2
                    Γ_merged Γ_cons Γ_out
                    ε1 ε2 ε_merged ε_cons ε_out
                    p1 p2 p_merged p_cons p_out
                    index_lhs index_rhs comid,
      r = t2 :: tl →
      Some(t', (index_lhs, index_rhs, comid)) = tuple_concat_by s1 s2 join_by t1 t2 →
      join_policy_and_trace index_lhs index_rhs comid Γ1 Γ2 p1 p2 (Some (Γ_merged, p_merged)) →
      ε_merged = calculate_budget ε1 ε2 →
      relation_join_by_prv_helper s1 s2 join_by t1 tl Γ1 Γ2 ε1 ε2 p1 p2
      (Some (r_cons, Γ_cons, ε_cons, p_cons)) →
      Γ_out = merge_env Γ_merged Γ_cons →
      ε_out = calculate_budget ε_merged ε_cons →
      p_out = merge_env p_merged p_cons →
      relation_join_by_prv_helper s1 s2 join_by t1 r Γ1 Γ2 ε1 ε2 p1 p2
      (Some (t' :: r_cons, Γ_out, ε_out, p_out))
.

Inductive relation_join_by_prv: ∀ s1 s2 join_by, relation s1 → relation s2 →
  Policy.context → Policy.context → budget → budget → trace → trace →
  option (relation (output_schema_join_by s1 s2 join_by) * Policy.context * budget * trace) → Prop :=
  | E_RelationJoinSchemaNil: ∀ s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2,
      s1 = nil ∨ s2 = nil →
      relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2
      (Some (nil, nil, O, nil))
  | E_RelationJoinNil: ∀ s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2,
      r1 = nil ∨ r2 = nil →
      relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2
      (Some (nil, nil, O, nil))
  | E_RelationJoinConsErr: ∀ s1 s2 join_by r1 r2 hd tl
                            Γ1 Γ2
                            (* TODO: Join budget? *)
                            ε1 ε2
                            p1 p2, 
      s1 ≠ nil ∧ s2 ≠ nil →
      r1 = hd :: tl →
      relation_join_by_prv_helper s1 s2 join_by hd r2 Γ1 Γ2 ε1 ε2 p1 p2 None ∨
      relation_join_by_prv s1 s2 join_by tl r2 Γ1 Γ2 ε1 ε2 p1 p2 None →
      relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2 None
  | E_RelationJoinConsOk: ∀ s1 s2 join_by r1 r2 r_hd r_cons r_out hd tl
                            Γ1 Γ2 Γ_hd Γ_cons Γ_out
                            (* TODO: Join budget? *)
                            ε1 ε2 ε_hd ε_cons ε_out
                            p1 p2 p_hd p_cons p_out,
      s1 ≠ nil ∧ s2 ≠ nil →
      r1 = hd :: tl →
      relation_join_by_prv_helper s1 s2 join_by hd r2 Γ1 Γ2 ε1 ε2 p1 p2 (Some (r_hd, Γ_hd, ε_hd, p_hd)) →
      relation_join_by_prv s1 s2 join_by tl r2 Γ1 Γ2 ε1 ε2 p1 p2 (Some (r_cons, Γ_cons, ε_cons, p_cons)) →
      Γ_out = merge_env Γ_hd Γ_cons →
      p_out = merge_env p_hd p_cons →
      ε_out = calculate_budget ε_hd ε_cons →
      r_out = r_hd ++ r_cons →
      relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2 (Some (r_out, Γ_out, ε_out, p_out))
.

Lemma relation_join_by_prv_helper_terminate: ∀ s1 s2 join_by t1 t2 Γ1 Γ2 ε1 ε2 p1 p2,
  ∃ res, relation_join_by_prv_helper s1 s2 join_by t1 t2 Γ1 Γ2 ε1 ε2 p1 p2 res.
Proof.
Admitted.

Lemma relation_join_by_prv_terminate: ∀ s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2, ∃ res,
  relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2 res.
Proof.
  intros. destruct s1; destruct s2.
  - exists (Some (nil, nil, O, nil)). constructor; intuition.
  - exists (Some (nil, nil, O, nil)). constructor; intuition.
  - exists (Some (nil, nil, O, nil)). constructor; intuition.
  - induction r1; destruct r2.
    + exists (Some (nil, nil, O, nil)). apply E_RelationJoinNil. intuition.
    + exists (Some (nil, nil, O, nil)). apply E_RelationJoinNil. intuition.
    + exists (Some (nil, nil, O, nil)). apply E_RelationJoinNil. intuition.
    + destruct (relation_join_by_prv_helper_terminate (a :: s1) (a0 :: s2) join_by a1 (t :: r2) Γ1 Γ2 ε1 ε2 p1 p2).
      destruct IHr1.
      destruct x; destruct x0.
      * destruct p as[ [ [ r_hd Γ_hd ] β_hd ] p_hd ].
        destruct p0 as[ [ [ r_cons Γ_cons ] β_cons ] p_cons ].
        pose (merge_env Γ_hd Γ_cons) as Γ_out.
        pose (merge_env p_hd p_cons) as p_out.
        pose (calculate_budget β_hd β_cons) as β_out.
        exists (Some (r_hd ++ r_cons, Γ_out, β_out, p_out)).
        eapply E_RelationJoinConsOk; intuition; try discriminate; auto.
      * exists None. econstructor; intuition; try discriminate; auto.
      * exists None. econstructor; intuition; try discriminate; auto.
      * exists None. econstructor; intuition; try discriminate; auto.
Qed.

Lemma relation_join_by_prv_deterministic: ∀ s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2 res1 res2,
  relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2 res1 →
  relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 ε1 ε2 p1 p2 res2 →
  res1 = res2.
Proof.
Admitted.

Fixpoint inject_id_tuple s (t: (Tuple.tuple_np (♭ s))) (p: Policy.policy_store (♭ s)) (id_start: nat)
  : (Tuple.tuple (♭ s) * Policy.context).
refine (
  match s as s' return s = s' → (Tuple.tuple (♭ s) * Policy.context) with
    | nil => fun _ => _
    | h :: t' => fun _ => _
  end eq_refl
). 
  - subst. simpl. exact (tt, nil).
  - specialize inject_id_tuple with (s := t').
    subst. destruct h. simpl in *.
    pose (inject_id_tuple (snd t) (snd p) (S id_start)) as t_next.
    destruct t_next as [t_next Γ].
    exact ((fst t), id_start, t_next, ((id_start, (fst p)) :: Γ)).
Defined.

(*
  @param s The schema of the relation.
  @param r A list of tuples and their associated policy stores. Each tuple corresponds to a row in the relation.
  @param id_start The starting identifier for the injection of identifiers into the relation.
  @return A tuple containing the relation with injected identifiers and the policy context.

  The `inject_id_helper` function injects identifiers into a relation. The relation is represented as a list of
  tuples `r`, where each tuple corresponds to a row in the relation and is associated with a policy store. The
  identifiers are injected starting with the identifier `id_start`. The function returns a tuple containing the
  relation with injected identifiers and the policy context.
*)
Fixpoint inject_id_helper s (r: list (db_entry s)) (id_start: nat)
  : (relation s * Policy.context) :=
  match r with
    | nil => (nil, nil)
    | (h, p) :: t =>
        let (r, Γ) := inject_id_tuple _ h p (S id_start) in
        match inject_id_helper s t (id_start + List.length s) with
        | (r', Γ') => (r :: r', Γ ++ Γ')
        end
  end.

Fixpoint database_get_contexts (db: database) (idx: nat)
  : option (relation_wrapped * Policy.context * trace * budget) :=
  match db with
    | database_empty => None
    | database_relation s r β db' =>
        if Nat.eqb idx O then
                match inject_id_helper s r 10 with
                | (r', Γ') =>
                  let p := empty_trace_from_pctx Γ' in
                    Some (RelationWrapped s r', Γ', p, β)
                end
        else database_get_contexts db' (idx - 1)
  end.
