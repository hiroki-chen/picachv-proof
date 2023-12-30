Require Import Nat.
Require Import List.
Require Import RelationClasses.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import String.
Require Import Lia.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import ordering.
Require Import finite_bags.
Require Import types.

(** 
  [relation_np] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.
  Note: this will make tuple ignorant of the policy.
  @param s   The schema of the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation_np (s: schema) := fbag (Tuple.tuple_np (schema_to_no_name s)).

(** 
  [relation] is a function that takes a tuple type [ty] as an argument and returns a finite bag (fbag) of tuples of type [ty]. 
  This function is used to define a relation in the context of a database or a similar data structure where relations are represented as collections of tuples.

  @param s   The schema of the relation.
  @return    A finite bag (fbag) of tuples of type [ty].
*)
Definition relation (s: schema) := fbag (Tuple.tuple (schema_to_no_name s)).

Lemma schema_concat_eq: ∀ s1 s2,
  schema_to_no_name (s1 ++ s2) = schema_to_no_name s1 ++ schema_to_no_name s2.
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

(**
  [inject_tuple_id_relation] is a function that takes a tuple type [ty], a relation [r] of type [relation_np ty] and an id [id] as arguments and returns a relation of type [relation ty].
  This function is used to inject an id into a relation. This is useful when we want to inject a policy into a relation.
  @param s   The schema of the relation that we want to inject an id into.
  @param r   The relation that we want to inject an id into.
  @param id  The id that we want to inject into the relation.
  @return    A relation of type [relation ty].
*)
Fixpoint inject_tuple_id_relation
  (s: schema)
  (r: relation_np s)
  (id: nat)
: relation s :=
  match r with
  | nil => nil
  | cons t r' =>
  cons (Tuple.inject_tuple_id (schema_to_no_name s) t id)
       (inject_tuple_id_relation s r' (id + List.length s))
  end.

Fixpoint extract_as_cell_list s (r: relation s) : list nat :=
  match r with
  | nil => nil
  | cons t r' => (Tuple.extract_as_cell_id (schema_to_no_name s) t) ++
                 (extract_as_cell_list s r')
  end.

Fixpoint cartesian_product_helper (s1 s2: schema) (t: Tuple.tuple (schema_to_no_name s1)) (r: relation s2) : relation (s1 ++ s2).
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

Fixpoint natural_join_list (s1 s2: schema): list string :=
  match s1 with
  | nil => nil
  | (ty, name) :: s1' =>
    if List.existsb (fun x => (snd x) =? name)%string s2 then
      natural_join_list s1' s2
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
  This `join_by` argument is a list of natural numbers that specifies which columns to join on.
  This function will do a pass on `join_by` by looking up the column names in the schema and
  removing the column names that do not exist in one of the schemas to be joined.
*)
Fixpoint output_schema_join_by_helper (s1 s2: schema) (join_by: list string): schema :=
  match join_by with
  | nil => nil
  | h :: t =>
      match (find (fun x => (snd x) =? h)%string s1), (find (fun x => (snd x) =? h)%string s2) with
      | Some (ty1, _), Some (ty2, _) =>
        if type_matches ty1 ty2 then
          (ty1, h) :: output_schema_join_by_helper s1 s2 t
        else output_schema_join_by_helper s1 s2 t
      | _, _ => output_schema_join_by_helper s1 s2 t
      end
  end.

(*
  This function computes the schema of the joined result of two relations provided a join list.
*)
Definition output_schema_join_by s1 s2 (join_by: list string): schema :=
  let common_col := output_schema_join_by_helper s1 s2 join_by in
    let s1' := List.filter (fun x => negb (List.existsb (fun y => (snd x) =? y)%string join_by)) s1 in
      let s2' := List.filter (fun x => negb (List.existsb (fun y => (snd x) =? y)%string join_by)) s2 in
        s1' ++ common_col ++ s2'.

Fixpoint join_list_to_index (s: schema) (join_by: list string) (n: nat): list (nat * Attribute) :=
  match s with
  | nil => nil
  | h :: t =>
    if List.existsb (fun x => x =? (snd h))%string join_by then
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

Lemma join_list_to_index_bounded: ∀ s join_by x y n,
  List.In (x, y) (join_list_to_index s join_by n) → x < n + List.length s.
Proof.
  induction s.
  - intros. simpl in H. contradiction.
  - simpl in *. destruct a. intros. simpl in H.
    destruct (existsb (λ x : string, (x =? s0)%string) join_by).
    + simpl in *. destruct H.
      * inversion H. subst. lia.
      * specialize IHs with (join_by := join_by) (x := x) (n := n + 1). apply IHs in H. lia.
    + specialize IHs with (join_by := join_by) (x := x) (n := n + 1). apply IHs in H. lia.
Qed.

Lemma join_list_to_index_bounded': ∀ index s join_by n,
  index = join_list_to_index s join_by n →
  ∀ x y, List.In (x, y) index → x < n + List.length s.
Proof.
  intros. subst. apply join_list_to_index_bounded in H0. assumption.
Qed.

Fixpoint find_common (lhs rhs: list (nat * Attribute)): list ((nat * nat) * Attribute) :=
  match lhs with
  | nil => nil
  | h :: t =>
    match find (fun x => String.eqb (snd (snd h)) (snd (snd x))) rhs with
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

Lemma find_common_bounded: ∀ s1 s2 n join_by lhs rhs ℓ x y z,
  lhs = join_list_to_index s1 join_by n → rhs = join_list_to_index s2 join_by n →
  List.In (x, y, z) ℓ → (∀ elem, List.In elem ℓ → List.In elem (find_common lhs rhs)) →
  x < n + List.length s1 ∧ y < n + List.length s2.
(* Proof.
  induction s1.
  - intros. subst. simpl in *. contradiction.
  - induction s2.
    + simpl in *. intuition.
      * subst. destruct a. simpl in *. destruct (existsb (λ x : string, (x =? s)%string) join_by).
        -- simpl in *. rewrite find_common_nil_r in H1. inversion H1.
        -- simpl in *. rewrite find_common_nil_r in H1. inversion H1.
      * subst. destruct a. simpl in *. destruct (existsb (λ x : string, (x =? s)%string) join_by).
        -- simpl in *. rewrite find_common_nil_r in H1. inversion H1.
        -- simpl in *. rewrite find_common_nil_r in H1. inversion H1.
    + intros. subst. simpl in H1.
      destruct (existsb (λ x : string, (x =? snd a)%string) join_by);
      destruct (existsb (λ x : string, (x =? snd a0)%string) join_by); destruct a; destruct a0;
      simpl in *; destruct ((s =? s0)%string); destruct (existsb (λ x0 : string, (x0 =? s)%string) join_by).
      * simpl in *. *)
Admitted.

Definition check_value s1 s2
  (common_join_list: list ((nat * nat) * Attribute)) (join_by: list string)
  (proof: ∀ elem, List.In elem common_join_list →
    List.In elem (find_common (join_list_to_index s1 join_by 0) 
      (join_list_to_index s2 join_by 0)))
  (lhs: Tuple.tuple (schema_to_no_name s1)) (rhs: Tuple.tuple (schema_to_no_name s2)): bool.
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
    (x := n1) (y := n2) (z := attr).
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
  destruct (Tuple.nth (schema_to_no_name s1) n1 extract1);
  destruct (Tuple.nth (schema_to_no_name s2) n2 extract2); simpl in tp1, tp2.
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

Lemma remove_common_nil: ∀ s n, remove_common s nil n = s.
Proof.
  induction s.
  - reflexivity.
  - intros. simpl. destruct (existsb (λ x : nat, (x =? n)%nat) nil) eqn: H.
    + simpl in H. inversion H.
    + simpl in H. rewrite IHs. reflexivity.
Qed.

(*
  This function removes the common columns from the two schemas specified by the `common`
  list that contains the indices of the common columns that need to be removed.
*)
Definition remove_common_part s (tp: Tuple.tuple (schema_to_no_name s)) (n: nat)
 (common: list nat): Tuple.tuple (schema_to_no_name (remove_common s common n)).
refine (
  (fix remove_common_part s tp n :=
    (* Pose s = s' for the ease of knowing the structure of `s`. *)
    match s as s' return s = s' → Tuple.tuple (schema_to_no_name (remove_common s common n)) with
    | nil => fun _ => _ 
    | h :: t => _
    end eq_refl) s tp n
).
  - subst. exact tt.
  - intros. subst.
    destruct h. simpl in *. specialize remove_common_part with (s := t).
    destruct tp. pose (remove_common_part t0) as rest.
    destruct (existsb (λ x : nat, (x =? n)%nat) common) eqn: H.
    + exact (rest (n + 1)).
    + simpl. exact (p, rest (n + 1)).
Defined.

Lemma join_type_eq: ∀s1 s2 join_by lhs rhs index_lhs index_rhs common_join_list,
  lhs = join_list_to_index s1 join_by 0 → rhs = join_list_to_index s2 join_by 0 → common_join_list = find_common lhs rhs →
    index_lhs = List.map (fun x => fst (fst x)) common_join_list →
    index_rhs = List.map (fun x => snd (fst x)) common_join_list →
    schema_to_no_name (remove_common s1 index_lhs 0) ++ schema_to_no_name (remove_common s2 index_rhs 0) =
    schema_to_no_name (output_schema_join_by s1 s2 join_by).
Admitted.

(* Useful for joining two databases with a join list. *)
Definition tuple_concat_by s1 s2 join_by
  (lhs: Tuple.tuple (schema_to_no_name s1))
  (rhs: Tuple.tuple (schema_to_no_name s2))
  : option (Tuple.tuple (schema_to_no_name (output_schema_join_by s1 s2 join_by))).
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
    assert (∀ elem : nat * nat * Attribute, In elem common_join_list →
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
    pose (Tuple.tuple_concat _ _ lhs' rhs') as result.
    specialize join_type_eq with
      (s1 := (a :: s1)) (s2 := (a0 :: s2)) (join_by := join_by)
      (lhs := lhs_join_list) (rhs := rhs_join_list)
      (index_lhs := index_lhs) (index_rhs := index_rhs) (common_join_list := common_join_list).
    intros.
    assert (schema_to_no_name (remove_common (a :: s1) index_lhs 0) ++
            schema_to_no_name (remove_common (a0 :: s2) index_rhs 0) =
    schema_to_no_name (output_schema_join_by (a :: s1) (a0 :: s2) join_by))
      by auto.
    rewrite <- H1.
    exact (Some result).
Defined.

(*
  This function computes the joined result of two relations provided a join list.

  TODO: What happens if we are joining tables with `nil` as one of the schemas?
*)
Definition relation_join_by s1 s2 (r1: relation s1) (r2: relation s2) (join_by: list string):
  relation (output_schema_join_by s1 s2 join_by).
  destruct s1; destruct s2.
  - exact nil.
  - exact nil.
  - exact nil.
  - induction r1.
    + exact nil.
    + induction r2.
      * exact nil.
      * (* concatenate two tuples a1 and a2. *)
        pose (tuple_concat_by _ _ join_by a1 a2).
        destruct o.
        -- (* Some *) exact ((t :: IHr1) ++ IHr2).
        -- (* None *) exact (IHr1 ++ IHr2).
Defined.

Definition relation_natural_join s1 s2 (r1: relation s1) (r2: relation s2):
  relation (output_schema_join_by s1 s2 (natural_join_list s1 s2)) :=
  relation_join_by s1 s2 r1 r2 (natural_join_list s1 s2).

Example relation_a :=
  [[ 4, 5, 6, ("abcd"%string) ]] ::
    [[ 7, 8, 9, ("abcd"%string) ]] :: nil.
Example relation_b :=
  [[ 1, 2, 3, ("abcd"%string) ]] ::
    [[ 114, 514, 114, ("abcd"%string) ]] :: nil.
Example simple_schema :=
  (IntegerType, "foo"%string) ::
    (IntegerType, "bar"%string) ::
      (IntegerType, "baz"%string) ::
        (StringType, "qux"%string) :: nil.
Example cartesian_product_test := relation_product simple_schema simple_schema relation_a relation_b.

Example cartesian_product_test': cartesian_product_test = (4, 0, (5, 0, (6, 0, ("abcd"%string, 0, (1, 0, (2, 0, (3, 0, ("abcd"%string, 0, tt)))))))) :: (4, 0, (5, 0, (6, 0, ("abcd"%string, 0, (114, 0, (514, 0, (114, 0, ("abcd"%string, 0, tt)))))))) :: (7, 0, (8, 0, (9, 0, ("abcd"%string, 0, (1, 0, (2, 0, (3, 0, ("abcd"%string, 0, tt)))))))) :: (7, 0, (8, 0, (9, 0, ("abcd"%string, 0, (114, 0, (514, 0, (114, 0, ("abcd"%string, 0, tt)))))))) :: nil.
Proof.
  reflexivity.
Qed.

Example relation_stitch_test := relation_stitch simple_schema simple_schema relation_a relation_b.
Example relation_stitch_test': relation_stitch_test = (4, 0, (5, 0, (6, 0, ("abcd"%string, 0, (1, 0, (2, 0, (3, 0, ("abcd"%string, 0, tt)))))))) :: (7, 0, (8, 0, (9, 0, ("abcd"%string, 0, (114, 0, (514, 0, (114, 0, ("abcd"%string, 0, tt)))))))) :: nil.
Proof.
  reflexivity.
Qed.

Example simple_schema_lhs :=
  (IntegerType, "foo"%string) ::
    (IntegerType, "bar"%string) ::
      (IntegerType, "baz"%string) :: nil.

Example simple_schema_rhs :=
  (IntegerType, "baz"%string) ::
    (StringType, "qux"%string) :: nil.

Example join_by_test := output_schema_join_by simple_schema_lhs simple_schema_rhs ("baz"%string :: nil).
Example join_by_test': join_by_test = (IntegerType, "foo"%string) :: (IntegerType, "bar"%string) :: (IntegerType, "baz"%string)  :: (StringType, "qux"%string) :: nil.
Proof.
  reflexivity.
Qed.

Example tuple_a := [[ 1, 2, 3, ("abcd"%string) ]].
Example tuple_b := [[ 4, 2, 3, ("abcd"%string) ]].
Example tuple_schema_lhs := (IntegerType, "foo"%string) :: (IntegerType, "bar"%string) :: (IntegerType, "baz"%string) :: (StringType, "qux"%string) :: nil.
Example tuple_schema_rhs := (IntegerType, "a"%string) :: (IntegerType, "bar"%string) :: (IntegerType, "baz"%string) :: (StringType, "b"%string) :: nil.
Example remove_common_test1 := remove_common tuple_schema_lhs (0 :: 1 :: nil) 0.
Example remove_common_test2 := remove_common_part tuple_schema_lhs tuple_a 0 (0 :: 1 :: nil).
Example tuple_concat_by_test := tuple_concat_by tuple_schema_lhs tuple_schema_rhs nil tuple_a tuple_b.

Example remove_common_test1_correct: remove_common_test1 = (IntegerType, "baz"%string) :: (StringType, "qux"%string) :: nil.
Proof.
  reflexivity.
Qed.

Example remove_common_test2_correct: remove_common_test2 = [[ 3, "abcd"%string ]].
Proof.
  reflexivity.
Qed.