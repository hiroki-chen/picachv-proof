(* The policy library. *)

Require Import String.
Require Import RelationClasses.
Require Import Lia.
Require Import SetoidDec.
Require Import SetoidClass.
(* Require Import EqNat. *)
Require Import List.

Require Import lattice.
Require Import ordering.
Require Import types.

Module Policy.
(* For now, the policy is just a placeholder. *)
(* TODO: Wrap more information? *)
Inductive policy : Set :=
  | policy_bot : policy
  (* Should be something like `pred -> policy` *)
  | policy_select: policy
  | policy_transform: policy
  | policy_agg: policy
  | policy_noise: policy
  | policy_top : policy
  .

(* Joins two policy labels. *)
Definition policy_join (lhs rhs: policy): policy :=
  match lhs, rhs with
    | Policy.policy_bot, _ => rhs
    | _, Policy.policy_bot => lhs
    | policy_select, policy_select => lhs
    | policy_select, policy_transform => rhs
    | policy_select, policy_agg => rhs
    | policy_select, policy_noise => rhs
    | policy_transform, policy_select => lhs
    | policy_transform, policy_transform => lhs
    | policy_transform, policy_agg => rhs
    | policy_transform, policy_noise => rhs
    | policy_agg, policy_select => lhs
    | policy_agg, policy_transform => lhs
    | policy_agg, policy_agg => lhs
    | policy_agg, policy_noise => rhs
    | policy_noise, policy_select => lhs
    | policy_noise, policy_transform => lhs
    | policy_noise, policy_agg => lhs
    | policy_noise, policy_noise => lhs
    | _, _ => policy_top
  end.

Definition policy_option_join (lhs rhs: option policy): option policy :=
  match lhs, rhs with
    | None, _ => rhs
    | _, None => lhs
    | Some lhs', Some rhs' => Some (policy_join lhs' rhs')
  end.

(* Meets two policy labels. *)
Definition policy_meet (lhs rhs: policy): policy :=
  match lhs, rhs with
    | policy_top, _ => rhs
    | _, policy_top => lhs
    | Policy.policy_bot, _ => Policy.policy_bot
    | _, Policy.policy_bot => Policy.policy_bot
    | policy_select, policy_select => lhs
    | policy_select, policy_transform => lhs
    | policy_select, policy_agg => lhs
    | policy_select, policy_noise => lhs
    | policy_transform, policy_select => rhs
    | policy_transform, policy_transform => lhs
    | policy_transform, policy_agg => lhs
    | policy_transform, policy_noise => lhs
    | policy_agg, policy_select => rhs
    | policy_agg, policy_transform => rhs
    | policy_agg, policy_agg => lhs
    | policy_agg, policy_noise => lhs
    | policy_noise, policy_select => rhs
    | policy_noise, policy_transform => rhs
    | policy_noise, policy_agg => rhs
    | policy_noise, policy_noise => lhs
  end.

Definition policy_option_meet (lhs rhs: option policy): option policy :=
  match lhs, rhs with
    | None, _ => None
    | _, None => None
    | Some lhs', Some rhs' => Some (policy_meet lhs' rhs')
  end.

(* Returns the top policy label. *)

Definition policy_eq (lhs rhs: policy): Prop :=
  lhs = rhs.
Definition policy_option_eq (lhs rhs: option policy): Prop :=
  match lhs, rhs with
    | None, None => True
    | Some lhs', Some rhs' => policy_eq lhs' rhs'
    | _, _ => False
  end.

Definition policy_eq_eqv: Equivalence policy_eq.
  constructor.
  - unfold Reflexive. intros. reflexivity.
  - unfold Symmetric. intros. induction H. reflexivity.
  - unfold Transitive. intros. induction H. assumption.
Defined.

Definition policy_option_eq_eqv: Equivalence policy_option_eq.
refine (
  @Build_Equivalence _ _ _ _ _
).
  - unfold Reflexive. intros. unfold policy_option_eq.
    destruct x; try reflexivity.
  - unfold Symmetric. intros. unfold policy_option_eq in *.
    destruct x; destruct y; try reflexivity; try contradiction.
    apply policy_eq_eqv. assumption.
  - unfold Transitive. intros. induction x; induction y; induction z; try intuition auto with *.
    simpl in *. eapply transitivity; eassumption.
Defined.

Lemma policy_join_comm: forall (lhs rhs: policy),
  policy_join lhs rhs = policy_join rhs lhs.
Proof.
  intros. destruct lhs; destruct rhs; reflexivity.
Qed.

Lemma policy_meet_comm: forall (lhs rhs: policy),
  policy_meet lhs rhs = policy_meet rhs lhs.
Proof.
  intros. destruct lhs; destruct rhs; reflexivity.
Qed.

Lemma policy_join_absorp: forall (lhs rhs: policy),
  policy_join lhs (policy_meet lhs rhs) = lhs.
Proof.
  intros. destruct lhs; destruct rhs; reflexivity.
Qed.

Lemma policy_join_assoc: forall (a b c: policy),
  policy_join a (policy_join b c) = policy_join (policy_join a b) c.
Proof.
  intros. destruct a; destruct b; destruct c; reflexivity.
Qed.

Lemma policy_meet_assoc: forall (a b c: policy),
  policy_meet a (policy_meet b c) = policy_meet (policy_meet a b) c.
Proof.
  intros. destruct a; destruct b; destruct c; reflexivity.
Qed.

Global Instance policy_lattice: lattice policy.
  econstructor.
  - eapply policy_eq_eqv.
  - intros. eapply policy_meet_comm.
  - intros. eapply policy_join_comm.
  - intros. eapply policy_join_assoc.
  - intros. eapply policy_join_absorp.
  - intros. eapply policy_meet_assoc.
  - intros. simpl. destruct a; destruct b; reflexivity.
  - intros. instantiate (1:=Policy.policy_bot). simpl. apply policy_eq_eqv. 
  - intros. instantiate (1:=policy_top). simpl. induction a; reflexivity.
  - intros. simpl. induction a; reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl in *.
    destruct x1; destruct x2; destruct y1; destruct y2; simpl; apply policy_eq_eqv; try inversion H0; try inversion H.
  - intros. simpl in *.
    destruct x1; destruct x2; destruct y1; destruct y2; simpl; apply policy_eq_eqv; try inversion H0; try inversion H.
  - intros. simpl in *. destruct x; destruct y; destruct z; simpl; apply policy_eq_eqv; try inversion H0; try inversion H.
  - intros. simpl in *. destruct x; destruct y; destruct z; simpl; apply policy_eq_eqv; try inversion H0; try inversion H.  
Defined.
Hint Resolve policy_lattice : typeclass_instances.

(* Global Instance policy_option_lattice: lattice (option policy).
Admitted. *)

Global Instance policy_setoid: Setoid policy.
refine (
  @Build_Setoid policy policy_eq policy_eq_eqv
).
Defined.

Global Instance policy_ordered: Ordered policy.
refine (
  @Build_Ordered policy policy_setoid flowsto _ _ _
).
Admitted.

(* The active policy context. *)
Definition policy_encoding := (option policy * option policy)%type.
Definition context := list (nat * policy_encoding)%type.
Definition can_release (p: policy_encoding): Prop := (fst p) = (snd p).
(* Lookup the policy context and check if the cell has been associated with an active policy. *)
Fixpoint label_lookup (id: nat) (ctx: context):
  option policy_encoding :=
    match ctx with
      | nil => None
      | (id', (cur, disc)) :: l' =>
          if Nat.eqb id id' then Some (cur, disc) else label_lookup id l'
    end.

End Policy.

Module Cell.

(* A cell that does not carry policies. *)
Definition clean_cell: Set := basic_type % type.
(* A cell that carries policies . *)
Definition cell: Set := (clean_cell * Policy.policy) % type.
Definition cell_denote (c: cell): Set := (type_to_coq_type (fst c) * Policy.policy) % type.

Definition cell_inject_policy (c: clean_cell) (p: Policy.policy): cell := (c, p).

End Cell.

Module Tuple.

(* A tuple is a list of cells of different values. *)
Definition tuple_type: Set := (list Cell.cell)%type.
Definition tuple_type_np: Set := (list Cell.clean_cell)%type.

(* A tuple is, in essence, an interpretation of abstract values to their
concrete values. Thus it is a dependent type of `tuple_type`. We also
make it a recursive type, so that we can build types of arbitrary length. *)
Fixpoint tuple (ty: tuple_type): Set :=
  match ty with
  | nil => unit
  | c :: t' => Cell.cell_denote c * tuple t'
  end%type.

Fixpoint tuple_np (ty: tuple_type_np): Set :=
  match ty with
    | nil => unit
    | bt :: t' => (type_to_coq_type bt) * tuple_np t'
  end%type.

Fixpoint tuple_value_lt (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return forall (lhs rhs: tuple ty), Prop with
    | nil => fun _ _ => False
    | (bt, _) :: t' => fun lhs rhs => lt (fst (fst lhs)) (fst (fst rhs)) \/
      (fst (fst lhs)) == (fst (fst rhs)) /\ tuple_value_lt t' (snd lhs) (snd rhs)
  end.

(* todo. *)
Fixpoint inject_policy (p: list Policy.policy) (ty: tuple_type_np): tuple_type :=
  match p, ty with
    | nil, nil => nil
    | p' :: p'', bt :: t' => (bt, p') :: inject_policy p'' t'
    | _, _ => nil
  end.

(* Revoves policies. *)
Definition extract_types (ty: tuple_type): tuple_type_np :=
  List.map (fun x => fst x) ty.

(* A tuple type is a list of basic types. *)

Definition example_tuple_ty : tuple_type := (StringType, Policy.policy_bot) :: (BoolType, Policy.policy_bot) :: nil.
Definition example_tuple: tuple example_tuple_ty := (("abcd"%string, Policy.policy_bot), ((true, Policy.policy_bot), tt)).
Definition example_tuple_ty' : tuple_type := (IntegerType, Policy.policy_bot) :: nil.
Definition example_tuple' : tuple example_tuple_ty' := ((1, Policy.policy_bot), tt).
Definition example_tuple'' : tuple (example_tuple_ty' ++ example_tuple_ty) := 
  ((1, Policy.policy_bot),
    (("abcd"%string, Policy.policy_bot),
      ((true, Policy.policy_bot),
        tt))).

(* Cast the type of the tuple, if needed. *)
Lemma tuple_cast: forall (ty1 ty2: tuple_type) (f: tuple_type -> Set),
  f ty1 -> ty1 = ty2 -> f ty2.
Proof.
  intros.
  rewrite H0 in H.
  auto. 
Qed.

(* A tuple type is a list of basic types. *)
Fixpoint tuple_type_eq (ty1 ty2: tuple_type) : bool :=
  match ty1, ty2 with
    | nil, nil => true
    | (bt1, _) :: t1', (bt2, _) :: t2' => andb (type_matches bt1 bt2) (tuple_type_eq t1' t2')
    | _, _ => false
  end.

(* Useful for joining two databases tuple-wise. *)
Definition tuple_concat (ty1 ty2: tuple_type)
  (lhs: tuple ty1) (rhs: tuple ty2): tuple (ty1 ++ ty2).
Proof.
  intros.
  induction ty1; auto.
    (* Just use existing component to construct the given type. *)
    simpl in *. destruct a; destruct lhs; constructor; auto.
Defined.

Global Instance tuple_concat_proper_eq (ty1 ty2: tuple_type):
  Proper (equiv ==> equiv ==> equiv) (tuple_concat ty1 ty2).
Proof.
  unfold Proper, respectful. induction ty1; destruct ty2; auto.
  - simpl in IHty1. intros. rewrite H0. rewrite H. reflexivity.
  - simpl in IHty1. intros. rewrite H0. rewrite H. reflexivity.
Qed.

Fixpoint tuple_value_eq (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return (forall (lhs rhs: tuple ty), Prop) with
    | nil => fun _ _ => True
    | (h, p) :: tl => fun lhs rhs => 
      (fst (fst lhs)) == (fst (fst rhs)) /\ tuple_value_eq tl (snd lhs) (snd rhs)
  end. 

Fixpoint tuple_total_eq (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return (forall (lhs rhs: tuple ty), Prop) with
    | nil => fun _ _ => True
    | (h, p) :: tl => fun lhs rhs => 
      (fst lhs) == (fst rhs) /\ (snd lhs) == (snd rhs) /\ tuple_total_eq tl (snd lhs) (snd rhs)
  end. 

Definition tuple_value_eq_eqv (ty: tuple_type): Equivalence (tuple_value_eq ty).
  (* Note that `Equivalence` is a class. *)
  constructor.
  - unfold Reflexive.
    intros. induction ty; intuition auto with *. destruct a; destruct c; simpl in *; auto. split; try reflexivity; auto.
  - unfold Symmetric.
    intros. induction ty; intuition auto with *. destruct a; destruct c; simpl in *; intuition auto with *.
  - unfold Transitive.
    induction ty; intuition auto with *. destruct a; destruct c; simpl in *; intuition auto with *.
    specialize (IHty _ _ _ H2 H3). assumption.
    eapply transitivity; eauto.
    specialize (IHty _ _ _ H2 H3). assumption.
    eapply transitivity; eauto.
    specialize (IHty _ _ _ H2 H3). assumption.    
Defined.

Definition tuple_total_eq_eqv (ty: tuple_type): Equivalence (tuple_total_eq ty).
  (* Note that `Equivalence` is a class. *)
  split.
  - unfold Reflexive.
    intros. induction ty. intuition auto with *. destruct a; destruct c; simpl in *; intuition auto with *;
    unfold pair_eq; auto with *.
  - unfold Symmetric.
    intros. induction ty. intuition auto with *. destruct a; destruct c; simpl in *; intuition auto with *;
    unfold pair_eq in *; intuition auto with *.
  - unfold Transitive.
    intros. induction ty. auto. destruct a. destruct c.
    simpl in *. intuition; unfold pair_eq in *; intuition; auto with *.
      + rewrite H3. assumption.
      + rewrite H6. assumption.
      + rewrite H0. assumption.
      + eapply IHty in H5; eauto.
      + simpl in *. intuition; unfold pair_eq in *; intuition; auto with *.
        * rewrite H3. assumption.
        * rewrite H6. assumption.
        * rewrite H0. assumption.
        * eapply IHty in H5; eauto.
      + simpl in *. intuition; unfold pair_eq in *; intuition; auto with *.
        * rewrite H3. assumption.
        * rewrite H6. assumption.
        * rewrite H0. assumption.
        * eapply IHty in H5; eauto.
Defined.

Definition nth: forall (ty: tuple_type) (n: nat) (extract: n < length ty), Cell.cell.
refine
(fix nth' (ty: tuple_type) (n: nat):
  n < length ty -> Cell.cell :=
     match ty as ty' , n as n' return ty = ty' -> n = n' -> n' < length ty' -> Cell.cell with
      | x :: y , 0 => fun _ _ _ => x
      | x :: y , S n' => fun _ _ _ => nth' y n' _
      | _ , _ => fun _ _ _ => False_rec _ _
    end (refl_equal _) (refl_equal _)).
Proof.
  - simpl in *. lia.
  - simpl in *. lia.
Defined.

Definition nth_col_tuple: forall (ty: tuple_type) (n : nat) (extract: n < length ty), tuple ty -> tuple ((nth ty n extract) :: nil).
refine (
  fix nth_col_tuple' (ty: tuple_type) (n : nat): forall (extract: n < length ty),
    tuple ty -> tuple ((nth ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple ((nth ty' n' extract) :: nil) with
        | (bt, p) :: l', 0 => fun _ _ _ t => ((fst t), tt)
        | (bt, p) :: l', S n' => fun _ _ _ t => nth_col_tuple' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. lia.
Defined.

Global Instance nth_col_tuple_proper_eq
(ty: tuple_type) (n: nat) (extract: n < length ty):
  Proper (equiv ==> equiv) (nth_col_tuple ty n extract).
Proof.
  unfold Proper, respectful. intros. rewrite H. reflexivity.
Qed.

(* Without `policy` extracted! *)
Definition nth_np: forall (ty: tuple_type) (n: nat) (extract: n < length ty), basic_type.
  intros.
  exact (fst (nth ty n extract)).
Defined.

(* Without `policy` extracted! *)
Definition nth_col_tuple_np: forall (ty: tuple_type) (n : nat) (extract: n < length ty), tuple ty -> tuple_np ((nth_np ty n extract) :: nil).
refine (
  fix nth_col_tuple_np' (ty: tuple_type) (n : nat): forall (extract: n < length ty),
    tuple ty -> tuple_np ((nth_np ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple_np ((nth_np ty' n' extract) :: nil) with
        | (bt, p) :: l', 0 => fun _ _ _ t => ((fst (fst t)), tt)
        | (bt, p) :: l', S n' => fun _ _ _ t => nth_col_tuple_np' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
simpl in *. lia.
Defined.

Global Instance nth_col_tuple_np_proper_eq
(ty: tuple_type) (n: nat) (extract: n < length ty):
  Proper (equiv ==> equiv) (nth_col_tuple_np ty n extract).
Proof.
  unfold Proper, respectful. intros. rewrite H. reflexivity.
Qed.

Global Instance tuple_is_setoid (ty: tuple_type): Setoid (tuple ty).
  exists (tuple_total_eq ty).
  apply tuple_total_eq_eqv.
Defined.

Definition tuple_value_compare: forall (ty: tuple_type) (lhs rhs: tuple ty), 
  OrderedType.Compare (tuple_value_lt ty) (@tuple_value_eq ty) lhs rhs.
Proof.
  intros. induction ty.
  - apply OrderedType.EQ. simpl. auto.
  - destruct a; destruct c.
    + simpl in lhs. simpl in rhs. destruct (cmp (fst (fst lhs)) (fst (fst rhs))).
      * apply OrderedType.LT. simpl. auto.
      * destruct (IHty (snd lhs) (snd rhs)).
        apply OrderedType.LT. simpl. auto.
        apply OrderedType.EQ. simpl. split; auto.
        apply OrderedType.GT. simpl. auto.
      * apply OrderedType.GT. simpl. auto.
    + simpl in lhs. simpl in rhs. destruct (cmp (fst (fst lhs)) (fst (fst rhs))).
      * apply OrderedType.LT. simpl. auto.
      * destruct (IHty (snd lhs) (snd rhs)).
        apply OrderedType.LT. simpl. auto.
        apply OrderedType.EQ. simpl. split; auto.
        apply OrderedType.GT. simpl. auto.
      * apply OrderedType.GT. simpl. auto.
    + simpl in lhs. simpl in rhs. destruct (cmp (fst (fst lhs)) (fst (fst rhs))).
      * apply OrderedType.LT. simpl. auto.
      * destruct (IHty (snd lhs) (snd rhs)).
        apply OrderedType.LT. simpl. auto.
        apply OrderedType.EQ. simpl. split; auto.
        apply OrderedType.GT. simpl. auto.
        right. split; auto. rewrite e. reflexivity.
      * apply OrderedType.GT. simpl. auto.
Qed.

Global Instance tuple_value_lt_trans (ty: tuple_type): Transitive (tuple_value_lt ty).
  unfold Transitive. induction ty.
  + intros. auto.
  + destruct a; destruct c. simpl in *.
    (* Integer. *)
    intuition auto with *. left. eapply transitivity; eauto. simpl in *.
    left. rewrite H0 in H1. assumption.
    left. rewrite <- H in H1. assumption.
    right. rewrite <- H0. split. auto.
    specialize (IHty _ _ _ H2 H3). assumption.

    (* Boolean *)
    intros. simpl in *. intuition.
    left. eapply transitivity; eauto.
    left. rewrite H0 in H1. assumption.
    left. rewrite <- H in H1. assumption.
    right. rewrite <- H0. split. auto.
    specialize (IHty _ _ _ H2 H3). assumption.

    (* String *)
    intros. simpl in *. intuition.
    left. eapply transitivity; eauto.
    left. rewrite H0 in H1. assumption.
    left. rewrite <- H in H1. assumption.
    right. rewrite <- H0. split. auto.
    specialize (IHty _ _ _ H2 H3). assumption.
Defined.

(* Partial comparison does not guarantee that tuples are `equiv` if `lt x y` and `lt y x`. *)
(* TODO: Change this to total comparison and establish equivalance between `tuple` and `tuple_np`. *)
Lemma tuple_value_eq_equiv: forall (ty: tuple_type) (lhs rhs: tuple ty),
  Equivalence.equiv lhs rhs <-> tuple_value_eq ty lhs rhs.
Proof.
Admitted.

Global Instance tuple_is_ordered_by_value (ty: tuple_type): Ordered (tuple ty).
refine(
  @Build_Ordered
  (tuple ty)
  (tuple_is_setoid ty)
  (tuple_value_lt ty)
  (tuple_value_lt_trans ty)
  _ _
).
  - intros. simpl. unfold complement.
    induction ty.
    + simpl in H. exfalso. assumption.
    + intros. destruct a; destruct c; simpl in *. intuition.
      unfold pair_eq in *. intuition. rewrite H in H2. inversion H2. lia. lia.
      eapply IHty in H3; auto.
      intuition. unfold pair_eq in *. intuition.
      rewrite H in H2. inversion H2. rewrite H1 in H5. inversion H5.
      eapply IHty in H3; auto.
      intuition. unfold pair_eq in *. intuition.
      rewrite H in H2. apply asymmetry in H2. auto. auto.
      eapply IHty in H3; auto.

    - intros. induction ty.
      + apply OrderedType.EQ. simpl. apply unit_eq_equiv. exact lhs.
      + destruct a; destruct c; simpl in *; intuition; destruct (cmp a a0).
        * apply OrderedType.LT. simpl. auto. unfold nat_lt in *. 
       (*TODO: MAKE IT TOTAL ORDER  *)
Admitted.

Definition example_tuple_lhs : tuple example_tuple_ty := (("abcd"%string, Policy.policy_bot), ((true, Policy.policy_bot), tt)).
Definition example_tuple_rhs : tuple example_tuple_ty := (("abcd"%string, Policy.policy_bot), ((true, Policy.policy_bot), tt)).

Example example_tuple_total_eq: tuple_total_eq example_tuple_ty example_tuple_lhs example_tuple_lhs.
Proof.
  simpl. repeat split; simpl; reflexivity.
Qed.

End Tuple.

Require Import Floats.
Module Configuration.

Definition privacy: Set := float.

(* TODO: The third one should be the operator. *)
Definition config:= (Policy.label_lookup, privacy, unit)%type.
End Configuration.

Ltac str_eq:= auto; simpl in *; unfold char_eq in *; unfold char_lt in *; lia.

Require Import finite_bags.

Module Relation.

Definition relation: Set := fbag Tuple.tuple_type.

(* Global Instance relation_is_fbag: FiniteBag Tuple.tuple_type. *)

End Relation.
