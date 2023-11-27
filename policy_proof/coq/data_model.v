Require Import String.
Require Import RelationClasses.
Require Import Lia.
Require Import SetoidDec.
Require Import SetoidClass.
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

Definition policy_lt (lhs rhs: policy): Prop :=
  flowsto lhs rhs /\ lhs =/= rhs.

Global Instance policy_lt_trans: Transitive policy_lt.
  unfold Transitive.
  intros. destruct x; destruct y; destruct z; unfold policy_lt in *; intuition auto with *;
  unfold "⊑" in *; simpl in *; unfold complement, policy_eq in *; intros; try inversion H0.
Defined.

Global Instance policy_ordered: Ordered policy.
refine (
  @Build_Ordered policy policy_setoid policy_lt policy_lt_trans _ _
).
  - intros. simpl. unfold complement, policy_eq, policy_lt in *. intuition auto with *.
  - intros. destruct lhs; destruct rhs.
    + apply OrderedType.EQ. apply policy_eq_eqv.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.EQ. apply policy_eq_eqv.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.EQ. apply policy_eq_eqv.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.EQ. apply policy_eq_eqv.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.EQ. apply policy_eq_eqv.
    + apply OrderedType.LT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.GT. unfold policy_lt. unfold "⊑". split; auto with *. simpl. unfold complement. intros.
      unfold policy_eq in *. inversion H.
    + apply OrderedType.EQ. apply policy_eq_eqv.
Defined.

(* The active policy context. *)
(* release policy: option policy *)
Definition policy_encoding := (policy * option policy)%type.
Definition context := list (nat * policy_encoding)%type.
Definition can_release (p: policy_encoding): Prop := 
  match p with
    | (cur, None) => False
    | (cur, Some disc) => disc <<= cur
  end.

Definition cannot_release (p: policy_encoding): Prop := ~ can_release p.
 
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
(* A cell that carries policies . *)
Definition cell: Set := basic_type % type.
Definition cell_denote (c: cell): Set := (type_to_coq_type c) % type.

Global Instance cell_denote_eq_propers:
  Proper (equiv ==> equiv) (cell_denote).
Proof.
  unfold Proper, respectful. intros. unfold cell_denote. rewrite H. reflexivity.
Qed.

End Cell.

Module Tuple.

(* A tuple is a list of cells of different values. *)
Definition tuple_type: Set := (list Cell.cell)%type.

(* A tuple is, in essence, an interpretation of abstract values to their
concrete values. Thus it is a dependent type of `tuple_type`. We also
make it a recursive type, so that we can build types of arbitrary length. *)
Fixpoint tuple (ty: tuple_type): Set :=
  match ty with
  | nil => unit
  | bt :: t' => ((type_to_coq_type bt) * nat) * tuple t'
  end%type.

Fixpoint tuple_np (ty: tuple_type): Set :=
  match ty with
    | nil => unit
    | bt :: t' => (type_to_coq_type bt) * tuple_np t'
  end%type.

Fixpoint bounded_list (l: list nat) (ty: tuple_type): Prop :=
  match l with
    | nil => True
    | n :: l' => n < length ty /\ bounded_list l' ty
  end.

Fixpoint inject_tuple_id
  (ty: tuple_type)
  (t: tuple_np ty)
  (id: nat)
: tuple ty :=
  match ty return forall (t: tuple_np ty) (id: nat), tuple ty with
    | nil => fun _  _ => tt
    | bt :: t' => fun t id => (((fst t), id), inject_tuple_id t' (snd t) (id + 1))
  end t id.

Fixpoint tuple_value_lt (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return forall (lhs rhs: tuple ty), Prop with
    | nil => fun _ _ => False
    | _ :: t' => fun lhs rhs => lt (fst (fst lhs)) (fst (fst rhs)) \/
      (fst (fst lhs)) == (fst (fst rhs)) /\ tuple_value_lt t' (snd lhs) (snd rhs)
  end.

Fixpoint tuple_total_lt (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return forall (lhs rhs: tuple ty), Prop with
    | nil => fun _ _ => False
    | _ :: t' => fun lhs rhs => lt (fst lhs) (fst rhs) \/
      (fst lhs) == (fst rhs) /\ tuple_total_lt t' (snd lhs) (snd rhs)
  end.

(* A tuple type is a list of basic types. *)

Example example_tuple_ty : tuple_type := StringType :: BoolType :: nil.
Example example_tuple: tuple_np example_tuple_ty := ("abcd"%string, (true, tt)).
Example example_tuple_ty' : tuple_type := IntegerType :: nil.
Example example_tuple' : tuple_np example_tuple_ty' := (1, tt).
Example example_tuple'' : tuple_np (example_tuple_ty' ++ example_tuple_ty) := 
  (1, ("abcd"%string, (true, tt))).

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
    | bt1 :: t1', bt2 :: t2' => andb (type_matches bt1 bt2) (tuple_type_eq t1' t2')
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
    | _ :: tl => fun lhs rhs => 
      (fst (fst lhs)) == (fst (fst rhs)) /\ tuple_value_eq tl (snd lhs) (snd rhs)
  end. 

Fixpoint tuple_total_eq (ty: tuple_type): forall (lhs rhs: tuple ty), Prop :=
  match ty return (forall (lhs rhs: tuple ty), Prop) with
    | nil => fun _ _ => True
    | _ :: tl => fun lhs rhs => 
      (fst lhs) == (fst rhs) /\ tuple_total_eq tl (snd lhs) (snd rhs)
  end.

Global Instance tuple_value_eq_eqv (ty: tuple_type): Equivalence (tuple_value_eq ty).
  (* Note that `Equivalence` is a class. *)
  constructor.
  - unfold Reflexive.
    intros. induction ty; intuition auto with *. destruct a; simpl in *; auto. split; try reflexivity; auto.
  - unfold Symmetric.
    intros. induction ty; intuition auto with *. destruct a; simpl in *; intuition auto with *.
  - unfold Transitive.
    induction ty; intuition auto with *. destruct a; simpl in *; intuition auto with *.
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
    intros. induction ty. intuition auto with *. destruct a; simpl in *; intuition auto with *;
    unfold pair_eq; auto with *.
  - unfold Symmetric.
    intros. induction ty. intuition auto with *. destruct a; simpl in *; intuition auto with *;
    unfold pair_eq in *; intuition auto with *.
  - unfold Transitive.
    intros. induction ty. auto. destruct a.
    simpl in *. intuition; unfold pair_eq in *; intuition; auto with *.
      + rewrite H0. assumption.
      + rewrite H4. assumption.
      + specialize (IHty _ _ _ H2 H3). assumption.
      
      + simpl in *. unfold pair_eq in *. intuition.
        -- rewrite H0. assumption.
        -- rewrite H4. assumption.
        -- specialize (IHty _ _ _ H2 H3). assumption.
      + simpl in *. unfold pair_eq in *. intuition.
        -- rewrite H0. assumption.
        -- rewrite H4. assumption.
        -- specialize (IHty _ _ _ H2 H3). assumption.
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

Definition ntypes (l: list nat) (ty: tuple_type) (bounded: bounded_list l ty): tuple_type.
  induction l.
  - exact nil. (* nil => nil *)
  - destruct bounded.
    apply cons. (* cons => cons *)
    apply (nth ty a H).
    apply IHl. apply H0.
Defined.

Definition nth_col_tuple: forall (ty: tuple_type) (n : nat) (extract: n < length ty), tuple ty -> tuple ((nth ty n extract) :: nil).
refine (
  fix nth_col_tuple' (ty: tuple_type) (n : nat): forall (extract: n < length ty),
    tuple ty -> tuple ((nth ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple ((nth ty' n' extract) :: nil) with
        |_  :: l', 0 => fun _ _ _ t => ((fst t), tt)
        | _ :: l', S n' => fun _ _ _ t => nth_col_tuple' l' n' _ (snd t)
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
  exact (nth ty n extract).
Defined.

(* Without `policy` extracted! *)
Definition nth_col_tuple_np: forall (ty: tuple_type) (n : nat) (extract: n < length ty), tuple ty -> tuple_np ((nth_np ty n extract) :: nil).
refine (
  fix nth_col_tuple_np' (ty: tuple_type) (n : nat): forall (extract: n < length ty),
    tuple ty -> tuple_np ((nth_np ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' -> n = n' -> 
            forall (extract: n' < length ty'), tuple ty' -> tuple_np ((nth_np ty' n' extract) :: nil) with
        | _ :: l', 0 => fun _ _ _ t => ((fst (fst t)), tt)
        | _ :: l', S n' => fun _ _ _ t => nth_col_tuple_np' l' n' _ (snd t)
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

Global Instance tuple_total_eq_setoid (ty: tuple_type): Setoid (tuple ty).
  exists (tuple_total_eq ty).
  apply tuple_total_eq_eqv.
Defined.

Definition tuple_value_compare: forall (ty: tuple_type) (lhs rhs: tuple ty), 
  OrderedType.Compare (tuple_value_lt ty) (@tuple_value_eq ty) lhs rhs.
Proof.
  intros. induction ty.
  - apply OrderedType.EQ. simpl. auto.
  - destruct a.
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
  + destruct a; simpl in *.
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

Global Instance tuple_total_lt_trans (ty: tuple_type): Transitive (tuple_total_lt ty).
  unfold Transitive. induction ty.
  - intros. auto.
  - destruct a. 
    + simpl in *. unfold pair_lt, pair_eq in *. intuition.
      * left. left. eapply transitivity; eauto.
      * left. left. rewrite H in H0. assumption.
      * left. left. rewrite <- H1 in H0. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- eapply transitivity; eauto.
      * left. left. rewrite <- H. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- rewrite H3 in H4. assumption.
      * left. left. rewrite H1. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- rewrite <- H3 in H4. assumption.
      * right. repeat split.
        -- rewrite H1. assumption.
        -- rewrite <- H5. assumption.
        -- specialize (IHty _ _ _ H2 H4). assumption.

    + simpl in *. unfold pair_lt, pair_eq in *. intuition.
      * left. left. eapply transitivity; eauto.
      * left. left. rewrite H in H0. assumption.
      * left. left. rewrite <- H1 in H0. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- eapply transitivity; eauto.
      * left. left. rewrite <- H. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- rewrite H3 in H4. assumption.
      * left. left. rewrite H1. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- rewrite <- H3 in H4. assumption.
      * right. repeat split.
        -- rewrite H1. assumption.
        -- rewrite <- H5. assumption.
        -- specialize (IHty _ _ _ H2 H4). assumption.

(* TODO: REDUCE DUPLICATE CODE. *)
    + simpl in *. unfold pair_lt, pair_eq in *. intuition.
      * left. left. eapply transitivity; eauto.
      * left. left. rewrite H in H0. assumption.
      * left. left. rewrite <- H1 in H0. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- eapply transitivity; eauto.
      * left. left. rewrite <- H. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- rewrite H3 in H4. assumption.
      * left. left. rewrite H1. assumption.
      * left. right. split.
        -- rewrite H1. assumption.
        -- rewrite <- H3 in H4. assumption.
      * right. repeat split.
        -- rewrite H1. assumption.
        -- rewrite <- H5. assumption.
        -- specialize (IHty _ _ _ H2 H4). assumption.
Defined.

Global Instance tuple_is_total_ordered (ty: tuple_type): Ordered (tuple ty).
refine(
  @Build_Ordered
  (tuple ty)
  (tuple_total_eq_setoid ty)
  (tuple_total_lt ty)
  (tuple_total_lt_trans ty)
  _ _
).
  - intros. simpl. unfold complement.
    induction ty.
    + simpl in H. exfalso. assumption.
    + intros. destruct a; simpl in *; unfold pair_lt, pair_eq in *; intuition.
      * rewrite H0 in H. apply neq in H. auto with *.
      * rewrite H3 in H4. apply neq in H4. auto with *.
      * specialize (IHty _ _ H4 H2). assumption.

      * rewrite H0 in H. apply neq in H. auto with *.
      * rewrite H3 in H4. apply neq in H4. auto with *.
      * specialize (IHty _ _ H4 H2). assumption.

      * rewrite H0 in H. apply neq in H. auto with *.
      * rewrite H3 in H4. apply neq in H4. auto with *.
      * specialize (IHty _ _ H4 H2). assumption.
  
  - induction ty.
    + intros. apply OrderedType.EQ. apply unit_eq_equiv. auto.
    + intros. destruct a.
      * destruct (cmp (fst lhs) (fst rhs)).
        -- apply OrderedType.LT. simpl. auto.
        -- destruct (IHty (snd lhs) (snd rhs)).
          apply OrderedType.LT. simpl. auto.
          apply OrderedType.EQ. simpl. split; auto.
          apply OrderedType.GT. simpl. auto.
          unfold pair_lt, pair_eq in *. right.
          repeat split; try rewrite e; try reflexivity; assumption.
        -- apply OrderedType.GT. simpl. auto.
      * destruct (cmp (fst lhs) (fst rhs)).
        -- apply OrderedType.LT. simpl. auto.
        -- destruct (IHty (snd lhs) (snd rhs)).
          apply OrderedType.LT. simpl. auto.
          apply OrderedType.EQ. simpl. split; auto.
          apply OrderedType.GT. simpl. auto.
          unfold pair_lt, pair_eq in *. right.
          repeat split; try rewrite e; try reflexivity; assumption.
        -- apply OrderedType.GT. simpl. auto.
      * destruct (cmp (fst lhs) (fst rhs)).
        -- apply OrderedType.LT. simpl. auto.
        -- destruct (IHty (snd lhs) (snd rhs)).
          apply OrderedType.LT. simpl. auto.
          apply OrderedType.EQ. simpl. split; auto.
          apply OrderedType.GT. simpl. auto.
          unfold pair_lt, pair_eq in *. right.
          repeat split; try rewrite e; try reflexivity; assumption.
        -- apply OrderedType.GT. simpl. auto. 
Defined.

Global Instance tuple_is_ordered_by_value (ty: tuple_type): Ordered (tuple ty).
refine(
  @Build_Ordered
  (tuple ty)
  (@Build_Setoid _ (tuple_value_eq ty) _)
  (tuple_value_lt ty) _ _ _
).
  intros.
  simpl. unfold complement. intros.
  induction ty.
  - simpl in H. exfalso. assumption.
  - destruct a; simpl in *; unfold pair_lt, pair_eq in *; intuition.
    * rewrite H1 in H0. unfold nat_lt in H0. auto with *.
    * specialize (IHty _ _ H3 H2). assumption.
    * unfold bool_lt in H0. destruct H0. rewrite H in H1. rewrite H0 in H1. inversion H1.
    * specialize (IHty _ _ H3 H2). assumption.
    * rewrite H1 in H0. apply string_lt_neq in H0. auto with *.
    * specialize (IHty _ _ H3 H2). assumption.

  - intros. induction ty.
    * apply OrderedType.EQ. simpl. red. auto.
    * destruct a; destruct (cmp (fst (fst lhs)) (fst (fst rhs))).
      + apply OrderedType.LT. simpl. auto.
      + destruct (IHty (snd lhs) (snd rhs)).
        apply OrderedType.LT. simpl. auto.
        apply OrderedType.EQ. simpl. split; auto.
        apply OrderedType.GT. simpl. auto.
      + apply OrderedType.GT. simpl. auto.
      + apply OrderedType.LT. simpl. auto.
      + destruct (IHty (snd lhs) (snd rhs)).
        apply OrderedType.LT. simpl. auto.
        apply OrderedType.EQ. simpl. split; auto.
        apply OrderedType.GT. simpl. auto.
      + apply OrderedType.GT. simpl. auto.
      + apply OrderedType.LT. simpl. auto.
      + destruct (IHty (snd lhs) (snd rhs)).
        apply OrderedType.LT. simpl. auto.
        apply OrderedType.EQ. simpl. split; auto.
        apply OrderedType.GT. simpl. auto.
        right. split. rewrite e. reflexivity.
        assumption.
      + apply OrderedType.GT. simpl. auto.
Defined.

Definition example_tuple_lhs : tuple example_tuple_ty := (("abcd"%string, 1), ((true, 2), tt)).
Definition example_tuple_rhs : tuple example_tuple_ty := (("abcd"%string, 1), ((true, 2), tt)).
Set Printing Constructor.
Set Printing Coercions.
Set Printing Implicit.
Set Printing Projections.
Example example_tuple_total_eq: tuple_total_eq example_tuple_ty example_tuple_lhs example_tuple_rhs.
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

Section Facts.
  Context {ty: Tuple.tuple_type}.

  Notation "a <~ b":= (Tuple.tuple_value_lt ty a b) (at level 70, no associativity):
    type_scope.
  Notation "a <<~ b":= (Tuple.tuple_total_lt ty a b) (at level 70, no associativity):
    type_scope.

End Facts.
