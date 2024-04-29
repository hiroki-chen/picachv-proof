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

Require Import lattice.
Require Import ordering.
Require Import types.
Require Import util.

Module Policy.
(*
  The `policy_label` inductive type represents the different types of policies that can be
  applied to data in the data model. Each policy_label can be applied to a cell in a rela-
  tion, and the effect of the policy_label depends on its type.

  This is the definition for ℓ^{op} in the paper; altough for simplicity we have modified
  the definition slightly.
*)
Inductive policy_label : Type :=
  | policy_bot: policy_label
  (* Should be something like `pred → policy_label` *)
  | policy_select: policy_label
  | policy_transform: set trans_op → policy_label
  | policy_agg: set agg_op → policy_label
  | policy_noise: noise_op → policy_label
  | policy_top : policy_label
.

Definition policy_base_label_eq (lhs rhs: policy_label): Prop :=
  match lhs, rhs with
  | policy_bot, policy_bot => True
  | policy_select, policy_select => True
  | policy_transform _, policy_transform _ => True
  | policy_agg _, policy_agg _ => True
  | policy_noise _, policy_noise _ => True
  | policy_top, policy_top => True
  | _, _ => False
  end.
Notation "x '≃' y" := (policy_base_label_eq x y) (at level 10, y at next level, no associativity).


Lemma policy_base_label_eq_dec: ∀ (lhs rhs: policy_label), {lhs ≃ rhs} + {~ (lhs ≃ rhs)}.
Proof.
  intros. destruct lhs; destruct rhs;
  solve [left; red; auto | right; unfold not; intros; apply H; reflexivity].
Qed.

(*
  The `policy` inductive type represents the different types of policies that can be applied
  to data in the data model. Each policy can be applied to a cell in a Relation, and the effect
  of the policy depends on its type.

  Currently we have two types of policy:
  * `policy_clean` means that we have applied all the required policies to the data.
  * `policy_declass` means that we have current policy `label` and if it is applied to the data,
    then we will have the next policy `policy`.
*)
Inductive policy: Type :=
  | policy_clean: policy
  | policy_declass: policy_label → policy → policy
.

Fixpoint policy_store (s: schema_no_name): Type :=
  match s with
  | nil => unit
  | h :: t => (policy * policy_store t)%type
  end.

(*
 * One should not be confused: the `ℓ1 ⇝ ℓ2 ...` means that the policy label `ℓ1`
 * is higher than the policy label `ℓ2` and so on.
 *)
Notation "x ⇝ y" := (policy_declass x y) (at level 10, no associativity).
Notation "'∎'" := (policy_clean).
(*
 * This is a shorthand for specifying the end of a policy chain.
 *)
Notation "'∘' x" := (x ⇝ ∎) (at level 10, no associativity).

Definition can_declassify ℓ ℓop : Prop :=
  match ℓ, ℓop with
  | policy_bot, _ => True
  | policy_transform s1, policy_transform s2 => s2 ⊆ s1
  | policy_agg s1, policy_agg s2 => s2 ⊆ s1
  | policy_top, _ => False
  | _, _ => ℓ = ℓop
  end.

Definition policy_label_eq (lhs rhs: policy_label): Prop :=
  match lhs, rhs with
  | policy_top, policy_top => True
  | policy_bot, policy_bot => True
  | policy_select, policy_select => True
  | policy_transform ℓ1, policy_transform ℓ2 => set_eq ℓ1 ℓ2
  | policy_agg ℓ1, policy_agg ℓ2 => set_eq ℓ1 ℓ2
  | policy_noise p1, policy_noise p2 =>
      match p1, p2 with
        | differential_privacy (ε1, δ1), differential_privacy (ε2, δ2) =>
            ε1 = ε2 ∧ δ1 = δ2
      end
  | _, _ => False
  end.

Lemma policy_eq_dec: ∀ (lhs rhs: policy_label), {policy_label_eq lhs rhs} + {~ (policy_label_eq lhs rhs)}.
Proof.
  destruct lhs; destruct rhs; auto with *;
  try destruct (set_eq_dec transop_dec s s0);
  try destruct (set_eq_dec aggop_dec s s0).
  - left. auto.
  - right. auto.
  - left. auto.
  - right. auto.
  - destruct n, n0, d, d0. auto with *.
    destruct (nat_dec n n1). destruct (nat_dec n0 n2); try destruct s; try destruct s0; simpl; intuition.
    1-5: right; lia.
    all:simpl; right; lia.
Defined.

Theorem can_declassify_dec: ∀ ℓ ℓop, {can_declassify ℓ ℓop} + {~ can_declassify ℓ ℓop}.
Proof.
  intros. destruct ℓ; destruct ℓop; auto with *;
  try solve [(left; simpl; auto) | (right; red; intros; discriminate)].
  - destruct (subset_dec trans_op_eq_dec s0 s).
    + left. simpl. assumption.
    + right. red. intros. apply n. simpl in H. assumption.
  - destruct (subset_dec agg_op_eq_dec s0 s).
    + left. simpl. assumption.
    + right. red. intros. apply n. simpl in H. assumption.
  - destruct n, n0, d, d0.
    destruct (Nat.eq_dec n n1); destruct (Nat.eq_dec n0 n2); subst;
    solve [(left; simpl; auto) | (unfold not in n3; right; red; intros; apply n3; inversion H; reflexivity)].
Qed.

Fixpoint policy_as_list (p: policy): list policy_label :=
  match p with
  | ℓ ⇝ p' => ℓ :: policy_as_list p'
  | _ => nil
  end.

Fixpoint list_as_policy (l: list policy_label): policy :=
  match l with
  | nil => ∎
  | h :: t => h ⇝ (list_as_policy t)
  end.

(* Joins two policy_label labels. *)
Definition policy_label_join (lhs rhs: policy_label): policy_label :=
  match lhs, rhs with
    | policy_top, _ => lhs
    | _, policy_top => rhs
    | policy_bot, _ => rhs
    | _, policy_bot => lhs
    | policy_select, policy_select => lhs
    | policy_select, policy_transform _ => lhs
    | policy_select, policy_agg _ => lhs
    | policy_select, policy_noise _ => lhs
    | policy_transform _, policy_select => rhs
    | policy_transform ℓ1, policy_transform ℓ2 => policy_transform (set_inter transop_dec ℓ1 ℓ2)
    | policy_transform _, policy_agg _ => lhs
    | policy_transform _, policy_noise _ => lhs
    | policy_agg _, policy_select => rhs
    | policy_agg _, policy_transform _ => rhs
    | policy_agg ℓ1, policy_agg ℓ2 => policy_agg (set_inter aggop_dec ℓ1 ℓ2)
    | policy_agg _, policy_noise _ => lhs
    | policy_noise _, policy_select => rhs
    | policy_noise _, policy_transform _ => rhs
    | policy_noise _, policy_agg _ => rhs
    | policy_noise p1, policy_noise p2 =>
        match p1, p2 with
          | differential_privacy (ε1, δ1), differential_privacy (ε2, δ2) =>
              let ε := min ε1 ε2 in
              let δ := min δ1 δ2 in
                policy_noise (differential_privacy (ε, δ))
        end
  end.

(* Meets two policy_label labels; not used but for compatibility with the type class definition. *)
Definition policy_meet (lhs rhs: policy_label): policy_label :=
  match lhs, rhs with
    | policy_top, _ => rhs
    | _, policy_top => lhs
    | policy_bot, _ => lhs
    | _, policy_bot => rhs
    | policy_select, policy_select => lhs
    | policy_select, policy_transform _ => rhs
    | policy_select, policy_agg _ => rhs
    | policy_select, policy_noise _ => rhs
    | policy_transform _, policy_select => lhs
    | policy_transform ℓ1, policy_transform ℓ2 => policy_transform (set_union transop_dec ℓ1 ℓ2)
    | policy_transform _, policy_agg _ => rhs
    | policy_transform _, policy_noise _ => rhs
    | policy_agg _, policy_select => lhs
    | policy_agg _, policy_transform _ => lhs
    | policy_agg ℓ1, policy_agg ℓ2 => policy_agg (set_union aggop_dec ℓ1 ℓ2)
    | policy_agg _, policy_noise _ => rhs
    | policy_noise _, policy_select => lhs
    | policy_noise _, policy_transform _ => lhs
    | policy_noise _, policy_agg _ => lhs
    | policy_noise p1, policy_noise p2 =>
        match p1, p2 with
          | differential_privacy (ε1, δ1), differential_privacy (ε2, δ2) =>
              let ε := max ε1 ε2 in
              let δ := max δ1 δ2 in
                policy_noise (differential_privacy (ε, δ))
        end
  end.

Definition policy_option_meet (lhs rhs: option policy_label): option policy_label :=
  match lhs, rhs with
    | None, _ => None
    | _, None => None
    | Some lhs', Some rhs' => Some (policy_meet lhs' rhs')
  end.

Definition policy_option_eq (lhs rhs: option policy_label): Prop :=
  match lhs, rhs with
    | None, None => True
    | Some lhs', Some rhs' => policy_label_eq lhs' rhs'
    | _, _ => False
  end.

Global Instance policy_eq_eqv: Equivalence (@policy_label_eq).
  constructor; unfold policy_label_eq.
  - unfold Reflexive. intros. destruct x; try reflexivity.
    destruct n. destruct d. auto.
  - unfold Symmetric. intros. destruct x; destruct y; try reflexivity; try contradiction;
    try symmetry; auto.
    destruct n0, n, d, d0. intuition.
  - unfold Transitive. intros. destruct x; destruct y; try transitivity; try contradiction;
    try symmetry; auto; try destruct z; try contradiction; try eapply transitivity; eauto.
    destruct n0, n, n1, d, d0, d1. intuition; subst; auto.
Defined.

Definition policy_option_eq_eqv: Equivalence policy_option_eq.
refine (
  @Build_Equivalence _ _ _ _ _
).
  - unfold Reflexive, policy_label_eq. intros. unfold policy_option_eq.
    destruct x; try reflexivity.
  - unfold Symmetric, policy_label_eq. intros. unfold policy_option_eq in *.
    destruct x; destruct y; try reflexivity; try contradiction.
    apply policy_eq_eqv. assumption.
  - unfold Transitive. intros. induction x; induction y; induction z; try intuition auto with *.
    simpl in *. eapply transitivity; eassumption.
Defined.

Lemma policy_join_comm: ∀ (lhs rhs: policy_label),
  policy_label_eq (policy_label_join lhs rhs) (policy_label_join rhs lhs).
Proof.
  intros. destruct lhs; destruct rhs; simpl; try reflexivity.
  - destruct n, d. intuition.
  - unfold set_eq. intros. split; apply set_inter_comm_in.
  - unfold set_eq. intros. split; apply set_inter_comm_in.
  - destruct n, d. intuition.
  - destruct n, n0, d, d0. unfold policy_label_eq. simpl.
    assert (min n n1 = min n1 n) by lia.
    assert (min n0 n2 = min n2 n0) by lia.
    rewrite H. rewrite H0. intuition.
Qed.

Lemma policy_meet_comm: ∀ (lhs rhs: policy_label),
  policy_label_eq (policy_meet lhs rhs) (policy_meet rhs lhs).
Proof.
  intros. destruct lhs; destruct rhs; simpl; try reflexivity.
  - destruct n, d. intuition.
  - unfold set_eq. intros. split; apply set_union_comm_in.
  - destruct n, d. intuition.
  - unfold set_eq. intros. split; apply set_union_comm_in.
  - destruct n, d. intuition.
  - destruct n, d. intuition.
  - destruct n, d. intuition.
  - destruct n, d. intuition.
  - destruct n, n0, d, d0. unfold policy_label_eq. simpl.
    assert (max n n1 = max n1 n) by lia.
    assert (max n0 n2 = max n2 n0) by lia.
    rewrite H. rewrite H0. intuition.
  - destruct n, d. intuition.
  - destruct n, d. intuition.
Qed.

Lemma policy_join_absorp: ∀ (lhs rhs: policy_label),
  policy_label_eq (policy_label_join lhs (policy_meet lhs rhs)) lhs.
Proof.
  intros. destruct lhs; destruct rhs; simpl; try reflexivity; try unfold set_eq; intros;
  try rewrite set_inter_refl_in; intuition; auto with *;
  try (apply set_inter_elim in H; destruct H; assumption);
  try (apply set_inter_intro; intuition);
  try (apply set_union_elim in H; destruct H; assumption).
  try (apply set_union_intro; intuition).
  - apply set_union_intro. intuition.
  - destruct n, d. intuition.
  - destruct n, d. simpl. lia.
  - destruct n, d. simpl. lia.
  - destruct n, d. simpl. lia.
  - destruct n, n0, d, d0. simpl. split; lia.
  - destruct n, d. simpl. lia.
Qed.

Lemma policy_join_assoc: ∀ (a b c: policy_label),
  policy_label_eq (policy_label_join a (policy_label_join b c)) (policy_label_join (policy_label_join a b) c).
Proof.
  intros. destruct a; destruct b; destruct c; try reflexivity;
  try (destruct n, n0, n1, n2, d, d0, d1, d2; simpl; intuition; lia);
  try (destruct n, n0, d, d0; auto); simpl; auto;
  try (apply set_inter_assoc_in; auto); try reflexivity.
  destruct n1, d. simpl. intuition; lia.
Qed.

Lemma policy_meet_assoc: ∀ (a b c: policy_label),
  policy_label_eq (policy_meet a (policy_meet b c)) (policy_meet (policy_meet a b) c).
Proof.
  intros. destruct a; destruct b; destruct c; simpl; try reflexivity;
  try (destruct n, d; lia); try (destruct n, n0, d, d0; auto with *);
  try (destruct n, n0, n1, n2, d, d0, d1, d2; simpl; intuition; lia);
  try (apply set_union_assoc_in; auto); try reflexivity.
  destruct n1, d. simpl. intuition; lia.
Qed.

Global Instance policy_lattice: lattice policy_label.
  econstructor.
  - eapply policy_eq_eqv.
  - intros. eapply policy_meet_comm.
  - intros. eapply policy_join_comm.
  - intros. eapply policy_join_assoc.
  - intros. eapply policy_join_absorp.
  - intros. eapply policy_meet_assoc.
  - intros. simpl. destruct a; destruct b; simpl;
    try (apply set_union_refl_in);
    try reflexivity;
    try (destruct n, d; simpl; lia);
    try (destruct n0, d; simpl; lia).
    + unfold set_eq. intros. split; intros.
      * apply set_union_elim in H; destruct H. auto. apply set_inter_elim in H. destruct H. auto.
      * apply set_union_intro. left. assumption.
    + unfold set_eq. intros. split; intros.
      * apply set_union_elim in H; destruct H. auto. apply set_inter_elim in H. destruct H. auto.
      * apply set_union_intro. left. assumption.
    + destruct n, n0, d, d0. simpl. lia.
  - intros. instantiate (1:=Policy.policy_bot). simpl. apply policy_eq_eqv. destruct a; reflexivity.
  - intros. instantiate (1:=policy_top). simpl. induction a; reflexivity.
  - intros. simpl. induction a; reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl in *.
    destruct x1; destruct x2; destruct y1; destruct y2; simpl; try apply policy_eq_eqv; try inversion H0; try inversion H; auto; simpl in *; unfold set_eq in *; intros; (try split; intros).
    + apply set_inter_intro; specialize H with a. specialize H0 with a. destruct H, H0.
      * apply H. apply set_inter_elim in H1. intuition.
      * apply H0. apply set_inter_elim in H1. intuition.
    + specialize H with a. specialize H0 with a.
      destruct H, H0. apply set_inter_elim in H1. apply set_inter_intro; intuition.
    + apply set_inter_elim in H1. specialize H with a. specialize H0 with a.
      apply set_inter_intro; intuition.
    + apply set_inter_intro; specialize H with a; specialize H0 with a.
      * apply set_inter_elim in H1. intuition.
      * apply set_inter_elim in H1. intuition.
    + destruct n, n1, n0, n2, d, d0, d1, d2. simpl in *. split; lia.
  - intros. simpl in *.
    destruct x1; destruct x2; destruct y1; destruct y2; simpl; try apply policy_eq_eqv; try inversion H0; try inversion H; auto; simpl in *; unfold set_eq in *; intros; (try split; intros).
    + apply set_union_intro.
      apply set_union_elim in H1. destruct H1. left. apply H. assumption. right. apply H0. assumption.
    + apply set_union_intro.
      apply set_union_elim in H1. destruct H1. left. apply H. assumption. right. apply H0. assumption.
    + apply set_union_intro.
      apply set_union_elim in H1. destruct H1. left. apply H. assumption. right. apply H0. assumption.
    + apply set_union_intro.
      apply set_union_elim in H1. destruct H1. left. apply H. assumption. right. apply H0. assumption.
    + destruct n, n1, n0, n2, d, d0, d1, d2. simpl in *. split; lia.
  - intros. simpl in *. destruct x; destruct y; destruct z; simpl; try apply policy_eq_eqv;
    try inversion H0; try inversion H; simpl in *; unfold set_eq in *; intros; (try split; intros); auto.
    + apply set_inter_elim in H1. destruct H1. assumption.
    + apply set_inter_intro.
      * apply H in H1. apply H0 in H1. apply set_inter_elim in H1. destruct H1. assumption.
      * assumption.
    + apply set_inter_elim in H1. destruct H1. assumption.
    + apply set_inter_intro.
      * apply H in H1. apply H0 in H1. apply set_inter_elim in H1. destruct H1. assumption.
      * assumption.
    + destruct n, n0, d, d0; lia.
    + destruct n, n0, n1, d, d0, d1; simpl in *; lia.
  - intros. simpl in *. destruct x; destruct y; destruct z; simpl; try apply policy_eq_eqv;
    try inversion H0; try inversion H; simpl in *; unfold set_eq in *; intros; (try split; intros); auto.
    + apply set_inter_elim in H1. destruct H1. assumption.
    + apply set_inter_intro.
      * apply H0 in H1. apply set_inter_elim in H1. destruct H1. apply H in H1. assumption.
      * assumption.
    + apply set_inter_elim in H1. destruct H1. assumption.
    + apply set_inter_intro.
      * apply H0 in H1. apply set_inter_elim in H1. destruct H1. apply H in H1. assumption.
      * assumption.
    + destruct n, n0, n1, d, d0, d1; simpl in *; lia.
Defined.

Inductive valid_policy: policy → Prop :=
  | valid_policy_clean: valid_policy ∎
  | valid_policy_atomic: ∀ ℓ, valid_policy (∘ ℓ)
  | valid_policy_declass: ∀ ℓ1 ℓ2 p, valid_policy (ℓ2 ⇝ p) → ℓ2 ⊑ ℓ1 → valid_policy (ℓ1 ⇝ (ℓ2 ⇝ p))
.

Global Instance policy_setoid: Setoid policy_label.
refine (
  @Build_Setoid policy_label policy_label_eq policy_eq_eqv
).
Defined.

Definition policy_lt (lhs rhs: policy_label): Prop :=
  flowsto lhs rhs ∧ lhs =/= rhs.
Definition policy_le (lhs rhs: policy_label): Prop :=
  flowsto lhs rhs.
Global Instance policy_lt_trans: Transitive policy_lt.
  unfold Transitive.
  intros. destruct x; destruct y; destruct z; unfold policy_lt in *; intuition auto with *;
  unfold "⊑" in *; simpl in *; unfold complement, policy_label_eq in *; intros; try inversion H0;
  auto with *. 
  - destruct n, n0, d, d0. simpl. lia.
  - assert (s0 ⊂ s).
    {
      red. split; red; intros.
      - unfold set_eq in H1. specialize H1 with a. destruct H1. apply H4 in H0.
        apply set_inter_elim in H0. intuition.
      - apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros.  unfold set_eq in H. specialize H with a. destruct H. apply H5 in H4.
        apply set_inter_elim in H4. intuition.
      - intros. apply H3. symmetry. auto.
    }
    assert (s1 ⊂ s) by (eapply transitivity; eauto).
    red in H5. destruct H5.
    red in H6.
    red. split; intros.
    + apply set_inter_elim in H7. intuition.
    + apply set_inter_intro. 
      * red in H5. apply H5. assumption.
      * assumption.
  - assert (s0 ⊂ s).
    {
      red. split; red.
      - intros. unfold set_eq in H1. specialize H1 with a. destruct H1. intuition.
        apply set_inter_elim in H6. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros. unfold set_eq in H. specialize H with a. destruct H. intuition.
        apply set_inter_elim in H7. intuition.
      - intros. apply H3. symmetry. auto.
    }
    assert (s1 ⊂ s) by (eapply transitivity; eauto).
    red in H6. destruct H6. red in H7.
    apply H7. symmetry. assumption.
  - assert (s0 ⊂ s).
    {
      red. split; red.
      - intros. unfold set_eq in H1. specialize H1 with a. destruct H1. apply H4 in H0.
        apply set_inter_elim in H0. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros.  unfold set_eq in H. specialize H with a. destruct H. apply H5 in H4.
        apply set_inter_elim in H4. intuition.
      - intros. apply H3. symmetry. auto.
    }
    assert (s1 ⊂ s) by (eapply transitivity; eauto).
    red in H5. destruct H5.
    red in H6.
    red. split; intros.
    + apply set_inter_elim in H7. intuition.
    + apply set_inter_intro. 
      * red in H5. apply H5. assumption.
      * assumption.
  - assert (s0 ⊂ s).
    {
      red. split; red.
      - intros. unfold set_eq in H1. specialize H1 with a. destruct H1. intuition.
        apply set_inter_elim in H6. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros. unfold set_eq in H. specialize H with a. destruct H. intuition.
        apply set_inter_elim in H7. intuition.
      - intros. apply H3. symmetry. auto.
    }
    assert (s1 ⊂ s) by (eapply transitivity; eauto).
    red in H6. destruct H6. red in H5.
    intuition auto with *.
  - destruct n, n0, n1, d, d0, d1. simpl in *. intuition; lia.
  - destruct n, n0, n1, d, d0, d1. simpl in *. intuition; lia.
Qed.

Ltac simpl_ord := unfold policy_lt; unfold "⊑"; (split; auto with *); simpl; unfold complement; intros; unfold policy_label_eq in *; inversion H.
Ltac ordering_lt := try (apply OrderedType.LT; auto; simpl_ord).
Ltac ordering_eq := try (apply OrderedType.EQ; auto; simpl_ord).
Ltac ordering_gt := try (apply OrderedType.GT; auto; simpl_ord).

Lemma policy_eq_dec': ∀ (lhs rhs: policy_label), {lhs === rhs} + {lhs =/= rhs}.
Proof.
  intros. destruct (policy_eq_dec lhs rhs).
  - left. unfold equiv. auto.
  - right. unfold equiv. auto.
Qed.

Lemma valid_policy_implies: ∀ ℓ p, valid_policy (ℓ ⇝ p) → valid_policy p.
Proof.
  induction p.
  - subst. intros. constructor.
  - intros. inversion H; subst. assumption.
Qed.

Lemma valid_policy_stronger: ∀ ℓ1 ℓ2 p, ℓ2 ⊑ ℓ1 → valid_policy (ℓ2 ⇝ p) → valid_policy (ℓ1 ⇝ p).
Proof.
  destruct p.
  - subst. intros. constructor.
  - constructor. eapply valid_policy_implies. eauto.
    inversion H0. subst. eapply transitivity; eauto.
Qed.

Lemma valid_policy_dec: ∀ p, {valid_policy p} + {~ valid_policy p}.
Proof.
  induction p.
  - subst. left. constructor.
  - destruct IHp.
    + induction p0.
      * subst. left. constructor.
      * destruct (flowsto_dec _ policy_lattice policy_eq_dec' p0 p).
        -- left. constructor; auto.
        -- right. red. intros. inversion H. subst. intuition.
    + right. red. intros. inversion H. subst. apply n. constructor. apply n. subst. assumption.
Qed.

Lemma policy_lt_dec: ∀ (lhs rhs: policy_label), {policy_lt lhs rhs} + {~ (policy_lt lhs rhs)}.
Proof.
  destruct lhs; destruct rhs.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - left. simpl_ord.
  - left. simpl_ord.
  - left. simpl_ord.
  - left. simpl_ord.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - destruct (set_eq_dec transop_dec s s0).
    + right. red. intros. inversion H. simpl in *. auto.
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' (policy_transform s) (policy_transform s0)).
      * left. simpl_ord.
      * right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - left. simpl_ord.
  - destruct (set_eq_dec aggop_dec s s0).
    + right. red. intros. inversion H. simpl in *. auto.
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' (policy_agg s) (policy_agg s0)).
      * left. simpl_ord.
      * right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - right. red. intros. inversion H. simpl in *. auto.
  - left. simpl_ord.
  - left. simpl_ord.
  - left. simpl_ord.
  - destruct n, n0, d, d0.
    + destruct (nat_dec n n1). destruct (nat_dec n0 n2); try destruct s; try destruct s0; simpl; intuition; simpl.
      * right. intros. unfold policy_lt in *. unfold flowsto in *. intuition.
        simpl in *. unfold complement in H1. simpl in *. lia.
      * right. intros. unfold policy_lt in *. unfold flowsto in *. intuition.
        simpl in *. unfold complement in H1. simpl in *. lia.
      * right. intros. unfold policy_lt in *. unfold flowsto in *. intuition.
        simpl in *. unfold complement in H1. simpl in *. lia.
      * right. intros. unfold policy_lt in *. unfold flowsto in *. intuition.
        simpl in *. unfold complement in H1. simpl in *. lia.
      * right. intros. unfold policy_lt in *. unfold flowsto in *. intuition.
        simpl in *. unfold complement in H1. simpl in *. lia.
      * left. intros. unfold policy_lt in *. unfold flowsto in *. intuition.
        simpl. subst. lia. simpl. red. intros. simpl in *. lia.
      * destruct (nat_dec n0 n2).
        -- destruct s. right. red. simpl. unfold policy_lt in *. unfold flowsto in *. intuition.
           simpl in *. red in H1. intuition. simpl in *. lia.
           left. red. simpl. unfold policy_lt in *. unfold flowsto in *. split; auto; try lia.
           red. simpl. intros. lia.
        -- left. red. simpl. unfold policy_lt in *. unfold flowsto in *. split; auto; try lia.
           red. simpl. intros. lia.
  - left. simpl_ord.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
  - right. red. intros. inversion H. simpl in *. auto.
Qed.

Reserved Notation "x ⪯ y" (at level 10, no associativity).
Inductive policy_ordering: policy → policy → Prop :=
  (* 
    ---------
     ∎ ⪯ p
  *)
  | policy_ordering_trivial: ∀ p, valid_policy p → ∎ ⪯ p

  | policy_ordering_spec: ∀ p1 p1' p2 p2' ℓ1 ℓ2,
      p1 = ℓ1 ⇝ p1' ∧ p2 = ℓ2 ⇝ p2' →
      valid_policy p1 ∧ valid_policy p2 →
      ℓ1 ⊑ ℓ2 →
   (* ---------- *)
      p1' ⪯ p2' → p1 ⪯ p2
where "x ⪯ y" := (policy_ordering x y).

Definition policy_eq (lhs rhs: policy): Prop := lhs ⪯ rhs ∧ rhs ⪯ lhs.
Notation "x ≡ y" := (policy_eq x y) (at level 10, no associativity).

Inductive max_policy: policy → policy → policy → Prop :=
  | MaxPolicy: ∀ p1 p2, p1 ⪯ p2 → max_policy p1 p2 p2
  | MaxPolicySym: ∀ p1 p2, p2 ⪯ p1 → max_policy p1 p2 p1
.

Lemma preceq_implies: ∀ ℓ1 p1 p,
  (ℓ1 ⇝ p1) ⪯ p → p1 ⪯ p.
Proof.
  intros ℓ1 p1. generalize dependent ℓ1.
  induction p1; intros; inversion H; intuition; subst.
  - constructor. assumption.
  - inversion H6. subst.
    inversion H0. subst. econstructor; eauto. etransitivity; eauto.
Qed.

Lemma preceq_refl: ∀ p, valid_policy p → p ⪯ p.
Proof.
  induction p; intros.
  - repeat constructor.
  - econstructor; eauto.
    + reflexivity.
    + apply IHp. inversion H; subst.
      * constructor.
      * assumption.
Qed.

(* A helper lemma to avoid `inversion` on the premise. *)
Lemma preceq_implies_valid: ∀ p1 p2, p1 ⪯ p2 → valid_policy p1 ∧ valid_policy p2.
Proof.
  intros. inversion H; subst; intuition. constructor.
Qed.

Lemma max_policy_max: ∀ p1 p2 p3,
  max_policy p1 p2 p3 → p1 ⪯ p3 ∧ p2 ⪯ p3.
Proof.
  intros. inversion H; subst; intuition.
  all: apply preceq_refl; inversion H0; subst; intuition.
Qed.

Lemma preceq_trans: ∀ p1 p2 p3,
  p1 ⪯ p2 → p2 ⪯ p3 → p1 ⪯ p3.
Proof.
  intros p1 p2 p3. generalize dependent p2. generalize dependent p1.
  induction p3; intros; inversion H0; subst; try assumption.
  - destruct H1. discriminate.
  - inversion H; subst; try discriminate.
    + constructor; auto.
    + destruct H2. discriminate.
  - destruct p1.
    + constructor. intuition.
    + econstructor; eauto.
      * inversion H. subst. inversion H0. subst. intuition. intuition.
      * destruct H1. inversion H5. subst.
        inversion H. subst.
        destruct H1. inversion H1. inversion H9. subst.
        etransitivity; eauto.
      * destruct H1. inversion H5. subst.
        eapply IHp3; eauto. inversion H.
        subst. destruct H1. inversion H1. inversion H9. subst. assumption.
Qed.

(* We export this so that we can use `transitivity` as one of Coq's built-in tactics. *)
Global Instance preceq_istrans: Transitive policy_ordering.
  unfold Transitive. apply preceq_trans.
Defined.

Reserved Notation "x '∪' y '=' z" (at level 10, y at next level, z at next level, no associativity).
Inductive policy_join: policy → policy → policy → Prop :=
  | policy_join_bot_lhs: ∀ p, valid_policy p → ∎ ∪ p = p
  | policy_join_bot_rhs: ∀ p, valid_policy p → p ∪ ∎ = p
  | policy_join_spec1: ∀ ℓ1 ℓ2 p1 p2 p3,
      valid_policy (ℓ1 ⇝ p1) →
      valid_policy (ℓ2 ⇝ p2) →
      ℓ2 ⊑ ℓ1 → 
      p1 ∪ (ℓ2 ⇝ p2) = p3 →
      (* ------------- *)
      (ℓ1 ⇝ p1) ∪ (ℓ2 ⇝ p2) = (ℓ1 ⇝ p3)
  | policy_join_spec2: ∀ ℓ1 ℓ2 p1 p2 p3,
      valid_policy (ℓ1 ⇝ p1) →
      valid_policy (ℓ2 ⇝ p2) →
      ℓ1 ⊑ ℓ2 →
      (ℓ1 ⇝ p1) ∪ p2 = p3 →
      (* ------------- *)
      (ℓ1 ⇝ p1) ∪ (ℓ2 ⇝ p2) = (ℓ2 ⇝ p3)
where "x '∪' y '=' z" := (policy_join x y z).

Lemma policy_join_valid: ∀ p1 p2 p3,
  p1 ∪ p2 = p3 → valid_policy p3.
Proof.
  intros p1 p2 p3. generalize dependent p2. generalize dependent p1.
  induction p3; intros; inversion H; subst; try constructor; auto.
  - inversion H7; subst; try (econstructor; eauto). inversion H2. subst. assumption.
  - inversion H7; subst; (econstructor; eauto). inversion H3. subst. assumption.
Qed.

Lemma policy_join_stronger: ∀ p1 p2 p3,
  p1 ∪ p2 = p3 → p1 ⪯ p3 ∧ p2 ⪯ p3.
Proof.
  intros.
  assert (valid_policy p3) by (apply policy_join_valid in H; auto).
  induction H; subst; intuition.
  - constructor; assumption.
  - apply preceq_refl; assumption.
  - apply preceq_refl; assumption.
  - constructor; assumption.
  - econstructor; eauto. reflexivity. apply IHpolicy_join.
    apply valid_policy_implies in H0. assumption.
  - econstructor; eauto.
    assert (valid_policy p3) by (apply valid_policy_implies in H0; assumption).
    apply IHpolicy_join in H4. destruct H4.
    apply preceq_implies in H5. assumption.
  - econstructor; eauto.
    assert (valid_policy p3) by (apply valid_policy_implies in H0; assumption).
    apply IHpolicy_join in H4. destruct H4.
    apply preceq_implies in H4. assumption.
  - econstructor; eauto. reflexivity.
    apply IHpolicy_join. apply valid_policy_implies in H0. assumption.
Qed.

Axiom policy_join_terminate: ∀ p1 p2, ∃ p3, p1 ∪ p2 = p3.

(*
  The `policy_ord_dec` lemma provides a decision procedure for the policy ordering.

  This lemma is important: Decidability is related to the concept of completeness in logic.
  If a property is decidable, then for any given input, we can either prove that the property
  holds, or prove that it doesn't hold. This is a strong form of completeness.

  A policy should be either "weaker" or "stronger" than another policy, or they should be equal.
  Thus, we can use `destruct` to discuss the different cases in the function application.
*)
Lemma policy_ord_dec: ∀ (lhs rhs: policy), valid_policy lhs → valid_policy rhs → { lhs ⪯ rhs } + { ~ (lhs ⪯ rhs) }.
Proof.
  induction lhs; induction rhs; intros; try specialize IHlhs with (rhs := rhs); intuition; subst.
  - left. subst. constructor. assumption.
  - left. subst. constructor. assumption.
  - right. unfold not. intros. inversion H1. subst. intuition. discriminate.
  - destruct IHlhs; try assumption;
    try (apply valid_policy_implies in H0; assumption); try (apply valid_policy_implies in H; assumption).
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
      * left. econstructor; try assumption; try eapply valid_policy_implies; eauto.
      * right. unfold not in *. intros. apply n. inversion H2. subst. intuition.
        inversion H7. inversion H8. subst. assumption. 
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
      * right. unfold not in *. intros. apply f. inversion H2. subst. intuition.
        inversion H7. inversion H8. subst. assumption. 
      * right. unfold not in *. intros. apply f. inversion H2. subst. intuition.
        inversion H7. inversion H8. subst. assumption. 
Qed.

Definition context := ctx policy.

Fixpoint policy_context_valid (Γ: ctx policy): Prop :=
  match Γ with
  | nil => True
  | (_, p) :: Γ' => valid_policy p ∧ policy_context_valid Γ'
  end.

Theorem policy_context_valid_dec: ∀ Γ, {policy_context_valid Γ} + {~ policy_context_valid Γ}.
Proof.
  induction Γ.
  - left. constructor.
  - destruct IHΓ.
    + destruct a. destruct (valid_policy_dec p0).
      * left. constructor; auto.
      * right. unfold not. intros. inversion H. subst. intuition.
    + right. unfold not. intros. apply n. simpl in H. destruct a. intuition.
Qed.

Section Tests.

Example policy_lhs := (policy_top ⇝ (policy_agg nil ⇝ (∘ policy_bot))).
Example policy_rhs := (policy_select ⇝ (policy_transform nil ⇝ (∘ (policy_noise (differential_privacy (2, 1)))))).
Example policy_res :=
(policy_top ⇝
  (policy_select ⇝
    (policy_transform nil ⇝
      (policy_agg nil ⇝
        ((policy_noise (differential_privacy (2, 1))) ⇝
          (∘ policy_bot)))))).

Example policy_lhs' := (∘ policy_bot).
Example policy_rhs' := (∘ policy_select).
Example policy_res' := (policy_select ⇝ (∘ policy_bot)).

Example policy_lhs'' := ∎.
Example policy_rhs'' := (∘ policy_select).
Example policy_trans_lhs := (policy_transform nil) ⇝ (∘ (policy_agg nil)).
Example policy_trans_rhs := (∘ (policy_transform (UnaryTransOp Identity :: nil))).

Example join_correct: policy_lhs ∪ policy_rhs = policy_res.
Proof.
  repeat constructor; intuition.
Qed.

Example join_correct': policy_lhs' ∪ policy_rhs' = policy_res'.
Proof.
  repeat constructor; intuition.
Qed.

Example join_correct'': policy_rhs'' ∪ policy_lhs'' = policy_rhs''.
Proof.
  repeat constructor.
Qed.

End Tests.

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
Hint Unfold tuple: core.

Fixpoint tuple_np (ty: tuple_type): Set :=
  match ty with
    | nil => unit
    | bt :: t' => (type_to_coq_type bt) * tuple_np t'
  end%type.

Fixpoint bounded_list (l: list nat) (ty: tuple_type): Prop :=
  match l with
    | nil => True
    | n :: l' => n < List.length ty ∧ bounded_list l' ty
  end.

Fixpoint tuple_as_cell_ids ty (t: tuple ty): list nat :=
  match ty as ty' return ty = ty' → tuple ty' → list nat with
  | nil => fun _ _ => nil
  | bt :: t' => fun _ t => (snd (fst t)) :: tuple_as_cell_ids t' (snd t)
  end eq_refl t.

Fixpoint inject_tuple_id
  (ty: tuple_type)
  (t: tuple_np ty)
  (stream: Stream)
: tuple ty :=
  match ty return ∀ (t: tuple_np ty) (stream: Stream), tuple ty with
    | nil => fun _ _ => tt
    | bt :: t' => fun t stream => (((fst t), (hd stream)), inject_tuple_id t' (snd t) (tl stream))
  end t stream.

Fixpoint inject_new_id s (tp: Tuple.tuple (♭ s)) (start: nat): Tuple.tuple (♭ s).
refine (
  match s as s' return s = s' → Tuple.tuple (♭ s') → nat → Tuple.tuple (♭ s') with
    | nil => fun _ _ _ => tt
    | bt :: t' => fun _ tp start => _
  end eq_refl tp start
).
  destruct bt.
  simpl in tp. destruct tp as [ [ty _] tp ].
  pose (ty, start) as hd.
  pose (inject_new_id _ tp (S start)) as tl.
  exact (hd, tl).
Defined.

Fixpoint tuple_value_lt (ty: tuple_type): ∀ (lhs rhs: tuple ty), Prop :=
  match ty return ∀ (lhs rhs: tuple ty), Prop with
    | nil => fun _ _ => False
    | _ :: t' => fun lhs rhs => lt (fst (fst lhs)) (fst (fst rhs)) ∨
      (fst (fst lhs)) == (fst (fst rhs)) ∧ tuple_value_lt t' (snd lhs) (snd rhs)
  end.

Fixpoint tuple_total_lt (ty: tuple_type): ∀ (lhs rhs: tuple ty), Prop :=
  match ty return ∀ (lhs rhs: tuple ty), Prop with
    | nil => fun _ _ => False
    | _ :: t' => fun lhs rhs => lt (fst lhs) (fst rhs) ∨
      (fst lhs) == (fst rhs) ∧ tuple_total_lt t' (snd lhs) (snd rhs)
  end.

(* A tuple type is a list of basic types. *)

Example example_tuple_ty : tuple_type := StringType :: BoolType :: nil.
Example example_tuple: tuple_np example_tuple_ty := ("abcd"%string, (true, tt)).
Example example_tuple_ty' : tuple_type := IntegerType :: nil.
Example example_tuple' : tuple_np example_tuple_ty' := (1, tt).
Example example_tuple'' : tuple_np (example_tuple_ty' ++ example_tuple_ty) := 
  (1, ("abcd"%string, (true, tt))).

(* Cast the type of the tuple, if needed. *)
Lemma tuple_cast: ∀ (ty1 ty2: tuple_type) (f: tuple_type → Set),
  f ty1 → ty1 = ty2 → f ty2.
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

Fixpoint tuple_value_eq (ty: tuple_type): ∀ (lhs rhs: tuple ty), Prop :=
  match ty return (∀ (lhs rhs: tuple ty), Prop) with
    | nil => fun _ _ => True
    | _ :: tl => fun lhs rhs => 
      (fst (fst lhs)) == (fst (fst rhs)) ∧ tuple_value_eq tl (snd lhs) (snd rhs)
  end.

Fixpoint tuple_value_eqb (ty: tuple_type): ∀ (lhs rhs: tuple ty), bool :=
  match ty return (∀ (lhs rhs: tuple ty), bool) with
    | nil => fun _ _ => true
    | _ :: tl => fun lhs rhs => 
      andb (value_eq _ _ (fst (fst lhs)) (fst (fst rhs))) (tuple_value_eqb tl (snd lhs) (snd rhs))
  end.

Fixpoint tuple_total_eq (ty: tuple_type): ∀ (lhs rhs: tuple ty), Prop :=
  match ty return (∀ (lhs rhs: tuple ty), Prop) with
    | nil => fun _ _ => True
    | _ :: tl => fun lhs rhs => 
      (fst lhs) == (fst rhs) ∧ tuple_total_eq tl (snd lhs) (snd rhs)
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
    eapply transitivity; eauto.
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

Definition nth: ∀ (ty: tuple_type) (n: nat) (extract: n < List.length ty), Cell.cell.
refine
(fix nth' (ty: tuple_type) (n: nat):
  n < List.length ty → Cell.cell :=
     match ty as ty' , n as n' return ty = ty' → n = n' → n' < List.length ty' → Cell.cell with
      | x :: y , 0 => fun _ _ _ => x
      | x :: y , S n' => fun _ _ _ => nth' y n' _
      | _ , _ => fun _ _ _ => False_rec _ _
    end (refl_equal _) (refl_equal _)).
Proof.
  - simpl in *. lia.
  - simpl in *. lia.
Defined.


Definition nth_nocheck: ∀ (ty: tuple_type) (n: nat), option Cell.cell.
refine
(fix nth' (ty: tuple_type) (n: nat): option Cell.cell :=
     match ty as ty' , n as n' return ty = ty' → n = n' → option Cell.cell with
      | x :: y , 0 => fun _ _  => Some x
      | x :: y , S n' => fun _ _  => nth' y n'
      | _ , _ => fun _ _ => None
    end (refl_equal _) (refl_equal _)).
Defined.

(* FIXME: ensures that types match between `c` and `x`. *)
(* Only matched types are allowed to transition. *)
Definition set_nth_type_match: ∀ (ty: tuple_type) (n: nat) (c: Cell.cell) (extract: n < List.length ty),
  tuple ty -> option (tuple ty).
refine
(fix set_nth' (ty: tuple_type) (n: nat) (c: Cell.cell):
  n < List.length ty -> tuple ty -> option (tuple ty) :=
  match ty as ty', n as n'
    return ty = ty' -> n = n' -> n' < List.length ty' -> tuple ty' -> option (tuple ty') with
      | x :: y, 0 => fun _ _ _ t => _
      | x :: y, S n' => fun _ _ _ t => match set_nth' y n' c _ (snd t) with
                                          | None => None
                                          | Some t' => Some (fst t, t')
                                        end
      | _, _ => fun _ _ _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
Proof.
  - simpl in *. lia.
  - exact (Some t).
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

Definition nth_col_tuple: ∀ (ty: tuple_type) (n : nat) (extract: n < List.length ty), tuple ty → tuple ((nth ty n extract) :: nil).
refine (
  fix nth_col_tuple' (ty: tuple_type) (n : nat): ∀ (extract: n < List.length ty),
    tuple ty → tuple ((nth ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' → n = n' → 
            ∀ (extract: n' < List.length ty'), tuple ty' → tuple ((nth ty' n' extract) :: nil) with
        | _ :: l', 0 => fun _ _ _ t => ((fst t), tt)
        | _ :: l', S n' => fun _ _ _ t => nth_col_tuple' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. lia.
Defined.

(*
  @param ty The type of the tuples.
  @param l A list of natural numbers representing the indices of the columns to be extracted.
  @param extract A bounded list that ensures the indices in `l` are within the bounds of `ty`.
  @param tuple The original tuple from which to extract the subtuple.
  @return A subtuple extracted from the original tuple.

  The `subtuple` function extracts a subtuple from a given tuple. The subtuple is specified by
  a list of natural numbers `l`, which represent the indices of the columns to be extracted.
*)
Fixpoint subtuple (l: list nat): ∀ (ty: tuple_type) (extract: bounded_list l ty), tuple ty → tuple (ntypes l ty extract).
  intros. destruct l.
  - exact tt.
  - destruct extract.
    rename H into t.
    pose (nth_col_tuple ty n l0 t).
    specialize subtuple with (l := l) (ty := ty) (extract := b).
    pose (subtuple t) as subtuple'.
    pose (tuple_concat _ _ t0 subtuple') as res.
    exact res.
Defined.

Definition extract_as_cell_id: ∀ (ty: tuple_type) (t: tuple ty), list nat.
refine (
  fix extract_as_cell' (ty: tuple_type) (t: tuple ty): list nat :=
    match ty as ty' return tuple ty' → list nat with
      | nil => fun _ => nil
      | bt :: t' => _
    end t
).
Proof.
  intros. simpl in H.
  pose (fst H). pose (snd H).
  apply extract_as_cell' in t0.
  exact ((snd p) :: t0).
Defined.

Global Instance nth_col_tuple_proper_eq
(ty: tuple_type) (n: nat) (extract: n < List.length ty):
  Proper (equiv ==> equiv) (nth_col_tuple ty n extract).
Proof.
  unfold Proper, respectful. intros. rewrite H. reflexivity.
Qed.

(* Without `policy_label` extracted! *)
Definition nth_np: ∀ (ty: tuple_type) (n: nat) (extract: n < List.length ty), basic_type.
  intros.
  exact (nth ty n extract).
Defined.

(* Without `policy_label` extracted! *)
Definition nth_col_tuple_np: ∀ (ty: tuple_type) (n : nat) (extract: n < List.length ty), tuple ty → tuple_np ((nth_np ty n extract) :: nil).
refine (
  fix nth_col_tuple_np' (ty: tuple_type) (n : nat): ∀ (extract: n < List.length ty),
    tuple ty → tuple_np ((nth_np ty n extract) :: nil) :=
      match ty as ty', n as n' return ty = ty' → n = n' → 
            ∀ (extract: n' < List.length ty'), tuple ty' → tuple_np ((nth_np ty' n' extract) :: nil) with
        | _ :: l', 0 => fun _ _ _ t => ((fst (fst t)), tt)
        | _ :: l', S n' => fun _ _ _ t => nth_col_tuple_np' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
simpl in *. lia.
Defined.

Global Instance nth_col_tuple_np_proper_eq
(ty: tuple_type) (n: nat) (extract: n < List.length ty):
  Proper (equiv ==> equiv) (nth_col_tuple_np ty n extract).
Proof.
  unfold Proper, respectful. intros. rewrite H. reflexivity.
Qed.

Global Instance tuple_total_eq_setoid (ty: tuple_type): Setoid (tuple ty).
  exists (tuple_total_eq ty).
  apply tuple_total_eq_eqv.
Defined.

Definition tuple_value_compare: ∀ (ty: tuple_type) (lhs rhs: tuple ty), 
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
      inversion H0; lia.
    * specialize (IHty _ _ H3 H2). assumption.
    * unfold bool_lt in H0. destruct H0. rewrite H in H1. rewrite H0 in H1. inversion H1.
    * specialize (IHty _ _ H3 H2). assumption.
    * rewrite H1 in H0. apply string_lt_neq in H0. auto with *.
    * specialize (IHty _ _ H3 H2). assumption.

  - intros. induction ty.
    * apply OrderedType.EQ. simpl. auto.
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

Example example_tuple_total_eq: tuple_total_eq example_tuple_ty example_tuple_lhs example_tuple_rhs.
Proof.
  simpl. repeat split; simpl; reflexivity.
Qed.

Example sublist := 1 :: nil.
Example sublist_bounded: bounded_list sublist example_tuple_ty.
Proof.
  simpl. split. lia. auto.
Defined.

Example subtuple': subtuple sublist example_tuple_ty sublist_bounded example_tuple_lhs = ((true, 2), tt).
Proof.
  reflexivity.
Qed.

Lemma schema_flat_2nd_arg_irrelevant_tuple: ∀ s hd snd_hd tl,
  s = hd :: tl → tuple (♭ (((fst hd, snd_hd) :: nil) ++ tl)) = tuple(♭ s).
Proof.
  intros. subst.
  simpl. destruct hd.
  simpl. reflexivity.
Qed.

End Tuple.

Ltac str_eq:= auto; simpl in *; unfold char_eq in *; unfold char_lt in *; lia.

Section Facts.
  Context {ty: Tuple.tuple_type}.

  Notation "a <~ b":= (Tuple.tuple_value_lt ty a b) (at level 70, no associativity):
    type_scope.
  Notation "a <<~ b":= (Tuple.tuple_total_lt ty a b) (at level 70, no associativity):
    type_scope.

  Theorem bounded_list_dec: ∀ l1 l2, Tuple.bounded_list l1 l2 ∨ ¬ (Tuple.bounded_list l1 l2).
  Proof.
    induction l1; intros.
    - left. simpl. auto.
    - destruct IHl1 with (l2 := l2).
      + destruct (Compare_dec.lt_dec a (Datatypes.length l2)).
        * left. simpl. auto.
        * right. simpl. auto.
          red. intros. destruct H0. contradiction.
      + right. simpl. red. intros. destruct H0. contradiction.
  Qed.
End Facts.

Notation "'<<' x '>>'" := (x, 0) (at level 0, x at next level).
Notation "'<<' x ; x0 '>>'" := (x, x0) (at level 0, x at next level, x0 at next level).
Notation "'[[' x , y , .. , z ']]'" := (x, (y, .. (z, tt) ..)) (at level 0, x at next level, y at next level, z at next level).
Notation "'[[' x ']]'" := (x, tt) (at level 0, x at next level).
Notation "x '⇝' y" := (Policy.policy_declass x y) (at level 10, no associativity).
Notation "'∎'" := (Policy.policy_clean) (at level 0, no associativity).
Notation "'∘' p " := (p ⇝ ∎) (at level 10, no associativity).
Notation "x '⪯' y" := (Policy.policy_ordering x y) (at level 10, no associativity).
Notation "x '∪' y '=' z" := (Policy.policy_join x y z) (at level 10, y at next level, z at next level, no associativity).
Notation "x '≡' y" := (Policy.policy_eq x y) (at level 10, no associativity).
Notation "x '↑' y '=' z" := (Policy.max_policy x y z) (at level 10, y at next level, z at next level, no associativity).
