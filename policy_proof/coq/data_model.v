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
*)
Inductive policy_label : Type :=
  | policy_bot : policy_label
  (* Should be something like `pred → policy_label` *)
  | policy_select: policy_label
  | policy_transform: set TransOp → policy_label
  | policy_agg: set AggOp → policy_label
  | policy_noise: NoiseOp → policy_label
  | policy_top : policy_label
.

(*
  The `policy` inductive type represents the different types of policies that can be applied
  to data in the data model. Each policy can be applied to a cell in a relation, and the effect
  of the policy depends on its type.
*)
Inductive policy: Type :=
  | policy_atomic: policy_label → policy
  | policy_declass: policy_label → policy → policy
.

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

(* Meets two policy_label labels. *)
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

Definition policy_eq (lhs rhs: policy_label): Prop :=
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

Definition policy_option_eq (lhs rhs: option policy_label): Prop :=
  match lhs, rhs with
    | None, None => True
    | Some lhs', Some rhs' => policy_eq lhs' rhs'
    | _, _ => False
  end.

Global Instance policy_eq_eqv: Equivalence (@policy_eq).
  constructor; unfold policy_eq.
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
  - unfold Reflexive, policy_eq. intros. unfold policy_option_eq.
    destruct x; try reflexivity.
  - unfold Symmetric, policy_eq. intros. unfold policy_option_eq in *.
    destruct x; destruct y; try reflexivity; try contradiction.
    apply policy_eq_eqv. assumption.
  - unfold Transitive. intros. induction x; induction y; induction z; try intuition auto with *.
    simpl in *. eapply transitivity; eassumption.
Defined.

Lemma policy_join_comm: ∀ (lhs rhs: policy_label),
  policy_eq (policy_label_join lhs rhs) (policy_label_join rhs lhs).
Proof.
  intros. destruct lhs; destruct rhs; simpl; try reflexivity.
  - destruct n, d. intuition.
  - unfold set_eq. intros. split; apply set_inter_comm_in.
  - unfold set_eq. intros. split; apply set_inter_comm_in.
  - destruct n, d. intuition.
  - destruct n, n0, d, d0. unfold policy_eq. simpl.
    assert (min n n1 = min n1 n) by lia.
    assert (min n0 n2 = min n2 n0) by lia.
    rewrite H. rewrite H0. intuition.
Qed.

Lemma policy_meet_comm: ∀ (lhs rhs: policy_label),
  policy_eq (policy_meet lhs rhs) (policy_meet rhs lhs).
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
  - destruct n, n0, d, d0. unfold policy_eq. simpl.
    assert (max n n1 = max n1 n) by lia.
    assert (max n0 n2 = max n2 n0) by lia.
    rewrite H. rewrite H0. intuition.
  - destruct n, d. intuition.
  - destruct n, d. intuition.
Qed.

Lemma policy_join_absorp: ∀ (lhs rhs: policy_label),
  policy_eq (policy_label_join lhs (policy_meet lhs rhs)) lhs.
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
  policy_eq (policy_label_join a (policy_label_join b c)) (policy_label_join (policy_label_join a b) c).
Proof.
  intros. destruct a; destruct b; destruct c; try reflexivity;
  try (destruct n, n0, n1, n2, d, d0, d1, d2; simpl; intuition; lia);
  try (destruct n, n0, d, d0; auto); simpl; auto;
  try (apply set_inter_assoc_in; auto); try reflexivity.
  destruct n1, d. simpl. intuition; lia.
Qed.

Lemma policy_meet_assoc: ∀ (a b c: policy_label),
  policy_eq (policy_meet a (policy_meet b c)) (policy_meet (policy_meet a b) c).
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
    + apply set_inter_intro; destruct H, H0.
      * apply H. apply set_inter_elim in H5. intuition.
      * apply H0. apply set_inter_elim in H5. intuition.
    + destruct H, H0. apply set_inter_elim in H5. apply set_inter_intro.
      * apply H6. intuition.
      * apply H2. intuition.
    + apply set_inter_elim in H5. apply set_inter_intro; destruct H, H0.
      * apply H. intuition.
      * apply H0. intuition.
    + apply set_inter_intro.
      * apply set_inter_elim in H5. destruct H5. apply H. auto.
      * apply set_inter_elim in H5. destruct H5. apply H0. auto.
    + destruct n, n1, n0, n2, d, d0, d1, d2. simpl in *. split; lia.
  - intros. simpl in *.
    destruct x1; destruct x2; destruct y1; destruct y2; simpl; try apply policy_eq_eqv; try inversion H0; try inversion H; auto; simpl in *; unfold set_eq in *; intros; (try split; intros).
    + apply set_union_intro.
      apply set_union_elim in H5. destruct H5. left. apply H. assumption. right. apply H0. assumption.
    + apply set_union_intro.
      apply set_union_elim in H5. destruct H5. left. apply H. assumption. right. apply H0. assumption.
    + apply set_union_intro.
      apply set_union_elim in H5. destruct H5. left. apply H. assumption. right. apply H0. assumption.
    + apply set_union_intro.
      apply set_union_elim in H5. destruct H5. left. apply H. assumption. right. apply H0. assumption.
    + destruct n, n1, n0, n2, d, d0, d1, d2. simpl in *. split; lia.
  - intros. simpl in *. destruct x; destruct y; destruct z; simpl; try apply policy_eq_eqv;
    try inversion H0; try inversion H; simpl in *; unfold set_eq in *; intros; (try split; intros); auto.
    + apply set_inter_elim in H5. destruct H5. assumption.
    + apply set_inter_intro.
      * apply H in H5. apply H0 in H5. apply set_inter_elim in H5. destruct H5. assumption.
      * assumption.
    + apply set_inter_elim in H5. destruct H5. assumption.
    + apply set_inter_intro.
      * apply H in H5. apply H0 in H5. apply set_inter_elim in H5. destruct H5. assumption.
      * assumption.
    + destruct n, n0, d, d0; lia.
    + destruct n, n0, n1, d, d0, d1; simpl in *; lia.
  - intros. simpl in *. destruct x; destruct y; destruct z; simpl; try apply policy_eq_eqv;
    try inversion H0; try inversion H; simpl in *; unfold set_eq in *; intros; (try split; intros); auto.
    + apply set_inter_elim in H5. destruct H5. assumption.
    + apply set_inter_intro.
      * apply H0 in H5. apply set_inter_elim in H5. destruct H5. apply H in H5. assumption.
      * assumption.
    + apply set_inter_elim in H5. destruct H5. assumption.
    + apply set_inter_intro.
      * apply H0 in H5. apply set_inter_elim in H5. destruct H5. apply H in H5. assumption.
      * assumption.
    + destruct n, n0, n1, d, d0, d1; simpl in *; lia.
Defined.

Global Instance policy_setoid: Setoid policy_label.
refine (
  @Build_Setoid policy_label policy_eq policy_eq_eqv
).
Defined.

Definition policy_lt (lhs rhs: policy_label): Prop :=
  flowsto lhs rhs ∧ lhs =/= rhs.
Definition policy_le (lhs rhs: policy_label): Prop :=
  flowsto lhs rhs.

Global Instance policy_lt_trans: Transitive policy_lt.
  unfold Transitive.
  intros. destruct x; destruct y; destruct z; unfold policy_lt in *; intuition auto with *;
  unfold "⊑" in *; simpl in *; unfold complement, policy_eq in *; intros; try inversion H0;
  auto with *. 
  - destruct n, n0, d, d0. simpl. lia.
  - assert (s0 ⊂ s).
    {
      red. split; red.
      - intros.  unfold set_eq in H1. destruct H1. apply H4 in H0.
        apply set_inter_elim in H0. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros.  unfold set_eq in H. destruct H. apply H5 in H4.
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
      - intros. unfold set_eq in H1. destruct H1. apply H7 in H6.
        apply set_inter_elim in H6. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros. unfold set_eq in H. destruct H. apply H8 in H7.
        apply set_inter_elim in H7. intuition.
      - intros. apply H3. symmetry. auto.
    }
    assert (s1 ⊂ s) by (eapply transitivity; eauto).
    red in H8. destruct H8. red in H9.
    apply H9. symmetry. assumption.
  - assert (s0 ⊂ s).
    {
      red. split; red.
      - intros.  unfold set_eq in H1. destruct H1. apply H4 in H0.
        apply set_inter_elim in H0. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros.  unfold set_eq in H. destruct H. apply H5 in H4.
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
      - intros. unfold set_eq in H1. destruct H1. apply H7 in H6.
        apply set_inter_elim in H6. intuition.
      - intros. apply H2. symmetry. auto.
    }
    assert (s1 ⊂ s0).
    {
      red. split; red.
      - intros. unfold set_eq in H. destruct H. apply H8 in H7.
        apply set_inter_elim in H7. intuition.
      - intros. apply H3. symmetry. auto.
    }
    assert (s1 ⊂ s) by (eapply transitivity; eauto).
    red in H8. destruct H8. red in H9.
    apply H9. symmetry. assumption.
  - destruct n, n0, n1, d, d0, d1. simpl in *. intuition; lia.
  - destruct n, n0, n1, d, d0, d1. simpl in *. intuition; lia.
Qed.

Ltac simpl_ord := unfold policy_lt; unfold "⊑"; (split; auto with *); simpl; unfold complement; intros; unfold policy_eq in *; inversion H.
Ltac ordering_lt := try (apply OrderedType.LT; auto; simpl_ord).
Ltac ordering_eq := try (apply OrderedType.EQ; auto; simpl_ord).
Ltac ordering_gt := try (apply OrderedType.GT; auto; simpl_ord).

Lemma policy_eq_dec: ∀ (lhs rhs: policy_label), {policy_eq lhs rhs} + {~ (policy_eq lhs rhs)}.
Proof.
  destruct lhs; destruct rhs; auto with *;
  try destruct (set_eq_dec _ transop_dec s s0);
  try destruct (set_eq_dec _ aggop_dec s s0).
  - left. auto.
  - right. auto.
  - left. auto.
  - right. auto.
  - destruct n, n0, d, d0. auto with *.
    destruct (nat_dec n n1). destruct (nat_dec n0 n2); try destruct s; try destruct s0; simpl; intuition.
    + right. lia.
    + right. lia.
    + right. lia.
    + right. lia.
    + right. lia.
    + simpl. right. lia.
Qed.

Lemma policy_eq_dec': ∀ (lhs rhs: policy_label), {lhs === rhs} + {lhs =/= rhs}.
Proof.
  intros. destruct (policy_eq_dec lhs rhs).
  - left. unfold equiv. auto.
  - right. unfold equiv. auto.
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
  - destruct (set_eq_dec _ transop_dec s s0).
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
  - destruct (set_eq_dec _ aggop_dec s s0).
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

Notation "x ⇝ y" := (policy_declass x y) (at level 10, no associativity).
Reserved Notation "x ⪯ y" (at level 10, no associativity).
Inductive policy_ordering: policy → policy → Prop :=
  (* 
    ---------
      ℓ1 ⪯ ℓ1
   *)
  | policy_ordering_refl: ∀ ℓ, policy_ordering ℓ ℓ
  (* 
     ℓ1 ⊑ ℓ2
    ---------
     ℓ1 ⪯ ℓ2
  *)
  | policy_ordering_trivial: ∀ ℓ1 ℓ2, ℓ1 ⊑ ℓ2 → (policy_atomic ℓ1) ⪯ (policy_atomic ℓ2)
  (*
     ℓ1 ⊑ ℓ2
    ---------
     ℓ1 ⪯ ℓ2 ⇝ p
  *)
  | policy_ordering_recur1: ∀ ℓ1 ℓ2 p, ℓ1 ⊑ ℓ2 → (policy_atomic ℓ1) ⪯ (ℓ2 ⇝ p)
  (*
    ℓ1 ⊑ ℓ2
    ---------
    ℓ1 ⇝ p ⪯ ℓ2
  *)
  | policy_ordering_recur2: ∀ ℓ1 ℓ2 p, ℓ1 ⊑ ℓ2 → (ℓ1 ⇝ p) ⪯ (policy_atomic ℓ2)
  (*
    ℓ' ⊑ ℓ'   p ⪯ p'
    -----------------
    ℓ ⇝ p ⪯ ℓ' ⇝ p'
  *)
  | policy_ordering_spec: ∀ ℓ ℓ' p p', ℓ ⊑ ℓ' → p ⪯ p' → (ℓ ⇝ p) ⪯ (ℓ' ⇝ p')
where "x ⪯ y" := (policy_ordering x y).

Global Instance ord_proper: Proper (equiv ==> equiv) policy_ordering.
Admitted.

(*
  The `policy_ord_dec` lemma provides a decision procedure for the policy ordering.

  This lemma is important: Decidability is related to the concept of completeness in logic.
  If a property is decidable, then for any given input, we can either prove that the property
  holds, or prove that it doesn't hold. This is a strong form of completeness.

  A policy should be either "weaker" or "stronger" than another policy, or they should be equal.
  Thus, we can use `destruct` to discuss the different cases in the function application.
*)
Lemma policy_ord_dec: ∀ (lhs rhs: policy), {lhs ⪯ rhs} + {~ (lhs ⪯ rhs)}.
Proof.
  induction lhs; induction rhs.
  - destruct (policy_eq_dec p p0).
    + left. subst. constructor. red. rewrite p1. apply join_idem.
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
      * left. constructor. assumption.
      * right. red. intros. inversion H. subst. apply n0. red. apply join_idem. intuition.
  - destruct (policy_eq_dec p p0).
    + left. constructor. red. rewrite p1. apply join_idem.
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
      * left. constructor. assumption.
      * right. red. intros. inversion H. subst. apply n0. red. intuition.
  - destruct (policy_eq_dec p p0).
    + left. constructor. red. rewrite p1. apply join_idem.
    + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
      * left. constructor. assumption.
      * right. red. intros. inversion H. subst. apply n0. red. intuition.
  - destruct (policy_eq_dec p p0); specialize IHlhs with rhs; destruct IHlhs.
      + left. constructor. red. rewrite p1. apply join_idem. assumption.
      + right. red. intros. apply n.
        inversion H.
        * constructor.
        * subst. assumption.
      + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
        * left. constructor. assumption. assumption.
        * right. red. intros. apply n.
          inversion H.
          -- subst. reflexivity.
          -- subst. intuition.
      + destruct (flowsto_dec _ policy_lattice policy_eq_dec' p p0).
        * right. red. intros. apply n.
          inversion H.
          -- subst. reflexivity.
          -- subst. intuition.
        * right. red. intros. apply n.
          inversion H.
          -- subst. reflexivity.
          -- subst. intuition.
Qed.

Definition context: Type := list (nat * policy).
Fixpoint label_lookup (id: nat) (Γ: context): option policy :=
  match Γ with
    | nil => None
    | (id', p) :: l' =>
        if Nat.eqb id id' then Some p else label_lookup id l'
  end.

Fixpoint next_available_id (Γ: context) (n: nat): nat :=
  match Γ with
    | nil => n
    | (id, _) :: l' => S (next_available_id l' (max id n))
  end.

Lemma new_id_non_exists: ∀ (Γ: context) (n: nat),
  ~ (In (next_available_id Γ n) (map fst Γ)).
Admitted.

Definition id_of_length (Γ: context) (len: nat): list nat :=
  let next_id := next_available_id Γ 0 in
    (fix id_of_length (len: nat) (next_id: nat): list nat :=
      match len with
        | O => nil
        | S len' => next_id :: id_of_length len' (S next_id)
      end) len next_id.

Fixpoint update_label (id: nat) (ctx: context) (p: policy): context :=
  match ctx with
  | nil => nil
  | (id', p') :: l' =>
      if Nat.eqb id id' then (id, p) :: l' else (id', p') :: update_label id l' p
  end.

Lemma update_valid: ∀ id ctx p p',
  label_lookup id ctx = Some p →
  label_lookup id (update_label id ctx p') = Some p'.
Proof.
  induction ctx.
  - simpl in *. intros. inversion H.
  - destruct a.
    + simpl in *. destruct (Nat.eqb id n) eqn: Heq.
      * intros. simpl. rewrite Nat.eqb_refl. reflexivity.
      * intros. simpl in *. rewrite Heq. specialize IHctx with (p := p0) (p' := p').
        apply IHctx. assumption.
Qed.
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
    | n :: l' => n < List.length ty ∧ bounded_list l' ty
  end.

Fixpoint inject_tuple_id
  (ty: tuple_type)
  (t: tuple_np ty)
  (id: nat)
: tuple ty :=
  match ty return ∀ (t: tuple_np ty) (id: nat), tuple ty with
    | nil => fun _  _ => tt
    | bt :: t' => fun t id => (((fst t), id), inject_tuple_id t' (snd t) (id + 1))
  end t id.

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
        |_  :: l', 0 => fun _ _ _ t => ((fst t), tt)
        | _ :: l', S n' => fun _ _ _ t => nth_col_tuple' l' n' _ (snd t)
        | _, _ => fun _ _ _ => fun _ => False_rec _ _
      end (refl_equal _) (refl_equal _)).
Proof.
  simpl in *. lia.
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

Notation "'<<' x '>>'" := (x, 0) (at level 0, x at next level).
Notation "'<<' x ; x0 '>>'" := (x, x0) (at level 0, x at next level, x0 at next level).
Notation "'[[' x , y , .. , z ']]'" := (x, (y, .. (z, tt) ..)) (at level 0, x at next level, y at next level, z at next level).
Notation "'[[' x ']]'" := (x, tt) (at level 0, x at next level).
