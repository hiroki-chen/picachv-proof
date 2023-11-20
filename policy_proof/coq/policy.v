(* The policy library. *)

Require Import lattice.
Require Import RelationClasses.
Require Import Lia.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import List.

Require Import ordering.

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
    | policy_bot, _ => rhs
    | _, policy_bot => lhs
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
    | policy_bot, _ => policy_bot
    | _, policy_bot => policy_bot
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
  - intros. instantiate (1:=policy_bot). simpl. apply policy_eq_eqv. 
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

Global Instance policy_option_lattice: lattice (option policy).
Admitted.

Global Instance policy_setoid: Setoid policy.
refine (
  @Build_Setoid policy policy_eq policy_eq_eqv
).
Defined.

(* The active policy context. *)
Definition policy_encoding := (option policy * option policy)%type.
Definition context := list (nat * policy_encoding)%type.
Definition can_release (p: policy_encoding): Prop := flowsto (fst p) (snd p).
(* Lookup the policy context and check if the cell has been associated with an active policy. *)
Fixpoint label_lookup (id: nat) (ctx: context):
  option policy_encoding :=
    match ctx with
      | nil => None
      | (id', (cur, disc)) :: l' =>
          if id == id' then Some (cur, disc) else label_lookup id l'
    end.
