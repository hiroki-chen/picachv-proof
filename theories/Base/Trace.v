Require Import Arith.
Require Import List.
Require Import Unicode.Utf8.

Require Import DataModel.
Require Import Types.
Require Import Util.

Inductive prov_type: Set :=
  | prov_trans_unary: un_op → prov_type
  | prov_trans_binary: ∀ bt, bin_op → type_to_coq_type bt → prov_type
  | prov_agg: agg_op → prov_type
  (* Just re-use it; should be fine. *)
  | prov_udf: trans_op → prov_type
  | prov_noise: noise_op → prov_type
  | prov_join: prov_type
.

Definition prov_type_eqb (τ1 τ2: prov_type): bool.
  refine (match τ1, τ2 with
  | prov_trans_unary op1, prov_trans_unary op2 => un_op_eqb op1 op2
  | prov_trans_binary bt1 op1 v1, prov_trans_binary bt2 op2 v2 => andb (bin_op_eqb op1 op2) _
  | prov_agg op1, prov_agg op2 => agg_op_eqb op1 op2
  | prov_noise op1, prov_noise op2 => noise_op_eqb op1 op2
  | prov_join, prov_join => true
  | prov_udf op1, prov_udf op2 => trans_op_eqb op1 op2
  | _, _ => false
  end).
  destruct (type_matches bt1 bt2) eqn: Heq.
  - apply type_matches_eq in Heq. subst.
    destruct bt2; simpl in *.
    + destruct (Nat.eqb v1 v2).
      * apply true.
      * apply false.
    + destruct (Bool.eqb v1 v2).
      * apply true.
      * apply false.
    + destruct (String.eqb v1 v2).
      * apply true.
      * apply false.
  - apply false.
Defined.

Inductive trace_ty: Type :=
  (* ⊥ *)
  | TrEmpty: Policy.policy → trace_ty
  (* Linear trace: op → current policy → predecessors *)
  | TrLinear: prov_type → Policy.policy → trace_ty → trace_ty
  (* Branching trace. *)
  | TrBranch: prov_type → Policy.policy → list trace_ty → trace_ty
  (* Binary expressions *)
  | TrBinary: prov_type → Policy.policy → trace_ty → trace_ty → trace_ty  
.

Definition extract_policy tr :=
  match tr with
  | TrEmpty p => p
  | TrLinear _ p _ => p
  | TrBranch _ p _ => p
  | TrBinary _ p _ _ => p
  end.

(*
 * A trace is a list of tuples recording how a given data cell is transitioned
 * from one policy to another; it also bookkeeps the provenance information.
 *)
Definition trace := ctx trace_ty.

(* σ ::= ⟨ Γ, β ⟩; the program state. *)
Definition σ := (Policy.context * budget)%type.


(*
 * Checks whether a policy p1 can be downgraded to p2 using op.
 *)
Definition valid_prov (τ: prov_type) (p1 p2: Policy.policy): Prop :=
  (*
   * First of all we must ensure that the level of policies are lowered, which would
   * otherwise make no sense at all.
   *)
  p2 ⪯ p1 ∧
  (*
   * Next we check if `p1` can be "lowered". This is ensured by `p1` ⪯ `∘ op`
   *)
    match τ with
      (*
      * Adding `p ⪯ ∘ op` should be enough for the condition as this is equivalent to
      * `(first label p) ⊑ op`, the proof of which is trivial and intuitive.
      *)
      | prov_trans_unary op => p2 ⪯ (∘ (Policy.policy_transform ((UnaryTransOp op) :: nil)))
      | prov_trans_binary bt op v => p2 ⪯ (∘ (Policy.policy_transform ((BinaryTransOp bt op v) :: nil)))
      | prov_agg op => p2 ⪯ (∘ (Policy.policy_agg (op :: nil)))
      | prov_noise op => p2 ⪯ (∘ (Policy.policy_noise op))
      | _ => True
    end
.

(*
 * For a cell to be released (i.e., it can be shared freely), it must be the case that all policies are satisfied.
 * Fortunately, we have `policy_clean`. This means that we can just check whether the policy is clean.
 *)
Definition can_release p: Prop := p = ∎.

(* TODO: Define this. *)
Definition budget_bounded (β: budget): Prop := True.

Notation "p1 '=[' p ']=>' p2" := (valid_prov p p1 p2)
  (at level 10, p at next level, p2 at next level).

(* 
 *                      ----< tr1
 *                     /
 * trace: join / agg --< lbl  -----< tr2
 *                     \
 *                      ----< ...
 *)
Inductive branch_ok: Policy.policy → list trace_ty → Prop :=
  | BranchEmptyOk: ∀ lbl, branch_ok lbl nil
  | BranchConsOk: ∀ lbl lbl1 tr hd tl,
      tr = hd :: tl →
      lbl1 = extract_policy hd →
      lbl1 ⪯ lbl →
      branch_ok lbl tl →
      branch_ok lbl tr
.

(*
 * Checks against for each element, can it be released via the current label?
 *)
Inductive valid_transition: prov_type → Policy.policy → trace_ty → Prop :=
  (* tr: old (higher) *)
  (* lbl: new (lower) *)
  | ValidTransition: ∀ prov lbl lbl' tr,
      lbl' = extract_policy tr →
      lbl' =[ prov ]=> lbl →
      valid_transition prov lbl tr
.

(*
 * Checks against the list element, can it be released via the current label?
 *)
Inductive label_transition_valid_impl: prov_type → Policy.policy → list (trace_ty) → Prop :=
  | LabelTransitionImplNil: ∀ prov lbl, label_transition_valid_impl prov lbl nil
  | LabelTransitionImplCons: ∀ prov lbl tr hd tl,
      tr = hd :: tl →
      label_transition_valid_impl prov lbl tl →
      (* hd: old trace (higher) *)
      valid_transition prov lbl hd →
      label_transition_valid_impl prov lbl tr
.

Inductive binary_ok: prov_type → Policy.policy → trace_ty → trace_ty → Prop :=
  | BinaryOkAllEmpty: ∀ prov lbl trace1 trace2,
    (* Basically we can do anything with non-policy guarded data. *)
      trace1 = TrEmpty (∎) ∧ trace2 = TrEmpty (∎) →
      binary_ok prov lbl trace1 trace2
  | BinaryOkCannotDisclose: ∀ prov lbl trace1 trace2,
      lbl = (∘ Policy.policy_top) →
      binary_ok prov lbl trace1 trace2
  | BinaryOkLhsEmpty: ∀ prov lbl trace1 trace2,
      extract_policy trace1 = ∎ →
      valid_transition prov lbl trace2 →
      binary_ok prov lbl trace1 trace2
  | BinaryOkRhsEmpty: ∀ prov lbl trace1 trace2,
      extract_policy trace2 = ∎ →
      valid_transition prov lbl trace1 →
      binary_ok prov lbl trace1 trace2
.

Inductive label_transition_valid: trace_ty → Prop :=
  | LabelTransitionTrEmpty: ∀ p, label_transition_valid (TrEmpty p)
  | LabelTransitionTrLinear: ∀ tr prov lbl l,
      tr = TrLinear prov lbl l →
      label_transition_valid_impl prov lbl (l :: nil) →
      label_transition_valid tr
  | LabelTransitionTrBranch: ∀ tr lbl prov trace,
      tr = TrBranch prov lbl trace →
      Forall (λ x, label_transition_valid x) trace →
      branch_ok lbl trace →
      label_transition_valid tr
  | LabelTransitionTrBinary: ∀ tr prov lbl trace1 trace2,
    tr = TrBinary prov lbl trace1 trace2 →
    binary_ok prov lbl trace1 trace2 →
    label_transition_valid tr
.

(*
 * We iterate over the trace information and checks for each cell id if its
 * corresponding policy transition is indeed valid and enforced in the course of
 * the query execution trace.
 *
 * This somehow resembles the following Fixpoint function:
 *
 * Fixpoint trace_ok tr :=
 *  match tr with
 *  | nil => True
 *  | hd :: tl => label_transition_valid (snd hd) ∧ trace_ok tl
 *  end.
 *)
Inductive trace_ok: trace → Prop :=
  | TraceEmpty: trace_ok nil
  | TraceCons: ∀ tr hd tl,
      tr = hd :: tl →
      label_transition_valid (snd hd) →
      trace_ok tl →
      trace_ok (hd :: tl)
.

(*
 * Checks if the trace faithfully "mirror"s the policy context.
 *)
Definition trace_consistent (tr: ctx trace_ty) (Γ: ctx Policy.policy): Prop :=
  match tr with
  | nil => True
  | (id, tr_ty) :: tl =>
    match label_lookup Γ id with
    | Some p => p ⪯ (extract_policy tr_ty)
    | None => False
    end
  end.

(* Definition trace_valid tr Γ := *)

Lemma label_transition_valid_impl_merge_app: ∀ body1 body2 prov lbl,
  label_transition_valid_impl prov lbl body1 ∧
  label_transition_valid_impl prov lbl body2 →
  label_transition_valid_impl prov lbl (body1 ++ body2).
Proof.
  induction body1; intros; simpl in *; intuition.
  induction body2.
  - rewrite app_nil_r. auto.
  - econstructor; eauto.
    + eapply IHbody1. split.
      * inversion H0. subst. inversion H. subst. assumption.
      * assumption.
    + inversion H0. subst. inversion H. subst. assumption.
Qed.

Lemma trace_ok_app_cons_tail: ∀ a tr1 tr2,
   trace_ok (tr1 ++ tr2) ∧ label_transition_valid (snd a) →
   trace_ok (tr1 ++ a :: tr2).
Proof.
  induction tr1; intros; simpl in *; intuition; (econstructor; eauto); inversion H0.
  - assumption.
  - subst. apply IHtr1. econstructor; eauto.
Qed.

Lemma trace_ok_app_comm: ∀ tr1 tr2,
  trace_ok (tr1 ++ tr2) →
  trace_ok (tr2 ++ tr1).
Proof.
  induction tr1; intros; simpl in *.
  - rewrite app_nil_r. assumption.
  - inversion H. subst. apply IHtr1 in H4.
    apply trace_ok_app_cons_tail. intuition.
Qed.

Lemma update_label_trace_ok_spec: ∀ tr id tr_new,
  trace_ok tr ∧ label_transition_valid tr_new →
  trace_ok (update_label tr id tr_new).
Proof.
  induction tr; intros; intuition.
  simpl. destruct a. destruct (Nat.eqb id n) eqn: Hn.
  - apply Nat.eqb_eq in Hn. subst.
    inversion H0. subst.
    econstructor; eauto. apply trace_ok_app_comm.
    econstructor; eauto.
  - inversion H0. subst. simpl. econstructor; eauto.
Qed.

Lemma label_lookup_no_effect: ∀ tr id item,
  trace_ok tr →
  label_lookup tr id = Some item →
  label_transition_valid item.
Proof.
  induction tr.
  - discriminate.
  - intros. destruct a. simpl in H0. destruct (Nat.eqb id n) eqn: Hn.
    + inversion H0; subst. inversion H; subst. auto.
    + eapply IHtr; eauto. inversion H; subst. auto.
Qed.
