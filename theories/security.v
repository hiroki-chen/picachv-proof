Require Import List.
Require Import Logic.Eqdep_dec Logic.EqdepFacts.
Require Import Unicode.Utf8.

Require Import config.
Require Import data_model.
Require Import lattice.
Require Import relation.
Require Import semantics.
Require Import trace.
Require Import types.
Require Import util.

(*
  For a cell to be released (i.e., it can be shared freely), it must be the case that all policies are satisfied.
  Fortunately, we have `policy_clean`. This means that we can just check whether the policy is clean.
*)
Definition can_release p: Prop := p = ∎.

(* TODO: Define this. *)
Definition budget_bounded (β: budget): Prop := True.

(*
 * Rules for the valid label transition.
 *)
Inductive downgrade_ok: prov_type → Policy.policy → Policy.policy → Prop :=
  | DowngradeUnary: ∀ prov op p1 p2,
      p2 ⪯ p1 →
      prov = prov_trans_unary op →
      downgrade_ok prov p1 p2
.

(* TODO: Implement this. *)
Notation "p1 '=[' p ']=>' p2" := (downgrade_ok p p1 p2)
  (at level 10, p at next level, p2 at next level).

Inductive join_ok: Policy.policy → trace_ty → trace_ty → Prop :=
  | JoinOk: ∀ lbl lbl1 lbl2 tr1 tr2,
      lbl1 = extract_policy tr1 →
      lbl2 = extract_policy tr2 →
      lbl1 ⪯ lbl →
      lbl2 ⪯ lbl →
      join_ok lbl tr1 tr2
.

(*
 * The dependency graph:
 *
 * label_transition_valid --> label_transition_valid_impl --> valid_transition
 *  ^                                                               |
 *  |                                                               |
 *  +---------------------------------------------------------------+
 *)
Inductive label_transition_valid: trace_ty → Prop :=
  | LabelTransitionTrEmpty: label_transition_valid ∅
  | LabelTransitionTrLinear: ∀ tr prov lbl l,
      tr = TrLinear prov lbl l →
      label_transition_valid_impl prov lbl l →
      label_transition_valid tr
  | LabelTransitionTrBranch: ∀ tr lbl prov tr1 tr2,
      tr = TrBranch prov lbl tr1 tr2 →
      label_transition_valid tr1 →
      label_transition_valid tr2 →
      join_ok lbl tr1 tr2 →
      label_transition_valid tr
(*
 * Checks against the list element, can it be released via the current label?
 *)
with
label_transition_valid_impl: prov_type → Policy.policy → list (trace_ty) → Prop :=
  | LabelTransitionImplNil: ∀ prov lbl, label_transition_valid_impl prov lbl nil
  | LabelTransitionImplCons: ∀ prov lbl tr hd tl,
      tr = hd :: tl →
      label_transition_valid_impl prov lbl tl →
      valid_transition prov lbl hd →
      label_transition_valid_impl prov lbl (hd :: tl)
(*
 * Checks against for each element, can it be released via the current label?
 *)
with
valid_transition: prov_type → Policy.policy → trace_ty → Prop :=
  | ValidEmpty: ∀ prov lbl, valid_transition prov lbl ∅
  | ValidTransition: ∀ prov lbl lbl' tr,
      lbl' = extract_policy tr →
      lbl =[ prov ]=> lbl' →
      valid_transition prov lbl tr
.

(*
 * We iterate over the trace information and checks for each cell id if its
 * corresponding policy transition is indeed valid and enforced in the course of
 * the query execution trace.
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
    ∀Γ, Γ′.Γ −→ Γ′ =⇒ ∀c′ ∈ Γ′.ℓ′1 ⊑ ℓ =⇒
      ∃C = {c1, · · · cn} −→ c′ =⇒
        ∀c ∈ C.(ℓ1, ℓ2) = Γ(c) ∧ ℓ1 ⊑ ℓ2 =⇒ Ok(ℓ1 ⇝o ℓ′1)

    Should we start from empty environment? Or this condition is unnecessary?
 *)

(*
 * This theorem is the main security theorem that states the following fact:
 *
 * Given an initial environment where the configuration is valid, one of the followings holds:
 * * The query evaluation results in an error, or
 * * There exists some configuration such that the query evaluation results in that configuration
 *   and the label transition is valid with regard to the cell provenance information, and that
 *   the budget is bounded.
 *
 * The proof is by induction on `o`.
 *
 * Note here we do not enforce how the data should be released, we only ensure that all the valid
 * transitions are enforced and that the budget is bounded. The release of data can be trivally
 * enforced by an extra epilogue function. The proof for that function is not included here.
 *)
Theorem secure_query:
  ∀ db o, ⟦ db o ⟧ ⇓ ⟦ ConfigError ⟧ ∨
    (∃ s c r σ tr,
      (* The output is valid. *)
      c = ConfigOut (RelationWrapped s r) σ tr ∧
      (* The evalaution goes to c. *)
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ ∧
      (* The transition of the trace is also valid. *)
      trace_ok tr ∧ budget_bounded (snd σ)).
Proof.
  (* induction o; intros; destruct H.
  - right.
    exists nil, (ConfigOut (RelationWrapped nil nil) c), db, Γ, β, p, nil. split.
    + specialize E_Empty with
      (c := c) (c' := ConfigOut (RelationWrapped nil nil) c) (db := db) (Γ := Γ) (β := β) (p := p).
      intros. intuition. subst. auto.
    + split.
      * subst. apply E_Empty with (c := ⟨ db Γ β p ⟩); auto.
      * split; constructor.
  - destruct db eqn: Hdb.
    + left. eapply E_GetRelationDbEmpty; subst; eauto.
    + destruct (database_get_contexts db n) as [ [ [ r' Γ' ] p' ] | ] eqn: Hget.
      * destruct r'. right.
        exists s0, (ConfigOut (RelationWrapped s0 r) (⟨ db Γ' β p' ⟩)), db, Γ', β, p', r.
        split; split; auto.
        -- eapply E_GetRelation with (db := db) (o := OperatorRel n).
          ++ red. intros. rewrite Hdb in H1. inversion H1.
          ++ reflexivity.
          ++ rewrite <- Hdb in H. eapply H.
          ++ eapply Hget.
          ++ auto.
        -- split; simpl.
          ++ destruct s0.
            ** constructor. reflexivity.
            ** 
          ++ inversion H1.
      * left. eapply E_GetRelationError with (db := db) (Γ := Γ) (β := β) (p := p); eauto.
        -- red. intros. subst. inversion H1.
        -- intuition. subst. reflexivity.
  - specialize (operator_always_terminate c o2).
    specialize (operator_always_terminate c o1).
    intros. intuition. subst.
    (*
      We need to introduce this existential variable *before* each sub-case to avoid
      scoping issues; otherwise, Coq will complain that it cannot find the variable.
    *)
    destruct H2 as [x H2]; destruct H1 as [x' H1]; try discriminate.
    + left. eapply E_UnionError.
      * reflexivity.
      * eapply H4.
      * eapply H5.
      * intuition.
    + assert (c ≠ ConfigError) by (subst; try discriminate). intuition. destruct H1.
      left. eapply E_UnionError; eauto.
    + assert (c ≠ ConfigError) by (subst; try discriminate). intuition. destruct H6.
      left. eapply E_UnionError; eauto.
    + assert (c ≠ ConfigError) by (subst; try discriminate). intuition.
      destruct H1; destruct H6; destruct x0; destruct x; subst; try discriminate; intuition.
      * left. eapply E_UnionError; eauto.
      * left. eapply E_UnionError; eauto.
      * left. eapply E_UnionError; eauto.
      * left. eapply E_UnionError; eauto.
      * inversion H1; subst; try discriminate.
      * inversion H2; subst; try discriminate.
      * left. eapply E_UnionError; eauto.
      * inversion H1; subst; try discriminate.
      * destruct r; destruct r0; destruct x0; destruct x.
        -- inversion H1; subst; try discriminate.
        -- inversion H2; subst; try discriminate.
        -- inversion H2; subst; try discriminate.
        -- inversion H1; subst; try discriminate.
        -- right.
          (* Now we need to discuss the equality of two schemas. *)
          destruct (list_eq_dec attribute_eq_dec s s0).
          ++ subst.
            pose (merged_p := merge_env p0 p1).
            pose (merged_Γ := merge_env c c0).
            pose (merged_β := calculate_budget b b0).
            exists s0, (ConfigOut (RelationWrapped _ (r ++ r0)) (⟨ d0 merged_Γ merged_β merged_p ⟩)),
                   d0, merged_Γ, merged_β, merged_p, (r ++ r0).
            intros. split.
            ** econstructor; eauto.
            ** split.
              --- destruct s0 eqn: Hs0; destruct (r ++ r0) eqn: Hr.
                +++ constructor. auto.
                +++ constructor. auto.
                +++ eapply valid_env.
                  *** intuition. discriminate.
                  *** eauto.
                  *** constructor.
                +++ 
                  (* Introduce the existential variable from hypothesis. *)
                  destruct H5 as [s'1 [c'1 [db'1 [Γ'1 [β'1 [p'1 [r'1 H5'] ] ] ] ] ] ].
                  destruct H4 as [s'2 [c'2 [db'2 [Γ'2 [β'2 [p'2 [r'2 H4'] ] ] ] ] ] ]. *)
                  
Admitted.
