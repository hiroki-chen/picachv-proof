Require Import Arith.
Require Import List.
Require Import Logic.Eqdep_dec Logic.EqdepFacts.
Require Import Unicode.Utf8.

Require Import config.
Require Import data_model.
Require Import expression.
Require Import lattice.
Require Import relation.
Require Import semantics.
Require Import trace.
Require Import types.
Require Import util.

Definition valid_prov (τ: prov_type) (p1 p2: Policy.policy): Prop :=
  p1 ⪯ p2 ∧
  match τ with
    | prov_trans_unary op => (∘ (Policy.policy_transform ((unary_trans_op op) :: nil))) ⪯ p1
    | prov_trans_binary op => (∘ (Policy.policy_transform ((binary_trans_op op) :: nil))) ⪯ p1
    | prov_agg op => (∘ (Policy.policy_agg (op :: nil))) ⪯ p1
    | prov_noise op => (∘ (Policy.policy_noise op)) ⪯ p1
    | prov_join => True
  end.

(*
 * For a cell to be released (i.e., it can be shared freely), it must be the case that all policies are satisfied.
 * Fortunately, we have `policy_clean`. This means that we can just check whether the policy is clean.
 *)
Definition can_release p: Prop := p = ∎.

(* TODO: Define this. *)
Definition budget_bounded (β: budget): Prop := True.

Notation "p1 '=[' p ']=>' p2" := (valid_prov p p1 p2)
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
 * Checks against for each element, can it be released via the current label?
 *)
Inductive
valid_transition: prov_type → Policy.policy → trace_ty → Prop :=
  | ValidEmpty: ∀ prov lbl, valid_transition prov lbl ∅
  | ValidTransition: ∀ prov lbl lbl' tr,
      lbl' = extract_policy tr →
      lbl =[ prov ]=> lbl' →
      valid_transition prov lbl tr
.

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

Lemma database_get_contexts_trace_ok: ∀ db s r n Γ β tr,
  database_get_contexts db n = Some (RelationWrapped s r, Γ, tr, β) →
  trace_ok tr.
Proof.
  induction db; intros.
  - simpl in *. discriminate.
  - destruct (Nat.eqb n 0) eqn: Hn0.
    + apply Nat.eqb_eq in Hn0. subst.
      simpl in H. destruct (inject_id_helper s l 10).
      inversion H. subst. apply inj_pair2_eq_dec in H2. subst.
      induction Γ.
      * simpl. constructor.
      * simpl. destruct a. econstructor.
        -- reflexivity.
        -- constructor.
        -- apply IHΓ. reflexivity.
      * apply list_eq_dec. apply attribute_eq_dec.
    + simpl in H. rewrite Hn0 in H. apply IHdb in H. auto.
Qed.

Lemma trace_ok_dedup_ok: ∀ tr,
  trace_ok tr →
  trace_ok (dedup tr).
Proof.
  induction tr; intros.
  - constructor.
  - simpl. destruct (existsb (λ x : nat * trace_ty, fst x =? fst a) tr).
    + apply IHtr. inversion H. assumption.
    + inversion H. subst. econstructor.
      * reflexivity.
      * assumption.
      * apply IHtr. assumption.
Qed.

Lemma trace_ok_merge_ok: ∀ tr1 tr2,
  trace_ok tr1 →
  trace_ok tr2 →
  trace_ok (tr1 ⊍ tr2).
Proof.
  induction tr1; intros; unfold merge_env in *; simpl.
  - apply trace_ok_dedup_ok. assumption.
  - destruct (existsb (λ x : nat * trace_ty, fst x =? fst a) (tr1 ++ tr2)).
    + apply IHtr1. inversion H. assumption. assumption.
    + inversion H. subst. econstructor.
      * reflexivity.
      * assumption.
      * apply IHtr1. assumption. assumption.
Qed.

Lemma eval_ok: ∀ n in_agg Γ Γ' β β' tr tr' tp tp' gb gb' expr v,
  trace_ok tr →
  eval n expr in_agg ((Γ, β), tr, tp, gb) (Some (((Γ', β'), tr', tp', gb', v))) →
  trace_ok tr'.
Proof.
Admitted.

Lemma eval_expr_in_relation_ok: ∀ s r ty r' Γ Γ' β β' tr tr' expr,
  trace_ok tr →
  eval_expr_in_relation s r ty Γ β tr expr (Some (r', Γ', β', tr')) →
  trace_ok tr'.
Proof.
  induction r; intros; inversion H0; subst;
  try discriminate; intuition;
  inversion H10; try inversion H1; subst; try discriminate.
  - inversion H9. subst. apply inj_pair2_eq_dec in H26. subst.
    + eapply IHr; eauto.
    + apply basic_type_eq_dec.
  - inversion H9. inversion H29. subst. eapply IHr; eauto.
  - inversion H9. subst. eapply IHr.
    + apply eval_ok in H1. eapply H1. assumption.
    + eauto.
  - cheat. (* Let us do it later. *)
Qed.

Lemma join_policy_and_trace_ok: ∀ l1 l2 com Γ1 Γ2 Γ tr1 tr2 tr,
  trace_ok tr1 →
  trace_ok tr2 →
  join_policy_and_trace l1 l2 com Γ1 Γ2 tr1 tr2 (Some (Γ, tr)) →
  trace_ok tr.
Proof.
  induction l1; intros; inversion H1; subst;
  try discriminate; try (apply trace_ok_merge_ok; auto).
  inversion H4. inversion H5. subst. clear H4.
  econstructor; eauto; simpl.
  - inversion H21; subst. intuition.
    eapply LabelTransitionTrBranch with (tr1 := tr1') (tr2 := tr2'); eauto.
    + reflexivity.
    + apply label_lookup_no_effect in H11; auto.
    + apply label_lookup_no_effect in H12; auto.
    + econstructor; eauto. 
  - assert (trace_ok tl4) by (inversion H; subst; auto).
    assert (trace_ok tl5) by (inversion H0; subst; auto).
    eapply IHl1 with (tr1 := tl4) (tr2 := tl5); eauto.
Qed.

Lemma trace_ok_join_ok_aux: ∀ s1 s2 join_by t r rout Γ1 Γ2 Γ β1 β2 β tr1 tr2 tr,
  trace_ok tr1 →
  trace_ok tr2 →
  relation_join_by_prv_helper s1 s2 join_by t r Γ1 Γ2 β1 β2 tr1 tr2 (Some (rout, Γ, β, tr)) →
  trace_ok tr.
Proof.
  (* Induction follows the pattern of the inductive relation. *)
  induction r; intros; inversion H1; subst.
  - apply trace_ok_merge_ok; auto.
  - apply inj_pair2_eq_dec in H2, H3, H4, H4, H4; subst.
    + discriminate.
    + apply list_eq_dec. apply Nat.eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
  - apply inj_pair2_eq_dec in H2, H3, H4, H4, H4; subst.
    + inversion H3; subst.
      assert (trace_ok p_cons) by (eapply IHr with (tr1 := tr1) (tr2 := tr2); eauto).
      eapply trace_ok_merge_ok with (tr1 := p_merged) (tr2 := p_cons); eauto.
      eapply join_policy_and_trace_ok with (tr1 := tr1) (tr2 := tr2); eauto.
    + apply list_eq_dec. apply Nat.eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
Qed.

Lemma trace_ok_join_ok: ∀ s1 s2 join_by r1 r2 r Γ1 Γ2 Γ β1 β2 β tr1 tr2 tr,
  trace_ok tr1 →
  trace_ok tr2 →
  relation_join_by_prv s1 s2 join_by r1 r2 Γ1 Γ2 β1 β2 tr1 tr2 (Some (r, Γ, β, tr)) →
  trace_ok tr.
Proof.
  induction r1; intros.
  - inversion H1; subst; try constructor.
    apply inj_pair2_eq_dec in H2.
    + discriminate.
    + apply list_eq_dec. apply attribute_eq_dec.
  - inversion H1; subst; try constructor.
    apply inj_pair2_eq_dec in H2, H3, H4, H4, H4; subst.
    + inversion H2; subst.
      assert (trace_ok p_cons) by (eapply IHr1 with (tr1 := tr1) (tr2 := tr2); eauto).
      eapply trace_ok_merge_ok with (tr1 := p_hd) (tr2 := p_cons).
      * apply trace_ok_join_ok_aux in H13; auto.
      * assumption.
    + apply list_eq_dec. apply Nat.eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
    + apply list_eq_dec. apply attribute_eq_dec.
Qed.

Lemma trace_ok_proj_ok: ∀ s s' r r' Γ Γ' β β' t t' pl,
  trace_ok t →
  apply_proj_in_relation s s' r pl Γ β t (Some (r', Γ', β', t')) →
  trace_ok t'.
Proof.
  induction s'; intros; inversion H0; subst; intuition.
  - discriminate.
  - inversion s_case. subst.
    apply eval_expr_in_relation_ok in H9.
    eapply IHs'.
    + eapply H9.
    + eauto.
    + assumption.
Qed.

Lemma eval_predicate_in_relation_ok: ∀ s r Γ β t e r' Γ' β' t',
  trace_ok t →
  eval_predicate_in_relation s r Γ β t e (Some (r', Γ', β', t')) →
  trace_ok t'.
Proof.
Admitted.

Lemma eval_aggregate_ok: ∀ s s' g b a expr r Γ β t r' Γ' β' t',
  trace_ok t →
  eval_aggregate s s' g b a expr Γ β t r (Some (r', Γ', β', t')) →
  trace_ok t'.
Proof.
Admitted.

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
  induction o; intros.
  - right.
    exists nil, (ConfigOut (RelationWrapped nil nil) (nil, 0) nil), nil, (nil, 0), nil.
    split.
    + reflexivity.
    + split; constructor.
      * reflexivity.
      * constructor.
      * constructor.

  - destruct db eqn: Hdb.
    + left. eapply E_GetRelationError; eauto.
    + destruct (database_get_contexts db n) as [ [ [ [ r Γ] ] β ] | ] eqn: Hget.
      * subst. destruct r. right.
        exists s0, (ConfigOut (RelationWrapped s0 r) (Γ, β) t), r, (Γ, β), t.
        intuition.
        -- econstructor; eauto.
        -- eapply database_get_contexts_trace_ok. eapply Hget.
        -- red. auto.
      * left. subst. eapply E_GetRelationError; eauto.
  - specialize (operator_always_terminate db o1).
    specialize (operator_always_terminate db o2).
    (*
      We need to introduce this existential variable *before* each sub-case to avoid
      scoping issues; otherwise, Coq will complain that it cannot find the variable.
    *)
    intros.
    destruct H as [c H]. destruct H0 as [c' H0].
    intuition.
    + left. eapply E_UnionError; eauto.
    + left. eapply E_UnionError.
      -- eapply H1.
      -- eapply H.
      -- left. reflexivity.
    + left. eapply E_UnionError.
      -- eapply H0.
      -- eapply H2.
      -- right. reflexivity.
    + destruct H1 as [ s1 [ c1 [r1 [ σ1 [ tr1 H1 ] ] ] ] ].
      destruct H2 as [ s2 [ c2 [r2 [ σ2 [ tr2 H2 ] ] ] ] ].
      intuition. subst.
      (* Now we need to discuss the equality of two schemas. *)
      destruct (list_eq_dec attribute_eq_dec s1 s2) eqn: Hs.
      * right. subst.
        rename s2 into s.
        destruct σ1 as [Γ1 β1], σ2 as [Γ2 β2].
        pose (merged_Γ := merge_env Γ1 Γ2).
        pose (merged_β := calculate_budget β1 β2).
        pose (merged_tr := merge_env tr1 tr2).
        exists s, (ConfigOut (RelationWrapped s (r1 ++ r2)) (merged_Γ, merged_β) merged_tr),
               (r1 ++ r2), (merged_Γ, merged_β), merged_tr.
        intuition.
        -- eapply E_UnionOk; eauto.
        -- eapply trace_ok_merge_ok; eauto. 
      * left. destruct σ1 as [Γ1 β1], σ2 as [Γ2 β2].
        eapply E_UnionSchemaError; eauto.
  - intuition.
    + left. econstructor; eauto.
    + destruct H0 as [s [c [r [σ [tr [H1 [ H2 H3 ] ] ] ] ] ] ]. 
      left. eapply E_JoinError.
      * eapply H.
      * eapply H2.
      * left. reflexivity.
    + destruct H as [s [c [r [σ [tr [H1 [ H2 H3 ] ] ] ] ] ] ].
      left. eapply E_JoinError.
      * eapply H2.
      * eapply H0.
      * right. reflexivity.
    + destruct H0 as [s1 [c1 [r1 [σ1 [tr1 [H1 [ H2 H3 ] ] ] ] ] ] ].
      destruct H  as [s2 [c2 [r2 [σ2 [tr2 [H4 [ H5 H6 ] ] ] ] ] ] ].
      intuition. destruct σ1 as [Γ1 β1], σ2 as [Γ2 β2]. simpl in *.

      (* Now we are going to discuss over `relation_join_by_prv`. *)
      destruct s1; destruct s2.
      * right.
        exists nil, (ConfigOut (RelationWrapped nil nil) (nil, 0) nil), nil, (nil, 0), nil.
        split.
        -- reflexivity.
        -- split.
          ++ econstructor; eauto. subst.
             constructor. intuition.
          ++ split; constructor.
      * right.
        pose (s := (output_schema_join_by (a :: s2) nil (natural_join_list (a :: s2) nil))).
        exists s,
          (ConfigOut
            (RelationWrapped s nil) (nil, 0) nil), nil, (nil, 0), nil.
        intuition.
        -- econstructor; eauto.
           econstructor. right. reflexivity.
        -- constructor.
      * right.
        pose (s := (output_schema_join_by nil (a :: s1) (natural_join_list (a :: s1) nil))).
        exists s,
          (ConfigOut
            (RelationWrapped s nil) (nil, 0) nil), nil, (nil, 0), nil.
        intuition.
        -- econstructor; eauto.
           econstructor. left. reflexivity.
        -- constructor.
      * pose (s := (output_schema_join_by (a0 :: s2) (a :: s1) (natural_join_list (a0 :: s2) (a :: s1)))).
        specialize
          (relation_join_by_prv_terminate
            (a0 :: s2) (a :: s1)
            (natural_join_list (a0 :: s2) (a :: s1) )
            r2 r1 Γ2 Γ1 β2 β1 tr2 tr1
          ).
        intros.
        destruct H3 as [res H3].
        destruct res as [ [ [ [ r Γ ] β ] tr ] |].
        -- (* Some *)
           right.
           exists s, (ConfigOut (RelationWrapped s r) (Γ, β) tr), r, (Γ, β), tr.
           intuition.
           ++ econstructor.
              ** eapply H5.
              ** eapply H4.
              ** eapply H2.
              ** eapply H1.
              ** eapply H3.
              ** reflexivity.
           ++ eapply trace_ok_join_ok.
              ** eapply H.
              ** eapply H6.
              ** eapply H3.
        -- left. eapply E_JoinError2.
           ++ eapply H5.
           ++ eapply H4.
           ++ eapply H2.
           ++ eapply H1.
           ++ eapply H3.

  - intuition.
    destruct H as [s [ c [r [σ [tr H] ] ] ] ].
    intuition. subst. destruct σ as [Γ β]. simpl in *.

    (* Now we discuss the projection semantics case by case. *)
    destruct s; destruct r.
    + right. exists nil, (ConfigOut (RelationWrapped nil nil) (Γ, β) tr), nil, (Γ, β), tr.
      split.
      * reflexivity.
      * split.
        -- econstructor; eauto.
        -- split; intuition.
    + right. exists nil, (ConfigOut (RelationWrapped nil (t :: r)) (Γ, β) tr), (t :: r), (Γ, β), tr.
      split.
      * reflexivity.
      * split.
        -- econstructor; eauto. 
        -- split; intuition.
    + right. exists (a :: s), (ConfigOut (RelationWrapped (a :: s) nil) (Γ, β) tr), nil, (Γ, β), tr.
      split.
      * reflexivity.
      * split.
        -- econstructor; eauto. 
        -- split; intuition.
    + destruct (project_list_preprocess_neq_star (a :: s) p) as [pl' Hpl]. subst.
      destruct (determine_schema (a :: s) pl') as [s'|] eqn: Hdet.
      * (* Some *)
        specialize apply_proj_in_relation_terminate with
          (s := (a :: s)) (s' := s') (r := (t :: r)) (pl := pl') (Γ := Γ) (β := β) (p := tr) as Hterm.
        intros. destruct Hterm as [res Hterm].
        destruct res as  [ [ [ [ r' Γ' ] β' ] tr' ] |].
        -- (* Some *)
           right. exists s', (ConfigOut (RelationWrapped s' r') (Γ', β') tr'), r', (Γ', β'), tr'.
           intuition.
           ++ eapply E_ProjOk.
              ** eapply H.
              ** reflexivity.
              ** intuition; discriminate.
              ** eauto.
              ** eauto.
              ** eapply Hterm.
              ** reflexivity.
           ++ eapply trace_ok_proj_ok; eauto.
        -- left. eapply E_ProjError; eauto. intuition; discriminate.
      * left. eapply E_ProjError3; eauto. intuition; discriminate.
  - intuition.
    destruct H as [s [ c [r [σ [tr H] ] ] ] ]. intuition. subst.
    destruct σ as [Γ β]. simpl in *.
    destruct (eval_predicate_in_relation_terminate s r Γ β tr e) as [res Hterm].
    destruct res as [ [ [ [r' Γ' ] β' ] tr' ] |].
    + (* Some *)
      right.
      exists s, (ConfigOut (RelationWrapped s r') (Γ', β') tr'), r', (Γ', β'), tr'.
      intuition.
      * econstructor; eauto.
      * eapply eval_predicate_in_relation_ok; eauto.
    + left. eapply E_SelectError; eauto.
  - intuition.
    destruct H as [s [ c [r [σ [tr H] ] ] ] ]. intuition. subst.
    destruct σ as [Γ β]. simpl in *.
    + destruct s; destruct r.
      * right. exists nil, (ConfigOut (RelationWrapped nil nil) (Γ, β) tr), nil, (Γ, β), tr.
        split.
        -- reflexivity.
        -- split.
          ++ econstructor; eauto.
          ++ split; intuition.
      * right. exists nil, (ConfigOut (RelationWrapped nil (t :: r)) (Γ, β) tr), (t :: r), (Γ, β), tr.
        split.
        -- reflexivity.
        -- split.
          ++ econstructor; eauto.
          ++ split; intuition.
      * right. exists (a0 :: s), (ConfigOut (RelationWrapped (a0 :: s) nil) (Γ, β) tr), nil, (Γ, β), tr.
        split.
        -- reflexivity.
        -- split.
          ++ econstructor; eauto.
          ++ split; intuition.
      * destruct (bounded_list_dec _ (a0 :: s) g).
        -- destruct (determine_schema_agg (a0 :: s) a g b) as [s_agg|] eqn: Hdet.
           ++ destruct (eval_aggregate_terminate (a0 :: s) s_agg g b a e Γ β tr (t :: r)) as [res Hterm].
              destruct res as [ [ [ [ r' Γ' ] β' ] tr' ] |].
              ** right.
                 exists s_agg, (ConfigOut (RelationWrapped s_agg r') (Γ', β') tr'), r', (Γ', β'), tr'.
                 intuition. eapply E_AggOk; eauto.
                 --- intuition; discriminate.
                 --- eapply eval_aggregate_ok; eauto.
              ** left. eapply E_AggFail; eauto. intuition; discriminate.
            ++ left. eapply E_AggSchemaError; eauto. intuition; discriminate.
        -- left. eapply E_AggNotBounded; eauto. intuition; discriminate.
Qed.
