Require Import Arith.
Require Import Arith.Compare.
Require Import Lia.
Require Import List.
Require Import ListSet.
Require Import Logic.Eqdep_dec Logic.EqdepFacts.
Require Import String.
Require Import Unicode.Utf8.

Require Import Base.Config.
Require Import Base.Trace.
Require Import Base.Types.
Require Import Base.Lattice.
Require Import Base.Ordering.
Require Import Base.Util.

Require Import Data.DataModel.
Require Import Data.Relation.

Require Import Operational.Expression.
Require Import Operational.Semantics.

Lemma join_policy_and_trace_terminate: ∀ l1 l2 com tr1 tr2, ∃ res,
  join_policy_and_trace l1 l2 com tr1 tr2 res.
Proof.
  induction l1; destruct l2; destruct com; intros.
  1-7: exists (Some (tr1 ⊍ tr2)); constructor; auto.
  all: remember a as hd1. remember n as hd2.
    destruct (label_lookup tr1 hd1) eqn: Hhd1, (label_lookup tr2 hd2) eqn: Hhd2.
    2-4: exists None; eapply join_policy_and_trace_lookup_err; eauto.
    all: assert (tr1 ≠ nil ∧ tr2 ≠ nil) as Hpreq.
    {
      destruct tr1; destruct tr2; try discriminate.
      split; discriminate. 
    }
    destruct Hpreq.
    destruct tr1; destruct tr2; try discriminate.
    destruct (IHl1 l2 com tr1 tr2).
    destruct x as [tr|].
    - pose (extract_policy t) as p1.
      pose (extract_policy t0) as p2.
      destruct (Policy.policy_join_terminate p1 p2) as [pjoin].
      exists (Some ((n0, (TrBranch prov_join pjoin (t :: t0 :: nil))) :: tr)).
      eapply join_policy_and_trace_cons_ok; eauto.
    - exists None. eapply join_policy_and_trace_cons_err; eauto.
Qed.

Lemma relation_join_by_prv_helper_terminate: ∀ s1 s2 join_by t r ε1 ε2 p1 p2,
  ∃ res, relation_join_by_prv_helper s1 s2 join_by t r ε1 ε2 p1 p2 res.
Proof.
  induction r; intros.
  - subst. exists (Some (nil, calculate_budget ε1 ε2, (p1 ⊍ p2))). constructor; auto.
  - rename t into t1. rename a into t2.
    destruct (tuple_concat_by s1 s2 join_by t1 t2) as [ [t' [ [ index_lhs index_rhs ] comid ] ]|] eqn: H1.
    + destruct (join_policy_and_trace_terminate index_lhs index_rhs comid p1 p2). destruct x as [tr_merged|] eqn: H2.
      * destruct (IHr ε1 ε2 p1 p2). destruct x0 as [ [ [r_cons ε_cons] tr_cons] |].
        -- exists (Some (t' :: r_cons, calculate_budget (calculate_budget ε1 ε2) ε_cons, (tr_merged ⊍ tr_cons))).
           eapply E_JoinConsOk; intuition; try discriminate; eauto.
        -- exists None. eapply E_JoinConsError3; intuition; try discriminate; eauto.
      * exists None. eapply E_JoinConsError2; intuition; try discriminate; eauto.
    + exists None. eapply E_JoinConsError1; intuition; try discriminate; eauto.
Qed.

Lemma relation_join_by_prv_terminate: ∀ s1 s2 join_by r1 r2 ε1 ε2 p1 p2, ∃ res,
  relation_join_by_prv s1 s2 join_by r1 r2 ε1 ε2 p1 p2 res.
Proof.
  intros. destruct s1; destruct s2.
  - exists (Some (nil, O, nil)). constructor; intuition.
  - exists (Some (nil, O, nil)). constructor; intuition.
  - exists (Some (nil, O, nil)). constructor; intuition.
  - induction r1; destruct r2.
    + exists (Some (nil, O, nil)). apply E_RelationJoinNil. intuition.
    + exists (Some (nil, O, nil)). apply E_RelationJoinNil. intuition.
    + exists (Some (nil, O, nil)). apply E_RelationJoinNil. intuition.
    + destruct (relation_join_by_prv_helper_terminate
                  (a :: s1) (a0 :: s2) join_by a1 (t :: r2) ε1 ε2 p1 p2).
      destruct IHr1.
      destruct x; destruct x0.
      * destruct p as[ [ r_hd β_hd ] p_hd ].
        destruct p0 as[ [ r_cons β_cons ] p_cons ].
        pose (merge_env p_hd p_cons) as p_out.
        pose (calculate_budget β_hd β_cons) as β_out.
        exists (Some (r_hd ++ r_cons, β_out, p_out)).
        eapply E_RelationJoinConsOk; intuition; try discriminate; eauto.
      * exists None. destruct p as[ [ r_hd β_hd ] p_hd ].
        eapply E_RelationJoinConsErr; intuition; try discriminate; eauto.
      * exists None. econstructor; intuition; try discriminate; auto.
      * exists None. econstructor; intuition; try discriminate; auto.
Qed.

Lemma relation_join_by_prv_deterministic: ∀ s1 s2 join_by r1 r2 ε1 ε2 p1 p2 res1 res2,
  relation_join_by_prv s1 s2 join_by r1 r2 ε1 ε2 p1 p2 res1 →
  relation_join_by_prv s1 s2 join_by r1 r2 ε1 ε2 p1 p2 res2 →
  res1 = res2.
Proof.
Admitted.

Theorem eval_terminate: ∀ e b β tp proxy, ∃ env, eval 100 e b (β, tp, proxy) env.
Proof.
  induction e; intros.
  - 
Admitted.

Theorem eval_expr_terminate: ∀ b β tr tp proxy e, ∃ res, eval_expr b (β, tr) tp proxy e res.
Proof.
  intros.
  destruct (eval_terminate e b (β, tr) tp proxy) as [env].
  exists env.
  constructor. assumption.
Qed.

Theorem eval_predicate_in_relation_terminate:
  ∀ s r β tr e, ∃ res, eval_predicate_in_relation s r β tr e res.
Proof.
  induction r; intros.
  - exists (Some (nil, β, tr)). constructor. reflexivity.
  - 
Admitted.

Theorem eval_aggregate_terminate:
  ∀ s s_agg gb b agg expr β tr r, ∃ res, eval_aggregate s s_agg gb b agg expr β tr r res.
Proof.
Admitted.


Theorem apply_proj_in_relation_deterministic: ∀ s s' r pl β tr res1 res2,
  apply_proj_in_relation s s' r pl β tr res1 →
  apply_proj_in_relation s s' r pl β tr res2 →
  res1 = res2.
Proof. Admitted.

Theorem apply_proj_in_relation_terminate: ∀ s s' r pl β tr,
  ∃ res, apply_proj_in_relation s s' r pl β tr res.
Proof. Admitted.

Theorem operator_deterministic: ∀ db o c1 c2, 
  ⟦ db o ⟧ ⇓ ⟦ c1 ⟧ →
  ⟦ db o ⟧ ⇓ ⟦ c2 ⟧ →
  c1 = c2.
Proof.
  induction o; intros.
  - inversion H0; inversion H; subst; auto; try discriminate.
  - inversion H0; inversion H; subst; auto; try discriminate;
    try (rewrite H5 in H12; inversion H12); auto; 
    try (rewrite H4 in H11; inversion H11; subst); auto.
    try (rewrite H4 in H10; inversion H10; subst); auto.
    + contradiction.
    + contradiction.
    + rewrite H4 in H10. discriminate.
  - destruct c1; destruct c2.
    + reflexivity.
    (* + inversion H0; subst; try discriminate.
    + inversion H; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * destruct H7; subst.
        -- inversion H0; subst.
           specialize IHo1 with (c1 := (ConfigOut (RelationWrapped s r') (⟨ db' β' tr' ⟩))) (c2 := ConfigError).
           apply IHo1 in H9.
           ++ discriminate.
           ++ assumption.
        -- inversion H0; subst.
           specialize IHo2 with (c1 := ConfigError) (c2 := (ConfigOut (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
           apply IHo2 in H11.
           ++ discriminate.
           ++ assumption.
      * inversion H0; subst; try discriminate.
        inversion H8. subst.
        (* The contradiction occurs when s1 ≠ s2 where s = s1 ∧ s = s2. *)
        specialize IHo1 with (c1 := (ConfigOut (RelationWrapped s1 r') (⟨ db' β' tr' ⟩)))
                             (c2 := (ConfigOut (RelationWrapped s r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩))).
        specialize IHo2 with (c1 := (ConfigOut (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩)))
                             (c2 := (ConfigOut (RelationWrapped s r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩))).
        apply IHo2 in H7. inversion H7. subst.
        apply IHo1 in H5. inversion H5. subst.
        -- exfalso. apply H9. reflexivity.
        -- assumption.
        -- assumption.
    + inversion H; subst; try discriminate.
    + inversion H0; subst; try discriminate.
    + inversion H; subst; try discriminate.
    + inversion H0; subst; try discriminate.
      * inversion H; subst; try discriminate.
      * destruct H7; subst.
        -- inversion H; subst; try discriminate.
           specialize IHo1 with (c1 := (ConfigOut (RelationWrapped s r') (⟨ db' β' tr' ⟩))) (c2 := ConfigError).
           apply IHo1 in H9.
           ++ discriminate.
           ++ assumption.
        -- inversion H; subst.
           specialize IHo2 with (c1 := ConfigError) (c2 := (ConfigOut (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
           apply IHo2 in H11.
           ++ discriminate.
           ++ assumption.
      * inversion H; subst; try discriminate.
        inversion H8. subst.
        (* The contradiction occurs when s1 ≠ s2 where s = s1 ∧ s = s2. *)
        specialize IHo1 with (c1 := (ConfigOut (RelationWrapped s1 r') (⟨ db' β' tr' ⟩)))
                             (c2 := (ConfigOut (RelationWrapped s r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩))).
        specialize IHo2 with (c1 := (ConfigOut (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩)))
                             (c2 := (ConfigOut (RelationWrapped s r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩))).
        apply IHo2 in H7. inversion H7. subst.
        apply IHo1 in H5. inversion H5. subst.
        -- exfalso. apply H9. reflexivity.
        -- assumption.
        -- assumption.
    + inversion H0; subst; try discriminate.
    + inversion H; inversion H0; subst; try discriminate.
      * inversion H8. subst. inversion H4. subst. assumption.
      * inversion H16. subst.
        specialize IHo2 with (c1 := (ConfigOut (RelationWrapped s0 r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩)))
                             (c2 := (ConfigOut (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
        specialize IHo1 with (c1 := (ConfigOut (RelationWrapped s0 r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩)))
                             (c2 := (ConfigOut (RelationWrapped s r') (⟨ db' β' tr' ⟩))).
        intuition. inversion H3. inversion H1. subst.
        (*
          Now we have some weird equality over dependent types:
                    existT P p a = existT P p b
                    ^^^^^: ∀ [A : Type] (P : A → Type) (x : A), P x → {x : A & P x}
        
           The reason for that is that the index `s` appears on the types of `a`
           and `b` cannot be generalized when typing the equality `a = b` which
           is required for `inversion` tactic.
           
           `existT` is the constructor for the dependent pair type, which "hides"
           the index and allows Coq to avoid this problem in the general case,
           producing a statement which is slightly similar.

           `inj_pair2_eq_dec` is a lemma that allows us to `inversion` equality of
            dependent pairs given that the index is decidable.
         *)

        apply inj_pair2_eq_dec in H5, H13; subst; try reflexivity;
        apply list_eq_dec; apply attribute_eq_dec.
  - inversion H0; inversion H; subst; try discriminate; auto.
    + intuition; subst.
      * apply (IHo1 ConfigError) in H13. discriminate. assumption.
      * apply (IHo2 ConfigError) in H15. discriminate. assumption.
    + inversion H14. subst. clear H14.
      apply (IHo1 (ConfigOut (RelationWrapped s1 r') (⟨ db' β' tr' ⟩))) in H15.
      apply (IHo2 (ConfigOut (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H17.
      inversion H15. inversion H17. subst.
      apply inj_pair2_eq_dec in H3, H12; subst. 
      * eapply relation_join_by_prv_deterministic with (res2 := None) in H20.
        inversion H20. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
    + intuition; inversion H15; subst.
      * apply (IHo1 ConfigError) in H5. discriminate. assumption.
      * apply (IHo2 ConfigError) in H7. discriminate. assumption.
    + inversion H15. subst. clear H15.
      apply (IHo1 (ConfigOut (RelationWrapped s1 r') (⟨ db' β' tr' ⟩))) in H16.
      apply (IHo2 (ConfigOut (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H18.
      inversion H16. inversion H18. subst.
      apply inj_pair2_eq_dec in H3, H12; subst. 
      * eapply relation_join_by_prv_deterministic with (res2 := None) in H10.
        inversion H10. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
    + apply (IHo1 (ConfigOut (RelationWrapped s1 r') (⟨ db' β' tr' ⟩))) in H16.
      apply (IHo2 (ConfigOut (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H18.
      inversion H15. inversion H18. inversion H16. subst.
      apply inj_pair2_eq_dec in H9, H19. subst.
      eapply relation_join_by_prv_deterministic with (res2 := (Some (rout, Γout, βout, pout))) in H21.
      * inversion H21. subst. reflexivity.
      * assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
  - inversion H0; inversion H; subst; intuition; auto; subst; try discriminate.
    + apply IHo with (c1 := ConfigOut (RelationWrapped s nil) (⟨ db' β' tr' ⟩)) in H13.
      inversion H12. subst. inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped nil r) (⟨ db' β' tr' ⟩))) in H13.
      inversion H12. subst. inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H1. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s nil) (⟨ db' β' tr' ⟩))) in H13.
      inversion H12. subst. inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 :=(ConfigOut (RelationWrapped nil r) (⟨ db' β' tr' ⟩))) in H13.
      inversion H12. subst. inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H1. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s nil) (⟨ db' β' tr' ⟩))) in H13.
      inversion H12. subst. inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 :=(ConfigOut (RelationWrapped nil r) (⟨ db' β' tr' ⟩))) in H13.
      inversion H12. subst. inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H1. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H17.
      inversion H16. subst. inversion H17. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 :=(ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H17.
      inversion H16. subst. inversion H17. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H1. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H17.
      inversion H16. subst. inversion H17. subst. apply inj_pair2_eq_dec in H10. subst.
      (* Subsitute pl' and pl'0. *)
      rewrite <- H8 in H20. inversion H20. subst.
      (* Then we are able to substite schemas. *)
      rewrite <- H9 in H21. inversion H21. subst.
      * specialize apply_proj_in_relation_deterministic
          with
          (s := s'0) (s' := s'')
          (r := r'0) (pl := pl')
          (Γ := Γ'0) (β := β'0) (p := p'0)
          (res1 := Some (r'', β'', tr'')) (res2 := Some (r''0, Γ''0, β''0, p''0)).
          intros.
        apply H6 in H11. inversion H11. subst.
        reflexivity. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H17.
      inversion H16. subst. inversion H17. subst. apply inj_pair2_eq_dec in H10. subst.
      rewrite <- H8 in H20. inversion H20. subst.
      rewrite <- H9 in H22. inversion H22. subst.
      * specialize apply_proj_in_relation_deterministic
          with
          (s := s'0) (s' := s'')
          (r := r'0) (pl := pl')
          (Γ := Γ'0) (β := β'0) (p := p'0)
          (res1 := Some (r'', β'', tr'')) (res2 := None).
          intros.
        apply H6 in H11. discriminate. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H18.
      inversion H18. assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H17.
      inversion H16. subst. inversion H17. subst. apply inj_pair2_eq_dec in H10. subst.
      rewrite <- H8 in H21. inversion H21. subst. rewrite <- H9 in H22.
      * discriminate.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H16.
      inversion H16. subst. inversion H15. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H2. reflexivity.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H16.
      inversion H16. subst. inversion H15. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H1. reflexivity.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H16.
      inversion H16. subst. inversion H15. subst. apply inj_pair2_eq_dec in H9. subst.
      rewrite <- H8 in H19. inversion H19. subst.
      rewrite <- H10 in H20. inversion H20. subst.
      * specialize apply_proj_in_relation_deterministic
          with
          (s := s'0) (s' := s'')
          (r := r'0) (pl := pl')
          (Γ := Γ'0) (β := β'0) (p := p'0)
          (res1 := None) (res2 := (Some (r'', β'', tr''))).
          intros.
        apply H6 in H11. inversion H11. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := ConfigError) in H11. inversion H11. assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H15.
      inversion H15. subst. inversion H14. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H2. reflexivity.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H15.
      inversion H15. subst. inversion H14. subst. apply inj_pair2_eq_dec in H6. subst.
      * exfalso. apply H1. reflexivity.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply IHo with (c1 := (ConfigOut (RelationWrapped s' r') (⟨ db' β' tr' ⟩))) in H15.
      inversion H15. subst. inversion H14. subst. apply inj_pair2_eq_dec in H8. subst.
      rewrite <- H9 in H18. inversion H18. subst.
      rewrite <- H10 in H19. inversion H19.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
  - inversion H0; inversion H; subst; intuition; auto; subst; try discriminate. *)
Admitted.


Theorem operator_always_terminate: ∀ db o, ∃ c, ⟦ db o ⟧ ⇓ ⟦ c ⟧.
Proof.
  (* induction o; unfold not; intros; destruct c.
  - exfalso. auto.
  - (* Although we don't need `s`, we need to introduce this term into the context. *)
    pose (s := @nil attribute).
    exists (ConfigOut (RelationWrapped nil nil) (⟨ d c b p ⟩)).
    econstructor; reflexivity.
  - pose (s := @nil attribute). exists (ConfigOut r c).
    eapply E_Already with (r := r) (c := (ConfigOut r c)) (c' := c). reflexivity.
  - exfalso. auto.
  - destruct d eqn: Hdb.
    + exists ConfigError. eapply E_GetRelationDbEmpty with (o := OperatorRel n); reflexivity.
    + destruct (database_get_contexts d n) as [ [ [ r' Γ' ] p' ] | ] eqn: Hget.
      * exists (ConfigOut r' (⟨ d Γ' b p' ⟩)).
        eapply E_GetRelation with (db := d) (o := OperatorRel n) (Γ := c) (β := b) (p := p).
        -- red. intros. subst. inversion H0.
        -- reflexivity.
        -- subst. reflexivity.
        -- eapply Hget.
        -- reflexivity.
      * exists ConfigError.
        eapply E_GetRelationError with (db := d) (o := OperatorRel n) (Γ := c) (β := b) (p := p).
        -- red. intros. subst. inversion H0.
        -- reflexivity.
        -- subst. reflexivity.
        -- assumption.
        -- reflexivity.
  - pose (s := @nil attribute). exists (ConfigOut r c).
    eapply E_Already with (r := r) (c := (ConfigOut r c)) (c' := c). reflexivity.
  - contradiction.
  - (* We now introduce the existential variables into the context. *)
    intuition. destruct H0. destruct H1.
    destruct x; destruct x0.
    + exists ConfigError. econstructor; try eauto.
    + exists ConfigError. econstructor; try eauto.
    + exists ConfigError. econstructor; try eauto.
    + exists ConfigError. econstructor; try eauto.
    + inversion H0; subst; try discriminate.
    + inversion H0; subst; try discriminate.
    + exists ConfigError. econstructor; try eauto.
    + inversion H1; subst; try discriminate.
    + destruct r, r0, x, x0; subst.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H1; subst; try discriminate.
      * destruct (list_eq_dec (attribute_eq_dec) s0 s).
        -- subst.
          pose (merged_p := merge_env p0 p1).
          pose (merged_Γ := merge_env c0 c1).
          pose (merged_β := calculate_budget b0 b1).
          exists (ConfigOut (RelationWrapped s (r ++ r0)) (⟨ d1 merged_Γ merged_β merged_p ⟩)).
          econstructor; try reflexivity; eauto.
        -- exists ConfigError. eapply E_UnionSchemaError with (s1 := s) (s2 := s0); try eauto.
      * (* There should be no rule for constructing nested output. *)
        inversion H1; subst; try discriminate. *)
Admitted.
