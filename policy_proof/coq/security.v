Require Import List.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import lattice.
Require Import prov.
Require Import relation.
Require Import semantics.
Require Import types.
Require Import util.

(*
  For a cell to be released (i.e., it can be shared freely), it must be the case that all policies are satisfied.
  Fortunately, we have `policy_clean`. This means that we can just check whether the policy is clean.
*)
Definition can_release p: Prop := p = ∎.

(* TODO: Define this. *)
Definition budget_bounded (β: budget): Prop := True.

Definition valid_transition (τ: prov_type) (p1 p2: Policy.policy): Prop :=
  p1 ⪯ p2 ∧
  match τ with
    | prov_trans_unary op => (∘ (Policy.policy_transform ((unary_trans_op op) :: nil))) ⪯ p1
    | prov_trans_binary op => (∘ (Policy.policy_transform ((binary_trans_op op) :: nil))) ⪯ p1
    | prov_agg op => (∘ (Policy.policy_agg (op :: nil))) ⪯ p1
    | prov_noise op => (∘ (Policy.policy_noise op)) ⪯ p1
    | prov_join => True
  end.

(*
  @param c1 The initial policy context.
  @param c2 The final policy context.
  @param p The policy that is being checked.
  @param prov_ctx The provenance context.
  @param prov The provenance tree that is being checked.
  @return A proposition that is true if the provenance tree is valid and false otherwise.

  Checks whether a given provenance tree (consisting of cells) is valid in the course of a query execution.
  It checks if policies are correctly enforced and if all transitions are permitted.
*)
Inductive prov_ok: Policy.context → Policy.context → Policy.policy → prov_ctx → prov → Prop :=
  | prov_ok_none: ∀ Γ Γ' ε' p, prov_ok Γ Γ' ε' p prov_none
  | prov_ok_list: ∀ Γ Γ' ε' p prv τ l,
      prv = prov_list τ l →
      prov_list_ok Γ Γ' ε' p τ l →
      prov_ok Γ Γ' ε' p prv
  with
prov_list_ok: Policy.context → Policy.context → Policy.policy → prov_ctx → prov_type → list (nat * prov) → Prop :=
  | prov_list_ok_empty: ∀ Γ Γ' ε' p τ, prov_list_ok Γ Γ' ε' p τ nil
  | prov_list_ok_cons: ∀ Γ Γ' ε ε' p τ c prov l l',
      l = (c, prov) :: l' →
      label_lookup Γ c  = Some ε →
      can_release ε →
      valid_transition τ ε ε' →
      prov_list_ok Γ Γ' ε' p τ l' →
      prov_ok Γ Γ' ε' p prov →
      prov_list_ok Γ Γ' ε' p τ l
.

Inductive label_transition_valid_es: Policy.context → Policy.context → prov_ctx → list nat → Prop :=
  | label_valid_empty_list: ∀ Γ Γ' p, label_transition_valid_es Γ Γ' p nil
  | label_valid_transition: ∀ Γ Γ' p c lc lc' ε ε' prov_term,
      lc = c :: lc' →
      label_lookup Γ c = Some ε →
      label_lookup Γ' c = Some ε' →
      can_release ε →
      label_lookup p c = Some (prov_term) →
      prov_ok Γ Γ' ε' p prov_term →
      label_transition_valid_es Γ Γ' p lc' →
      label_transition_valid_es Γ Γ' p lc
.

Inductive label_transition_valid: ∀ s, relation s → Policy.context → Policy.context → prov_ctx → Prop :=
  | valid_refl: ∀ s r Γ p, label_transition_valid s r Γ Γ p
  | valid_empty_schema: ∀ s r Γ Γ' p, s = nil → label_transition_valid s r Γ Γ' p
  | valid_env: ∀ s r r' Γ Γ' p, s ≠ nil →
      r' = extract_as_cell_list s r →
      label_transition_valid_es Γ Γ' p r' →
      label_transition_valid s r Γ Γ' p
.

(* 
    ∀Γ, Γ′.Γ −→ Γ′ =⇒ ∀c′ ∈ Γ′.ℓ′1 ⊑ ℓ =⇒
      ∃C = {c1, · · · cn} −→ c′ =⇒
        ∀c ∈ C.(ℓ1, ℓ2) = Γ(c) ∧ ℓ1 ⊑ ℓ2 =⇒ Ok(ℓ1 ⇝o ℓ′1)

    Should we start from empty environment? Or this condition is unnecessary?
 *)
Theorem secure_query:
  ∀ c db Γ β p o,
  c = ⟨ db Γ β p ⟩ ∧ config_valid c →
  {{ c o }} ⇓ {{ config_error }} ∨ 
    (∃ s c' db' Γ' β' p' r, 
        c' = config_output (relation_output s r) (⟨ db' Γ' β' p' ⟩) →
      {{ c o }} ⇓ {{ c' }} ∧ label_transition_valid s r Γ Γ' p' ∧ budget_bounded β').
Proof.
  induction o; intros.
  - right. exists nil, (config_output (relation_output nil nil) c), db, Γ, β, p, nil. split.
    + apply E_Empty1 with nil. reflexivity.
    + constructor.
      * constructor.
      * red. trivial.
  - destruct db eqn: Hdb.
    + left. eapply E_GetRelationDbEmpty; eauto.
    + destruct (database_get_contexts db n) as [ [ [ r' Γ' ] p' ] | ] eqn: Hget.
      * destruct r'. right. exists s0, (⟨ db Γ' β p' ⟩), db, Γ', β, p', r. split.
        -- eapply E_GetRelation with (db := db) (o := operator_relation n).
          ++ red. intros. rewrite Hdb in H1. inversion H1.
          ++ reflexivity.
          ++ rewrite <- Hdb in H. destruct H. eapply H.
          ++ eapply Hget.
          ++ eapply H0.
        -- split; simpl.
          ++ destruct s0.
            ** constructor. reflexivity.
            ** inversion H0.
          ++ inversion H0.
      * left. eapply E_GetRelationError with (db := db) (Γ := Γ) (β := β) (p := p); eauto.
        -- red. intros. rewrite Hdb in H0. inversion H0.
        -- intuition. subst. reflexivity.
  - specialize (operator_always_terminate c o2). intros.
        assert (c ≠ config_error). {
          destruct H. subst. red. intros. inversion H.
        }
        apply H0 in H1. clear H0.
      destruct IHo1; destruct IHo2; try assumption.
    + left. eapply E_UnionError with (db := db) (Γ := Γ) (β := β) (p := p).
      * destruct H. assumption.
      * eapply H0.
      * eapply H2.
      * intuition.
    + 
      destruct H2 as [ s [ c' [ db' [ Γ' [ β' [ p' [ r H3 ] ] ] ] ] ] ].
      left. eapply E_UnionError with (db := db) (Γ := Γ) (β := β) (p := p).
      * destruct H. assumption.
      * eapply H0.
      *

Admitted.
