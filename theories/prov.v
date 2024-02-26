Require Import List.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import types.
Require Import util.

Inductive prov_type: Set :=
  | prov_trans_unary: un_op → prov_type
  | prov_trans_binary: bin_op → prov_type
  | prov_agg: agg_op → prov_type
  | prov_noise: noise_op → prov_type
  | prov_join: prov_type
.

Definition prov_type_eqb τ1 τ2: bool :=
  match τ1, τ2 with
  | prov_trans_unary op1, prov_trans_unary op2 => un_op_eqb op1 op2
  | prov_trans_binary op1, prov_trans_binary op2 => bin_op_eqb op1 op2
  | prov_agg op1, prov_agg op2 => agg_op_eqb op1 op2
  | prov_noise op1, prov_noise op2 => noise_op_eqb op1 op2
  | prov_join, prov_join => true
  | _, _ => false
  end.

(*
    This is an auxiliary definition to help us define the prov type to help prove the
    main theorem that involve the "flow" of each sensitive data piece at the cell level.
*)
Inductive prov: Set :=
  | prov_list: prov_type → list (nat * prov) → prov
  | prov_none: prov
.

Definition prov_ctx := ctx prov.

Fixpoint empty_prov_from_pctx (Γ: Policy.context): prov_ctx :=
  match Γ with
  | nil => nil
  | (n, _) :: Γ' => (n, prov_none) :: empty_prov_from_pctx Γ'
  end.

Notation "∅" := (prov_none).

Section Facts.

Lemma prov_eqb_eq: ∀ τ1 τ2, prov_type_eqb τ1 τ2 = true → τ1 = τ2.
Proof.
  intros τ1 τ2 H.
  destruct τ1, τ2; simpl in H; try discriminate.
  - apply un_op_eq_eqb in H. subst. reflexivity.
  - apply bin_op_eq_eqb in H. subst. reflexivity.
  - apply agg_op_eq_eqb in H. subst. reflexivity.
  - apply noise_op_eq_eqb in H. subst. reflexivity.
  - reflexivity.
Qed.

End Facts.
