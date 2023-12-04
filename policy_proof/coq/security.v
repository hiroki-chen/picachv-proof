Require Import List.
Require Import Unicode.Utf8.

Require Import query.
Require Import types.
Require Import relation.
Require Import data_model.

Definition policy_ok_tuple: ∀ s (Γ: Policy.context), Tuple.tuple s -> Prop.
refine (
  fix policy_ok_tuple' s (Γ: Policy.context): Tuple.tuple s -> Prop :=
    match s as s' return s = s' -> Tuple.tuple s' -> Prop with 
    | nil => fun _ _ => True
    | bt :: t' => fun _ _ => _
    end (eq_refl _)
).
  destruct t.
  pose (Policy.label_lookup (snd p) Γ).
  destruct o.
  - exact (Policy.can_release p0 ∧ policy_ok_tuple' _ Γ t).
  - exact False.
Defined.
  
Fixpoint policy_ok_relation s (Γ: Policy.context) (r: relation s) : Prop :=
  match r with
    | nil => True
    | t :: r' => policy_ok_tuple _ Γ t ∧ policy_ok_relation _ Γ r'
  end.

Definition policy_ok s (Γ: Policy.context) (e : ℰ s) : Prop :=
  match e with
    | nil => True
    | es :: _ =>
        match es with (r, _, _, _) => policy_ok_relation _ Γ r end
  end.

(* todo *)
Theorem secure_query:
  ∀ s s' Γ Γ' β β' e e' o c,
    ⟨ s Γ β e ⟩ =[ o ]=> c →
      c = config_error ∨
      c = ⟨ s' Γ' β' e' ⟩ ∧ policy_ok s' Γ' e'.
Proof.
  intros. induction H; simpl in *.
  - right. split.
Admitted.
