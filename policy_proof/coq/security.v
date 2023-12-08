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
        match es with (r, _, _, _) =>
          match r with
          | nil => True
          | t :: _ => policy_ok_relation _ Γ t
          end
    end
  end.

(* todo *)
Theorem secure_query:
  ∀ s Γ β e o,
    ⟨ s Γ β e ⟩ =[ o ]=> config_error \/
    (∃ s' Γ' β' e', ⟨ s Γ β e ⟩ =[ o ]=> ⟨ s' Γ' β' e' ⟩
      ∧ policy_ok s' Γ' e').
Proof.
  induction o.
  + right. exists s, Γ, β, nil. split.
    - apply E_Empty; reflexivity.
    - simpl. trivial.

  + 
Admitted.

