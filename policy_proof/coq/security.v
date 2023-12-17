Require Import List.
Require Import Unicode.Utf8.

Require Import query.
Require Import types.
Require Import relation.
Require Import data_model.
Require Import prov.
Require Import lattice.

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
    | (r, _, _, _) :: _ => policy_ok_relation _ Γ r
  end.

Fixpoint label_transition_valid' (Γ Γ': Policy.context) (lc: list nat): Prop :=
  match lc with
    | nil => True
    | c :: lc' => False
      (* TODO!! *)
      (* match Policy.label_lookup c Γ' with *)
      (* | Some l' => 
        match Policy.label_lookup c Γ with
        | Some l => l' ⊑ l ∧ label_transition_valid' Γ Γ' lc'
        | None => False
        end
      | _ => False *)
      (* end *)
  end.

Definition label_transition_valid s (Γ Γ': Policy.context) (e: ℰ s) (p: prov_ctx) : Prop :=
  match e with
    | nil => True
    | (r, _, _, _) :: _ => label_transition_valid' (extract_as_cell_list _ r)
  end.

(* 
    ∀Γ, Γ′.Γ −→ Γ′ =⇒ ∀c′ ∈ Γ′.ℓ′1 ⊑ ℓ =⇒
      ∃C = {c1, · · · cn} −→ c′ =⇒
        ∀c ∈ C.(ℓ1, ℓ2) = Γ(c) ∧ ℓ1 ⊑ ℓ2 =⇒ Ok(ℓ1 ⇝o ℓ′1)
 *)
Theorem secure_query:
  ∀ s Γ β e p o,
    (∃ s' Γ' β' e' p', ⟨ s Γ β e p ⟩ =[ o ]=> ⟨ s' Γ' β' e' p' ⟩
      → policy_ok s' Γ' e' ∧ label_transition_valid s' Γ Γ' e' p').
Proof.
  induction o.
Admitted.

