Require Import List.
Require Import Unicode.Utf8.

Require Import query.
Require Import types.

(* todo *)
Fixpoint env_ok s (e : ℰ s) : Prop :=
  match e with
    | nil => True
    | (x, t) :: e' =>  False ∨ env_ok _ e'
  end.

(* todo *)
Theorem secure_query:
  ∀ s s' Γ Γ' β β' e e' o c,
    config_ok s Γ β e =[ o ]=> c →
      c = config_error ∨
      c = config_ok s' Γ' β' e' ∧ env_ok s' e'.
Proof.
  intros.
Admitted.
