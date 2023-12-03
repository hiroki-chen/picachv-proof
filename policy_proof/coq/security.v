Require Import List.
Require Import Unicode.Utf8.

Require Import query.
Require Import types.

(* todo *)
Fixpoint env_ok s (e : env s) : Prop :=
  match e with
    | nil => True
    | (x, t) :: e' =>  False \/ env_ok _ e'
  end.

(* todo *)
Theorem secure_query:
  ∀ s ctx priv e o c,
    config_ok s ctx priv e =[ o ]=> c →
      c = config_error \/
      ∃ s' ctx' priv' e',
        c = config_ok s' ctx' priv' e' /\ env_ok s' e'.
Proof.
  intros.
Admitted.
