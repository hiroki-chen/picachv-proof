Require Import List.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import lattice.
Require Import prov.
Require Import query.
Require Import relation.
Require Import types.
Require Import util.

(* ====================================== Deprecated =========================================== *)
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

(* Definition policy_ok s (Γ: Policy.context) (e : ℰ s) : Prop :=
  match e with
    | tt => True
    | (r, _, _, _) :: _ => policy_ok_relation _ Γ r
  end. *)
(* =========================================================================================== *)


Definition valid_transition (τ: prov_type) (ℓ1 ℓ2: Policy.policy): Prop :=
  match τ with
    | prov_trans_unary => ℓ1 ⊑ Policy.policy_transform ∧ ℓ2 = Policy.policy_agg
    | prov_trans_binary => ℓ1 ⊑ Policy.policy_transform ∧ ℓ2 = Policy.policy_agg
    | prov_agg _ => ℓ1 ⊑ Policy.policy_agg ∧ ℓ2 = Policy.policy_noise
    | prov_noise => ℓ1 ⊑ Policy.policy_transform ∧ ℓ2 = Policy.policy_bot
    | prov_join => ℓ1 ⊑ ℓ2
  end.

(*
    This fixpoint function checks whether a given provenance tree (consisting of cells) is valid
    in the course of a query execution. It will check if policies are correctly enforced and if
    all transitions are permitted.
*)
Fixpoint prov_ok (Γ Γ': Policy.context) (ε': Policy.policy_encoding)
                      (p: prov_ctx) (prv: prov)
  : Prop :=
  match prv with
    | prov_none => True
    | prov_list τ l =>
      (*
          We use an anonymous recursive function sometimes necessary to use
          them for difficult recursion patterns.
      *)
      (fix prov_list_ok
        (Γ Γ': Policy.context) (ε': Policy.policy_encoding)
        (p: prov_ctx) (τ: prov_type) (l: list (nat * prov)): Prop :=
          match l with
          | nil => True
          | (c, prov) :: l' =>
            match Policy.label_lookup c Γ with
              | Some ε => Policy.can_release ε ∨
                  match (ε, ε') with
                  | ((false, _), _) => True
                  | ((_, (ℓ1, _)), (_, (ℓ1', _))) => valid_transition τ ℓ1 ℓ1' ∧ 
                                           prov_list_ok Γ Γ' ε' p τ l'
                  end 
              | None => False
            end ∧ prov_ok Γ Γ' ε' p prov
          end)
      Γ Γ' ε' p τ l
  end.

Fixpoint label_transition_valid' (Γ Γ': Policy.context) (p: prov_ctx) (lc: list nat): Prop :=
  match lc with
    | nil => True
    | c :: lc' =>
      match (Policy.label_lookup c Γ, Policy.label_lookup c Γ') with
      | (Some ε, Some ε') =>
          Policy.can_release ε →
            match lookup c p with
            | Some prov => prov_ok Γ Γ' ε' p prov
            | _ => True
            end
      (* Really so? *)
      | _ => False
      end ∧ label_transition_valid' Γ Γ' p lc'
  end. 

Definition label_transition_valid s (Γ Γ': Policy.context) (e: ℰ s) (p: prov_ctx) : Prop.
  induction s.
  - exact True.
  - apply fst in e. (* We just throw away its tails because by default
                       we are interested in the first term. *)
    apply env_slice_get_relation in e. rename e into r.
    exact (label_transition_valid' Γ Γ' p (extract_as_cell_list _ r)).
Defined.

(* 
    ∀Γ, Γ′.Γ −→ Γ′ =⇒ ∀c′ ∈ Γ′.ℓ′1 ⊑ ℓ =⇒
      ∃C = {c1, · · · cn} −→ c′ =⇒
        ∀c ∈ C.(ℓ1, ℓ2) = Γ(c) ∧ ℓ1 ⊑ ℓ2 =⇒ Ok(ℓ1 ⇝o ℓ′1)
 *)
Theorem secure_query:
  ∀ s Γ β e p o,
    (∃ s' Γ' β' e' p', ⟨ s Γ β e p ⟩ =[ o ]=> ⟨ s' Γ' β' e' p' ⟩
      → label_transition_valid s' Γ Γ' e' p').
      (* TODO: Add something for privacy parameter. *)
Proof.
  induction o.
  - exists nil, nil, β, tt, nil. intros. clear H.
    simpl. trivial.
  - 
Admitted.
