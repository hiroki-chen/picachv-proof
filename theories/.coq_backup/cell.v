Require Import Unicode.Utf8.

(*
  `step_cell` is an inductive type that defines a Relation between two configurations except that
  it works on the level of cells. This transition is defined by a notation `c1 >[ f ]> c2` where `f`
  is a function that transforms cell(s).
*)
Reserved Notation "c1 '>[' f ':' arg ']>' c2" (
  at level 50, no associativity, f at next level, arg at next level, c2 at next level
).
Inductive step_cell_single: unary_func → (Cell.cell * nat) → config → config → Prop :=
  | E_CTerminal:
      ∀ c f arg, config_terminal c >[ f : arg ]> config_terminal c
  (* If the environment is empty, then we cannot do anything.  *)
  | E_CTransErrorEmptyEnv:
      ∀ s Γ β e p f arg,
          List.length s = 0 →
          ⟨ s Γ β e p ⟩ >[ f : arg ]> config_error
  (* If the function works on a different type, we simply throw an error. *)
  | E_CTransErrorType:
      ∀ c f arg ty, ty = get_unary_type f →
      type_matches (fst arg) ty = false →
      c >[ f : arg ]> config_error
  (* If the environment is not empty but there is no active tuples, we cannot do anything. *)
  | E_CTransErrorNoTuple:
      ∀ s Γ β e p f arg (non_empty: List.length s > 0) tl,
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          List.length tl = 0 → 
          ⟨ s Γ β e p ⟩ >[ f : arg ]> config_error
  (* The label does not flow to the current one. *)
  | E_CTransErrorLabel:
      ∀ (ℓ1 ℓ2: Policy.policy) ℓcur ℓdisc s Γ β e p f arg (non_empty: List.length s > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (true, (ℓcur, Some ℓdisc)) = label_lookup c_idx Γ →
          ~ (ℓcur ⊑ ℓ1) →
          ⟨ s Γ β e p ⟩ >[ f : arg ]> config_error
  (* No active labels are found; this should be an error. *)
   | E_CTransError4:
      ∀ s Γ β e p f arg (non_empty: List.length s > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          None = label_lookup c_idx Γ →
          ⟨ s Γ β e p ⟩ >[ f : arg ]> config_error *)

  (* Type error: we do not support casting for the time being. *)
  | E_CTransError2:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e p f (non_empty: List.length s > 0)
        tl (tl_non_empty: List.length tl > 0) t c c' c_idx
        (idx_bound: c_idx < List.length (♭ (hd_ok s non_empty))),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (true, (ℓcur, Some ℓdisc)) = label_lookup c_idx Γ →
          (ℓ1, ℓ2) = get_policy_label f →
          (* udpate the policy environment. *)
          ℓcur ⊑ ℓ1 → Γ' = Policy.update_label c_idx Γ (true, (ℓ2, Some ℓdisc)) →
          (* update the cell *)
          c = Tuple.nth _ c_idx idx_bound → c' = (interp_transformation f) c →
          (* update the tuple by updating this cell. *)
          None = Tuple.set_nth_type_match _ c_idx c' idx_bound t →
          ⟨ s Γ β e p ⟩ >[ f ]> config_error
  (* This transition is ok. *)
  (* TODO: Perhaps we need to add some sort of provenance update? *)
  | E_CTransOk1:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e e' p p' f (non_empty: List.length s > 0)
        tl tl' (tl_non_empty: List.length tl > 0) t t' c c' c_idx
        (idx_bound: c_idx < List.length (♭ (hd_ok s non_empty))),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (true, (ℓcur, Some ℓdisc)) = label_lookup c_idx Γ →
          (ℓ1, ℓ2) = get_policy_label f →
          (* udpate the policy environment. *)
          ℓcur ⊑ ℓ1 → Γ' = Policy.update_label c_idx Γ (true, (ℓ2, Some ℓdisc)) →
          (* update the cell. *)
          c = Tuple.nth _ c_idx idx_bound → c' = (interp_transformation f) c →
          (* update the tuple by updating this cell. *)
          Some t' = Tuple.set_nth_type_match _ c_idx c' idx_bound t →
          (* update the tuple environment. *)
          tl' = set_nth tl 0 t' →
          (* update the environment. *)
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ' β e' p' ⟩
  | E_CTransOk2:
    ∀ ℓ1 ℓ2 s Γ β e e' p f (non_empty: List.length s > 0)
        tl tl' (tl_non_empty: List.length tl > 0) t t' c c' c_idx
        (idx_bound: c_idx < List.length (♭ (hd_ok s non_empty))),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (false, (ℓ1, ℓ2)) = label_lookup c_idx Γ →
          (* update the cell. *)
          c = Tuple.nth _ c_idx idx_bound → c' = (interp_transformation f) c →
          (* update the tuple by updating this cell. *)
          Some t' = Tuple.set_nth_type_match _ c_idx c' idx_bound t →
          (* update the tuple environment. *)
          tl' = set_nth tl 0 t' →
          (* update the environment. *)
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e' p ⟩
where "c1 '>[' f : arg ']>' c2" := (step_cell_single f arg c1 c2).
Hint Constructors step_cell_single: core.
