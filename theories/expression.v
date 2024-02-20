Require Import Arith.Compare_dec.
Require Import Lia.
Require Import List.
Require Import String.
Require Import Unicode.Utf8.

Require Import config.
Require Import data_model.
Require Import lattice.
Require Import ordering.
Require Import prov.
Require Import relation.
Require Import types.
Require Import util.

Lemma tuple_single_eq: ∀ s ty, s = ty :: nil →
  Tuple.tuple (♭ s) = (prod (prod (type_to_coq_type (fst ty)) nat) unit).
Proof.
  intros. subst. simpl. auto.
  destruct ty.
  simpl.
  reflexivity.
Qed.

Inductive expr_type: Type :=
  | ExprTypeBasic: basic_type → expr_type
  | ExprTypeFunc: expr_type → expr_type → expr_type
.

Fixpoint expr_type_eqb (τ1 τ2: expr_type): bool :=
  match τ1, τ2 with
    | ExprTypeBasic bt1, ExprTypeBasic bt2 => type_matches bt1 bt2
    | ExprTypeFunc τ1a τ1b, ExprTypeFunc τ2a τ2b =>
      andb (expr_type_eqb τ1a τ2a) (expr_type_eqb τ1b τ2b)
    | _, _ => false
  end.

Inductive expression: Type :=
  (* v *)
  | ExprConst: ∀ bt, type_to_coq_type bt → expression
  (* a *)
  | ExprCol: ∀ (n: nat), expression
  (* ∘ e *)
  | ExprUnary: unary_func → expression → expression
  (* e1 ⊗ e2 *)
  | ExprBinary: binary_func → expression → expression → expression
  (* fold *)
  | ExprAgg: agg_func → expression → expression
.


Inductive e_value: Type :=
  (*
    A value can be associated with a unique identifier for looking up in the context;
    if it is not associated with an identifier, the identifier is `None` which means
    that it is just a "safe" value (like the value obtained by projecting a constant).
  *)
  | ValuePrimitive: ∀ bt, (type_to_coq_type bt * option nat) → e_value
  (* This is the argument for the aggregation expression because it operates on list of values. *)
  | ValuePrimitiveList: ∀ bt, list (type_to_coq_type bt * option nat) → e_value
.

(* `groupby` list is just a list of indices of the original data frame that should be chosen as keys. *)
Definition groupby_list := (list nat)%type.
(* simple_agg_expression := (agg_op * agg_func * nat) *)
Definition agg_list := (list (expression * nat))%type.
(* This represents a range of groups within the original data frame. *)
Definition group := (list nat)%type.

(*
  A GroupbyProxy can be visualized as a pair:
  
  +-----------------+-----------------+
  |   groupby keys  |   data          |
  +-----------------+-----------------+
  | Tuple.tuple s   |  data 0         |
  |                 |  data 1         |
  |                 |  data 2         |
  |                 |  data 3         |
  |                 |  ...            |
  +-----------------+-----------------+

  Where:
  - relation s1 is the relation of the original data frame the groupby proxy is referring to.
  - Tuple.tuple s is the tuple of s, which represents the grouped columns.
  - group_range represents the range of each group.

  We define it as an inductive type because we want to be able to "hide" s; making it
  a dependent type would introduce undue complexity.
*)
Inductive groupby :=
  | GroupbyProxy: ∀ s1 s2, relation s1 → Tuple.tuple s2 → group → groupby
.

Inductive tuple_wrapped: Type :=
  | TupleWrapped: ∀ s, Tuple.tuple (♭ s) → tuple_wrapped
.

(*
  The evaluation environment for the lambda calculus is a list of:
  - The current configuration.
  - The current active tuple (for non-aggregate expressions).
  - The current groupby proxy (optional).
*)
Definition eval_env := (config * tuple_wrapped * option groupby)%type.

Fixpoint index (x: string) (env: list string): nat :=
  match env with
    | h :: t => if string_dec h x then 0 else 1 + index x t
    | _ => 0
  end.

(*
  Since this function is called only after we have decided that p_cur ⪯ p_f which means that
  the current policy is less or equal to the operation we are about to apply, we can safely
  assume that the operation is allowed. So, this function's logic is simple as there are
  only two possible cases:
  - The current policy is less stricter, then the new policy is the current policy.
  - The current policy can be declassified, then the new policy is the declassified policy.
    In other words, ℓ ⇝ p ⪯ ∘ (op) ==> p_new = p.
*)
Definition get_new_policy cur op: Policy.policy :=
  match cur with
  | ∎ => cur
  | ℓ ⇝ p =>
    match Policy.can_declassify_dec ℓ op with
    | left _ => p
    | right _ => cur
    end
  end.

(*
  This function merges two provenance information.

  The first argument is the operation and p1 is the new provenance information to be applied 
  to p2. If p2 is empty, then we just return p1. If p2 is a list, then we need to check if
  the operation is the same as the operation of p2. If it is, then we just append p1 to p2.
  Otherwise, we just return p2.
*)
Definition merge_prov op p1 p2 : prov :=
  match p2 with
  | ∅ => prov_list op (p1 :: nil)
  | prov_list op' l =>
    if prov_type_eqb op op'
    then prov_list op (p1 :: l)
    else p2
  end.

Inductive eval_unary_expression_in_cell: ∀ bt,
  unary_func → (type_to_coq_type bt * nat) → eval_env →
    option (eval_env * e_value) → Prop :=
  | E_UnaryLabelNotFound: ∀ bt f (arg: type_to_coq_type bt) id c tr proxy db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      label_lookup Γ id = None ∨
      label_lookup p id = None →
      eval_unary_expression_in_cell bt f (arg, id) (c, tr, proxy) None
  | E_UnaryTypeError: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id c tr proxy,
      f = UnaryFunc op bt' lambda →
      bt ≠ bt' →
      eval_unary_expression_in_cell bt f (arg, id) (c, tr, proxy) None
  | E_UnaryPolicyError: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id db c tr proxy Γ β p p_cur,
      c = ⟨ db Γ β p ⟩ →
      label_lookup Γ id = Some p_cur →
      f = UnaryFunc op bt' lambda →
      bt = bt' → 
      let p_f := ∘ (Policy.policy_transform ((unary_trans_op op) :: nil)) in
        ¬ (p_cur ⪯ p_f) →
        eval_unary_expression_in_cell bt f (arg, id) (c, tr, proxy) None
  | E_UnaryPolicyOk: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id c tr proxy
                       db Γ Γ' β β' p p' p_cur prov_cur,
      c = ⟨ db Γ β p ⟩ →
      label_lookup Γ id = Some p_cur →
      label_lookup p id = Some prov_cur →
      f = UnaryFunc op bt' lambda →
      ∀ (eq: bt = bt'), let p_f := (Policy.policy_transform ((unary_trans_op op) :: nil)) in
        p_cur ⪯ (∘ p_f) →
          let p_new := get_new_policy p_cur p_f in
            let prov_new := prov_list (prov_trans_unary op) ((id, prov_cur) :: nil) in
              Γ' = update_label Γ id p_new →
              p' = update_label p id prov_new →
              eval_unary_expression_in_cell bt f (arg, id) (c, tr, proxy)
                (Some ((⟨ db Γ' β' p' ⟩, tr, proxy), ValuePrimitive bt' (lambda (eq ♯ arg), Some id)))
.

(*
  This function evaluates a unary expression with a given function and returns a value.

  Notice that this works on a single value, not a list of values.
*)
Inductive eval_unary_expression_prim:
  ∀ bt, unary_func → eval_env → (type_to_coq_type bt * option nat) →
    option (eval_env * e_value) → Prop :=
  | EvalUnaryValueTypeMismatch: ∀ f op env bt bt' v v' id lambda,
    v = (v', id) →
    f = UnaryFunc op bt' lambda →
    (* We cannot cast it. *)
    try_cast bt bt' v' = None →
    eval_unary_expression_prim bt f env v None
  (* If a value does not carry any id, then it is just a value without any policy. *)
  | EvalUnaryValue: ∀ f op env bt bt' v v' v'' lambda,
    v = (v', None) →
    f = UnaryFunc op bt' lambda →
    try_cast bt bt' v' = Some v'' →
    eval_unary_expression_prim bt f env v (Some (env, ValuePrimitive bt' (lambda v'', None)))
  | EvalUnaryValueWithId: ∀ f env bt v v' id res,
    v = (v', Some id) →
    eval_unary_expression_in_cell bt f (v', id) env res →
    eval_unary_expression_prim bt f env v res
.

Inductive eval_unary_expression_list:
  ∀ bt, unary_func → eval_env → list (type_to_coq_type bt * option nat) →
    option (eval_env * e_value) → Prop :=
  | EvalUnaryListNil: ∀ bt f env l,
    l = nil →
    eval_unary_expression_list bt f env l (Some (env, ValuePrimitiveList bt nil))
  | EvalUnaryListHeadError: ∀ bt f env l hd tl,
    l = hd :: tl →
    eval_unary_expression_prim bt f env hd None →
    eval_unary_expression_list bt f env l None
  | EvalUnaryListTailError: ∀ bt f env l hd tl,
    l = hd :: tl →
    eval_unary_expression_list bt f env tl None →
    eval_unary_expression_list bt f env l None
  | EvalUnaryListOk: ∀ bt f env env' env'' l hd tl hd' tl',
    l = hd :: tl →
    eval_unary_expression_prim bt f env hd (Some (env', ValuePrimitive bt hd')) →
    eval_unary_expression_list bt f env' tl (Some (env'', ValuePrimitiveList bt tl')) →
    eval_unary_expression_list bt f env l (Some (env'', ValuePrimitiveList bt (hd' :: tl')))
.

(* TODO *)
Inductive eval_binary_expression_prim:
  ∀ bt1 bt2, binary_func → eval_env → (type_to_coq_type bt1 * option nat) → (type_to_coq_type bt2 * option nat) →
  option (eval_env * e_value) → Prop :=
.

(* TODO *)
Inductive eval_binary_expression_list:
  ∀ bt1 bt2, binary_func → eval_env → list (type_to_coq_type bt1 * option nat) → list (type_to_coq_type bt2 * option nat)
    → option (eval_env * e_value) → Prop :=
.

(* bt1: the input type; bt2: the output type; this evaluates the aggregation expression within a group. *)
Inductive do_eval_agg:
  ∀ bt1 bt2, agg_func → Policy.context → prov_ctx → list (type_to_coq_type bt1 * option nat) →
    option (Policy.policy * prov * (type_to_coq_type bt2)) → Prop :=
  (* When the list being folded is empty, we shall return the initial value. *)
  | EvalDoAggNil: ∀ f op bt1 bt2 f' init_val noise Γ p l,
      l = nil →
      f = AggFunc op bt1 bt2 f' init_val noise →
      do_eval_agg bt1 bt2 f Γ p l (Some (∎, ∅, init_val))
  | EvalDoAggLabelNotFound: ∀ f op bt1 bt2 f' init_val noise Γ p l hd hd_v id tl,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup Γ id = None ∨
      label_lookup p id = None →
      do_eval_agg bt1 bt2 f Γ p l None
  | EvalDoAggPolicyError: ∀ f op bt1 bt2 f' init_val noise Γ p l hd hd_v id tl p_cur p_f,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup Γ id = Some p_cur →
      p_f = ∘ (Policy.policy_agg (op :: nil)) →
      ¬ (p_cur ⪯ p_f) →
      do_eval_agg bt1 bt2 f Γ p l None
  | EvalDoAggPolicyConsError: ∀ bt1 bt2 f Γ p l hd tl,
      l = hd :: tl →
      do_eval_agg bt1 bt2 f Γ p tl None →
      do_eval_agg bt1 bt2 f Γ p l None
  | EvalDoAggOk: ∀ f op bt1 bt2 f' init_val noise Γ p l hd hd_v id tl tl_v p_cur p_f prov_cur p_tl p_final prov_tl,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup Γ id = Some p_cur →
      label_lookup p id = Some prov_cur →
      p_f = ∘ (Policy.policy_agg (op :: nil)) →
      p_cur ⪯ p_f →
      do_eval_agg bt1 bt2 f Γ p tl (Some (p_tl, prov_tl, tl_v)) →
      let p_new := get_new_policy p_cur (Policy.policy_agg (op :: nil)) in
      let prov_new := merge_prov (prov_agg op) (id, prov_cur) prov_tl in
      let res := f' tl_v hd_v in
      p_new ∪ p_tl = p_final →
      do_eval_agg bt1 bt2 f Γ p l (Some (p_final, prov_new, res))
.

Inductive apply_noise:
  ∀ bt, type_to_coq_type bt → budget → noise_gen → nat → Policy.policy →
        prov → Policy.context → prov_ctx →
    option (type_to_coq_type bt * Policy.context * budget * prov_ctx) → Prop :=
  | ApplyNoiseTooWeak: ∀ bt v β ε δ 𝒩 oracle new_id policy provenance Γ p,
      𝒩 = NoiseGen (ε, δ) oracle →
      let p_f := (Policy.policy_noise (differential_privacy (ε, δ))) in
      ¬ (policy ⪯ (∘ p_f)) →
      apply_noise bt v β 𝒩 new_id policy provenance Γ p None
  | ApplyNoiseNoBudget: ∀ bt v β ε δ 𝒩 oracle new_id policy provenance Γ p,
      𝒩 = NoiseGen (ε, δ) oracle →
      let p_f := (Policy.policy_noise (differential_privacy (ε, δ))) in
      policy ⪯ (∘ p_f) →
      β < ε →
      apply_noise bt v β 𝒩 new_id policy provenance Γ p None
  | ApplyNoiseOk: ∀ bt v β ε δ 𝒩 oracle new_id policy provenance Γ p,
      𝒩 = NoiseGen (ε, δ) oracle →
      let p_f := (Policy.policy_noise (differential_privacy (ε, δ))) in
      (* The privacy requirement is satisfied. *)
      policy ⪯ (∘ p_f) →
      β ≥ ε →
      let policy' := get_new_policy policy p_f in
      let provenance' := prov_list (prov_noise (differential_privacy (ε, δ))) ((new_id, provenance) :: nil) in
      let Γ' := (new_id, policy') :: Γ in
      let β' := β - ε in
      let p' := (new_id, provenance') :: p in
      apply_noise bt v β 𝒩 new_id policy provenance Γ p (Some (oracle _ v, Γ', β', p'))
.

(*
  This is just a simple wrapper around `do_eval_agg` that does the policy job.
*)
Inductive eval_agg: ∀ bt, agg_func → eval_env → list (type_to_coq_type bt * option nat) →
  option (eval_env * e_value) → Prop :=
  | EvalAggErr: ∀ bt f env db Γ β p l res,
      fst (fst env) = ⟨ db Γ β p ⟩ →
      do_eval_agg bt bt f Γ p l None →
      eval_agg bt f env l res
  | EvalAggOkNoNoise: ∀ bt bt' f op f' init_val env c tr proxy db Γ β p l v policy provenance,
      env = (c, tr, proxy) →
      c = ⟨ db Γ β p ⟩ →
      f = AggFunc op bt bt' f' init_val None →
      do_eval_agg bt bt' f Γ p l (Some (policy, provenance, v)) →
      let new_id := next_available_id Γ 0 in
      let Γ' := (new_id, policy) :: Γ in
      let p' := (new_id, provenance) :: p in
      let v' := (ValuePrimitive bt' (v, Some new_id)) in
        eval_agg bt f env l (Some ((⟨ db Γ' β p' ⟩, tr, proxy), v'))
  | EvalAggOkNoBudget: ∀ bt bt'  f op f' init_val noise env c tr proxy db Γ β p l v policy provenance,
      env = (c, tr, proxy) →
      c = ⟨ db Γ β p ⟩ →
      f = AggFunc op bt bt' f' init_val (Some noise) →
      do_eval_agg bt bt' f Γ p l (Some (policy, provenance, v)) →
      let new_id := next_available_id Γ 0 in
      apply_noise bt' v β noise new_id policy provenance Γ p None →
      eval_agg bt f env l None
  | EvalAggOkNoise: ∀ bt bt' f op f' init_val noise env c tr proxy db Γ Γ' β β' p p' l v v' policy provenance res,
      env = (c, tr, proxy) →
      c = ⟨ db Γ β p ⟩ →
      f = AggFunc op bt bt' f' init_val (Some noise) →
      do_eval_agg bt bt' f Γ p l (Some (policy, provenance, v)) →
      let new_id := next_available_id Γ 0 in
      apply_noise bt' v β noise new_id policy provenance Γ p res →
      res = Some (v', Γ', β', p') →
      eval_agg bt f env l (Some ((⟨ db Γ' β' p' ⟩, tr, proxy), ValuePrimitive _ (v', Some new_id)))
.

(*
  Eval : (ℕ × Expr × 𝔹 × Γ) × Maybe (Γ' × Val) 
    where 
  - ℕ is the number of steps to evaluate the expression.
  - Expr is the expression to evaluate.
  - 𝔹 is a boolean flag indicating whether the evaluation is performed within an aggregation context.
    - If it is `true`, we need to evaluate the expression on groupby proxy rather than the current tuple.
  - Γ is the current environment.
  - Maybe (Γ' × Val) is the result of the evaluation:
    - If it is `None`, the evaluation results in an error.
    - If it is `Some (Γ', Val)`, the evaluation is finished with an updated environment Γ',
      and the result is `Val`.
*)
Inductive eval: nat → expression → bool → eval_env → option (eval_env * e_value) → Prop :=
  (* The evaluation hangs and we have to force termination. *)
  | EvalNoStep: ∀ e b env step, step = O → eval step e b env None
  (* Evaluating a constant value is simple: we just return it. *)
  | EvalConst: ∀ step step' b bt v e c tr db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = ExprConst bt v →
      eval step e b (c, tr, proxy) (Some ((c, tr, proxy), ValuePrimitive bt (v, None)))
  (* Extracts the value from the tuple if we are not inside an aggregation context. *)
  | EvalColumnNotAgg: ∀ step step' b id n e c s tr t db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = ExprCol id →
      tr = TupleWrapped s t →
      b = false →
      (* We locate this column by its identifier `id` using the comparison function. *)
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s id 0 = Some n),
        let col := 
          (Tuple.nth_col_tuple (♭ s) n
            (eq_sym (schema_to_no_name_length s) ♯
              (elem_find_index_bounded_zero _ _ _ _ find)) t) in
        eval step e b (c, tr, proxy)
          (Some (((c, tr, proxy), ValuePrimitive _ (fst (fst col), Some (snd (fst col))))))
  | EvalColumnNotAggFail: ∀ step step' b id e c s tr t proxy,
      step = S step' →
      e = ExprCol id →
      b = false →
      tr = TupleWrapped s t →
      (* The requested column identifier is not found. *)
      find_index (λ x y, Nat.eqb (snd x) y) s id 0 = None →
      eval step e b (c, tr, proxy) None
  (* Extracts the value from the groupby proxy if we are inside an aggregation context. *)
  | EvalColumnInAggProxyMissing: ∀ step step' b id e c tr proxy,
      step = S step' →
      e = ExprCol id →
      b = true →
      proxy = None →
      eval step e b (c, tr, proxy) None
  | EvalColumnInAgg: ∀ step step' b id n e c s1 s2 tr proxy r gb_keys gb_indices,
      step = S step' →
      e = ExprCol id →
      b = true →
      proxy = Some (GroupbyProxy s1 s2 r gb_keys gb_indices) →
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s1 id 0 = Some n),
        let col' := extract_column_as_list s1 r n (elem_find_index_bounded_zero _ _ _ _ find) in
          let col := map (fun elem => (fst elem, Some (snd elem))) col' in
            eval step e b (c, tr, proxy) (Some ((c, tr, proxy), ValuePrimitiveList _ col))
  | EvalColumnInAggFail: ∀ step step' b id e c s1 s2 tr proxy r gb_keys gb_indices,
      step = S step' →
      e = ExprCol id →
      b = true →
      proxy = Some (GroupbyProxy s1 s2 r gb_keys gb_indices) →
      find_index (λ x y, Nat.eqb (snd x) y) s1 id 0 = None →
      eval step e b (c, tr, proxy) None
  | EvalUnary: ∀ step step' bt b e f e' env v v' res c tr db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = ExprUnary f e' →
      b = false →
      eval step' e' b (c, tr, proxy) (Some (env, v)) →
      v = ValuePrimitive bt v' →
      eval_unary_expression_prim bt f env v' res →
      eval step e b (c, tr, proxy) res
  | EvalUnaryInAgg: ∀ step step' bt b e f e' env v v' res c tr db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = ExprUnary f e' →
      b = true →
      eval step' e' b (c, tr, proxy) (Some (env, v)) →
      v = ValuePrimitiveList bt v' →
      eval_unary_expression_list bt f env v' res →
      eval step e b (c, tr, proxy) res
  (*
    There are still many other cases for us to deal with:

    - Type coercion.
    - Scalar value + vector value -> This means we need to propagate to lists.
   *)
  | EvalBinary: ∀ step step' bt1 bt2 b e f e1 e2 env v1 v1' v2 v2' res c tr db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = ExprBinary f e1 e2 →
      b = false →
      eval step' e1 b (c, tr, proxy) (Some (env, v1)) →
      eval step' e2 b (c, tr, proxy) (Some (env, v2)) →
      v1 = ValuePrimitive bt1 v1' →
      v2 = ValuePrimitive bt2 v2' →
      eval_binary_expression_prim bt1 bt2 f env v1' v2' res →
      eval step e b (c, tr, proxy) res
  | EvalBinaryInAgg: ∀ step step' bt1 bt2 b e f e1 e2 env v1 v1' v2 v2' res c tr db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = ExprBinary f e1 e2 →
      b = true →
      eval step' e1 b (c, tr, proxy) (Some (env, v1)) →
      eval step' e2 b (c, tr, proxy) (Some (env, v2)) →
      v1 = ValuePrimitiveList bt1 v1' →
      v2 = ValuePrimitiveList bt2 v2' →
      eval_binary_expression_list bt1 bt2 f env v1' v2' res →
      eval step e b (c, tr, proxy) res
  (* Nested aggregation makes no sense. *)
  | EvalNestedAgg: ∀ step step' b e agg body c tr db Γ β p proxy s r s_key gb_keys gb_indices,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = true →
      eval step e b (c, tr, proxy) None
  | EvalAggProxyMissing: ∀ step step' b e agg body c tr db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = None →
      b = false →
      e = ExprAgg agg body →
      eval step e b (c, tr, proxy) None
  | EvalAggError: ∀ step step' b e agg body c tr db Γ β p proxy s r s_key gb_keys gb_indices,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = false →
      eval step' body b (c, tr, proxy) None →
      eval step e b (c, tr, proxy) None
  | EvalAggArgError: ∀ step step' b e agg body c tr db Γ β p proxy s r s_key gb_keys gb_indices v bt l,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = false →
      eval step' body b (c, tr, proxy) (Some v) →
      snd v ≠ ValuePrimitiveList bt l →
      eval step e b (c, tr, proxy) None
  | EvalAgg: ∀ step step' b e agg body c tr db Γ β p proxy s r s_key gb_keys gb_indices v bt l res,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = false →
      eval step' body b (c, tr, proxy) (Some v) →
      snd v = ValuePrimitiveList bt l →
      eval_agg bt agg (c, tr, proxy) l res →
      eval step e b (c, tr, proxy) res
.

Inductive eval_expr:
  bool → config → tuple_wrapped → option groupby → expression → option (eval_env * e_value) → Prop :=
  | EvalExpr: ∀ b c tr proxy e env,
    eval 100 e b (c, tr, proxy) env → eval_expr b c tr proxy e env
.

Section Facts.

Import Bool.

Lemma expr_type_eqb_refl: ∀ τ, expr_type_eqb τ τ = true.
Proof.
  induction τ; simpl; try easy.
  - destruct b; simpl; reflexivity.
  - rewrite IHτ1, IHτ2. reflexivity.
Qed.

Lemma expr_type_eqb_eq_iff: ∀ τ1 τ2, expr_type_eqb τ1 τ2 = true ↔ τ1 = τ2.
Proof.
  induction τ1; intro τ2; destruct τ2; simpl; split; try easy; intros.
  - apply type_matches_eq in H. rewrite H. reflexivity.
  - inversion H. destruct b0; simpl; reflexivity.
  - apply andb_true_iff in H. destruct H.
    apply IHτ1_1 in H. apply IHτ1_2 in H0. subst. reflexivity.
  - inversion H. subst. apply andb_true_iff. split; apply expr_type_eqb_refl.
Qed.

End Facts.
