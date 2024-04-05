Require Import Arith.Compare_dec.
Require Import Lia.
Require Import List.
Require Import String.
Require Import Unicode.Utf8.

Require Import config.
Require Import data_model.
Require Import lattice.
Require Import ordering.
Require Import relation.
Require Import trace.
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
 * Try to get a policy or the default policy if not found; it is useful for
 * cells that do not carry labels at all because they have no labels at all.
 *)
Definition try_get_policy (tr: trace) (id: option nat) :=
  match id with
  | Some id' => match label_lookup tr id' with
                | Some tr' => extract_policy tr'
                | None => ∎
                end
  | None => ∎
  end.

Definition try_get_new_trace (tr: trace) (id1 id2: option nat) op p :=
  let tr1 := match id1 with
             | Some id1' => label_lookup tr id1'
             | None => None
             end in
  let tr2 := match id2 with
             | Some id2' => label_lookup tr id2'
             | None => None
             end in
    match tr1, tr2 with
    | Some tr1', Some tr2' => TrBranch op p (tr1' :: tr2' :: nil)
    | Some tr1', None => TrBranch op p (tr1' :: nil)
    | None, Some tr2' => TrBranch op p (tr2' :: nil)
    | None, None => TrBranch op p nil
    end.

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
  - The current budget.
  - The current trace.
  - The current active tuple (for non-aggregate expressions).
  - The current groupby proxy (optional).
*)
Definition eval_env := (budget * trace * tuple_wrapped * option groupby)%type.

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

Inductive eval_unary_expression_in_cell: ∀ bt,
  unary_func → (type_to_coq_type bt * nat) → eval_env →
    option (eval_env * e_value) → Prop :=
  | E_UnaryLabelNotFound: ∀ bt f (arg: type_to_coq_type bt) id tp proxy β tr,
      label_lookup tr id = None →
      eval_unary_expression_in_cell bt f (arg, id) (β, tr, tp, proxy) None
  | E_UnaryTypeError: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id ee tr proxy,
      f = UnaryFunc op bt' lambda →
      bt ≠ bt' →
      eval_unary_expression_in_cell bt f (arg, id) (ee, tr, proxy) None
  | E_UnaryPolicyError: ∀ bt bt' f op lambda
                         (arg: type_to_coq_type bt) id
                         tp tr_cur proxy β tr p_cur,
      label_lookup tr id = Some tr_cur →
      extract_policy tr_cur = p_cur →
      f = UnaryFunc op bt' lambda →
      bt = bt' → 
      let p_f := ∘ (Policy.policy_transform ((unary_trans_op op) :: nil)) in
        ¬ (p_cur ⪯ p_f) →
        eval_unary_expression_in_cell bt f (arg, id) (β, tr, tp, proxy) None
  | E_UnaryPolicyOk: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id tp proxy
                       β β' tr tr' p_cur tr_cur,
      label_lookup tr id = Some tr_cur →
      extract_policy tr_cur = p_cur →
      f = UnaryFunc op bt' lambda →
      ∀ (eq: bt = bt'), let p_f := (Policy.policy_transform ((unary_trans_op op) :: nil)) in
        p_cur ⪯ (∘ p_f) →
          let p_new := get_new_policy p_cur p_f in
            let tr_new := TrLinear (prov_trans_unary op) p_new tr_cur in
              tr' = update_label tr id tr_new →
              eval_unary_expression_in_cell bt f (arg, id) (β, tr', tp, proxy)
                (Some ((β', tr', tp, proxy), ValuePrimitive bt' (lambda (eq ♯ arg), Some id)))
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

(*
  Somehow more complicated case because we have to deal with
  * Label = None => OK.
  * Label = Some id ∧ policy not found.
  * Label = Some id ∧ policy not valid.
  * Label = Some id ∧ policy valid.

  So, in all, there would be 16 cases in total. Simply iterating all possible cases
  would be a nightmare, but we can merge some cases:
  * policy_valid lhs ∧ policy_valid rhs
    - (Label = None ∨ (Label = Some id ∧ policy valid)) ∧ (Label = None ∨ (Label = Some id ∧ policy valid))
  * policy_invalid lhs ∨ policy_invalid rhs
    - all the rest cases.

  Although it seems feasible, when we are dealing with trace update, how can we ensure that id is
  really meaningful? ...

  TODO: We need a cleverer way to do this.
*)
Inductive eval_binary_expression_in_cell: ∀ bt,
  binary_func → (type_to_coq_type bt * option nat) → (type_to_coq_type bt * option nat) → eval_env →
    option (eval_env * e_value) → Prop :=
  | E_BinaryLabelNotFound: ∀ bt f v1 v2 id1 id1' id2 id2' tp proxy β tr,
      (id1 = Some id1' ∧ label_lookup tr id1' = None) ∨
      (id2 = Some id2' ∧ label_lookup tr id2' = None) →
      eval_binary_expression_in_cell bt f (v1, id1) (v2, id2)  (β, tr, tp, proxy) None
  | E_BinaryTypeError: ∀ bt bt' f op lambda arg1 arg2 ee tr proxy,
      f = BinFunc op bt' lambda →
      bt ≠ bt' →
      eval_binary_expression_in_cell bt f arg1 arg2 (ee, tr, proxy) None
  | E_BinaryPolicyError:
      ∀ bt bt' f op lambda
        arg1 arg2 id1 id2 id1' id2'
        tp proxy β tr
        p_cur1 p_cur2,
      f = BinFunc op bt' lambda →
      let p_f := Policy.policy_transform ((binary_trans_op op) :: nil) in
        p_cur1 = try_get_policy tr id1' →
        p_cur2 = try_get_policy tr id2' →
        ¬ (p_cur1 ⪯ (∘ p_f)) ∨ ¬ (p_cur2 ⪯ (∘ p_f)) →
        eval_binary_expression_in_cell bt f (arg1, id1) (arg2, id2) (β, tr, tp, proxy) None
| E_BinaryPolicyOk:
      ∀ bt bt' f op lambda
        arg1 arg2 id1 id2 id1' id2'
        tp proxy β tr
        p_cur1 p_cur2 p_new
        (eq: bt = bt'),
      f = BinFunc op bt' lambda →
      let p_f := Policy.policy_transform ((binary_trans_op op) :: nil) in
      let new_id := next_available_id tr 0 in
      let tr_new := try_get_new_trace tr id1' id2' (prov_trans_binary op) p_new in
        p_cur1 ↑ p_cur2 = p_new →
        p_cur1 = try_get_policy tr id1' →
        p_cur2 = try_get_policy tr id2' →
        p_cur1 ⪯ (∘ p_f) ∧ p_cur2 ⪯ (∘ p_f) →
        eval_binary_expression_in_cell bt f (arg1, id1) (arg2, id2) (β, tr, tp, proxy)
          (Some ((β, ((new_id, tr_new) :: tr), tp, proxy),
            ValuePrimitive bt' (lambda (eq ♯ arg1) (eq ♯ arg2), Some new_id)))
.

(* For binary expressions we just need to check if the operands satisfy their own policies. *)
Inductive eval_binary_expression_prim:
  ∀ bt1 bt2, binary_func → eval_env → (type_to_coq_type bt1 * option nat) → (type_to_coq_type bt2 * option nat) →
  option (eval_env * e_value) → Prop :=
  | EvalBinaryValueTypeMismatch: ∀ f op env bt1 bt2 bt lambda v1 v2 v1' v2' id1 id2,
    v1 = (v1', id1) →
    v2 = (v2', id2) →
    f = BinFunc op bt lambda →
    (* We cannot cast it. *)
    try_cast bt1 bt v1' = None ∨ try_cast bt2 bt v2' = None →
    eval_binary_expression_prim bt1 bt2 f env v1 v2 None
  | EvalBinaryValueOk: ∀ f op env bt1 bt2 bt lambda v1 v2 v1' v2' v1'' v2'' id1 id2 res,
    v1 = (v1', id1) →
    v2 = (v2', id2) →
    f = BinFunc op bt lambda →
    try_cast bt1 bt v1' = Some v1'' →
    try_cast bt2 bt v2' = Some v2'' →
    eval_binary_expression_in_cell bt f (v1'', id1) (v2'', id2) env res →
    eval_binary_expression_prim bt1 bt2 f env v1 v2 res
.

Inductive eval_binary_expression_list:
  ∀ bt1 bt2, binary_func → eval_env → list (type_to_coq_type bt1 * option nat) → list (type_to_coq_type bt2 * option nat)
    → option (eval_env * e_value) → Prop :=
  (* The length of the lists must match. *)
  | EvalBinaryListLengthMismatch: ∀ bt1 bt2 f env l1 l2,
    List.length l1 ≠ List.length l2 →
    eval_binary_expression_list bt1 bt2 f env l1 l2 None
  | EvalBinaryListNil: ∀ bt1 bt2 f env l1 l2,
    l1 = nil → l2 = nil →
    eval_binary_expression_list bt1 bt2 f env l1 l2 (Some (env, ValuePrimitiveList bt1 nil))
  | EvalBinaryListHeadError: ∀ bt1 bt2 f env l1 l2 hd1 hd2 tl1 tl2,
    l1 = hd1 :: tl1 → l2 = hd2 :: tl2 →
    eval_binary_expression_prim bt1 bt2 f env hd1 hd2 None →
    eval_binary_expression_list bt1 bt2 f env l1 l2 None
  | EvalBinaryListTailError: ∀ bt1 bt2 f env l1 l2 hd1 hd2 tl1 tl2,
    l1 = hd1 :: tl1 → l2 = hd2 :: tl2 →
    eval_binary_expression_list bt1 bt2 f env tl1 tl2 None →
    eval_binary_expression_list bt1 bt2 f env l1 l2 None
  | EvalBinaryListOk: ∀ bt1 bt2 f env env' env'' l1 l2 hd1 hd2 tl1 tl2 hd' tl',
    l1 = hd1 :: tl1 → l2 = hd2 :: tl2 →
    eval_binary_expression_prim bt1 bt2 f env hd1 hd2 (Some (env', ValuePrimitive bt1 hd')) →
    eval_binary_expression_list bt1 bt2 f env' tl1 tl2 (Some (env'', ValuePrimitiveList bt1 tl')) →
    eval_binary_expression_list bt1 bt2 f env l1 l2 (Some (env'', ValuePrimitiveList bt1 (hd' :: tl')))
.

(* bt1: the input type; bt2: the output type; this evaluates the aggregation expression within a group. *)
Inductive do_eval_agg:
  ∀ bt1 bt2, agg_func → trace → list (type_to_coq_type bt1 * option nat) →
    option (Policy.policy * (list trace_ty) * (type_to_coq_type bt2)) → Prop :=
  (* When the list being folded is empty, we shall return the initial value. *)
  | EvalDoAggNil: ∀ f op bt1 bt2 f' init_val noise tr l,
      l = nil →
      f = AggFunc op bt1 bt2 f' init_val noise →
      do_eval_agg bt1 bt2 f tr l (Some (∎, nil, init_val))
  | EvalDoAggLabelNotFound: ∀ f op bt1 bt2 f' init_val noise p l hd hd_v id tl,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup p id = None →
      do_eval_agg bt1 bt2 f p l None
  | EvalDoAggPolicyError: ∀ f op bt1 bt2 f' init_val noise tr tr_cur l hd hd_v id tl p_cur p_f,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup tr id = Some tr_cur →
      extract_policy tr_cur = p_cur →
      p_f = ∘ (Policy.policy_agg (op :: nil)) →
      ¬ (p_cur ⪯ p_f) →
      do_eval_agg bt1 bt2 f tr l None
  | EvalDoAggPolicyConsError: ∀ bt1 bt2 f tr l hd tl,
      l = hd :: tl →
      do_eval_agg bt1 bt2 f tr tl None →
      do_eval_agg bt1 bt2 f tr l None
  (* These evaluation rules cannot guarantee *)
  | EvalDoAggOk: ∀ f op bt1 bt2 f' init_val noise tr l hd hd_v
                   id tl tl_v p_cur p_f tr_cur tr_new p_tl tr_tl,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup tr id = Some tr_cur →
      extract_policy tr_cur = p_cur →
      p_f = ∘ (Policy.policy_agg (op :: nil)) →
      p_cur ⪯ p_f →
      do_eval_agg bt1 bt2 f tr tl (Some (p_tl, tr_tl, tl_v)) →
      let p_new := get_new_policy p_cur (Policy.policy_agg (op :: nil)) in
      let res := f' tl_v hd_v in
        tr_new = tr_cur :: tr_tl →
        p_new ⪯ p_tl →
        do_eval_agg bt1 bt2 f tr l (Some (p_tl, tr_new, res))
  | EvalDoAggOk2: ∀ f op bt1 bt2 f' init_val noise tr l hd hd_v
                   id tl tl_v p_cur p_f tr_cur tr_new p_tl tr_tl,
      l = hd :: tl →
      f = AggFunc op bt1 bt2 f' init_val noise →
      hd = (hd_v, Some id) →
      label_lookup tr id = Some tr_cur →
      extract_policy tr_cur = p_cur →
      p_f = ∘ (Policy.policy_agg (op :: nil)) →
      p_cur ⪯ p_f →
      do_eval_agg bt1 bt2 f tr tl (Some (p_tl, tr_tl, tl_v)) →
      let p_new := get_new_policy p_cur (Policy.policy_agg (op :: nil)) in
      let res := f' tl_v hd_v in
        tr_new = tr_cur :: tr_tl →
        p_tl ⪯ p_new →
        do_eval_agg bt1 bt2 f tr l (Some (p_new, tr_new, res))
.

Inductive apply_noise:
  ∀ bt, type_to_coq_type bt → budget → noise_gen → nat → Policy.policy → trace_ty → trace →
    option (type_to_coq_type bt * budget * trace) → Prop :=
  | ApplyNoiseTooWeak: ∀ bt v β ε δ 𝒩 oracle new_id policy tr_ty tr,
      𝒩 = NoiseGen (ε, δ) oracle →
      let p_f := (Policy.policy_noise (differential_privacy (ε, δ))) in
      ¬ (policy ⪯ (∘ p_f)) →
      apply_noise bt v β 𝒩 new_id policy tr_ty tr None
  | ApplyNoiseNoBudget: ∀ bt v β ε δ 𝒩 oracle new_id policy tr_ty tr,
      𝒩 = NoiseGen (ε, δ) oracle →
      let p_f := (Policy.policy_noise (differential_privacy (ε, δ))) in
      policy ⪯ (∘ p_f) →
      β < ε →
      apply_noise bt v β 𝒩 new_id policy tr_ty tr None
  | ApplyNoiseOk: ∀ bt v β ε δ 𝒩 oracle new_id policy tr_ty tr,
      𝒩 = NoiseGen (ε, δ) oracle →
      let p_f := (Policy.policy_noise (differential_privacy (ε, δ))) in
      (* The privacy requirement is satisfied. *)
      policy ⪯ (∘ p_f) →
      β ≥ ε →
      let policy' := get_new_policy policy p_f in
      let trace' := TrLinear (prov_noise (differential_privacy (ε, δ))) policy' tr_ty in
      let β' := β - ε in
      let tr' := (new_id, trace') :: tr in
      apply_noise bt v β 𝒩 new_id policy tr_ty tr (Some (oracle _ v, β', tr'))
.

(*
  This is just a simple wrapper around `do_eval_agg` that does the policy job.
*)
Inductive eval_agg: ∀ bt, agg_func → eval_env → list (type_to_coq_type bt * option nat) →
  option (eval_env * e_value) → Prop :=
  | EvalAggErr: ∀ bt f env β tr l,
      fst (fst env) = (β, tr) →
      do_eval_agg bt bt f tr l None →
      eval_agg bt f env l None
  | EvalAggOkNoNoise: ∀ bt bt' f op f' init_val env tp proxy β tr l v policy trace,
      env = (β, tr, tp, proxy) →
      f = AggFunc op bt bt' f' init_val None →
      do_eval_agg bt bt' f tr l (Some (policy, trace, v)) →
      let new_id := next_available_id tr 0 in
      let tr' := (new_id, TrBranch (prov_agg op) (∘ (Policy.policy_agg (op :: nil))) trace) :: tr in
      let v' := (ValuePrimitive bt' (v, Some new_id)) in
        eval_agg bt f env l (Some ((β, tr', tp, proxy), v'))
  | EvalAggOkNoBudget: ∀ bt bt'  f op f' init_val noise env tp proxy β tr l v policy trace,
      env = (β, tr, tp, proxy) →
      f = AggFunc op bt bt' f' init_val (Some noise) →
      do_eval_agg bt bt' f tr l (Some (policy, trace, v)) →
      let new_id := next_available_id tr 0 in
      apply_noise bt' v β noise new_id policy (TrBranch (prov_agg op) (∘ (Policy.policy_agg (op :: nil))) trace) tr None →
      eval_agg bt f env l None
  | EvalAggOkNoise: ∀ bt bt' f op f' init_val noise
                      env tp proxy β β' tr tr' l v v' policy trace res,
      env = (β, tr, tp, proxy) →
      f = AggFunc op bt bt' f' init_val (Some noise) →
      do_eval_agg bt bt' f tr l (Some (policy, trace, v)) →
      let new_id := next_available_id tr 0 in
      apply_noise bt' v β noise new_id policy (TrBranch (prov_agg op) (∘ (Policy.policy_agg (op :: nil))) trace) tr res →
      res = Some (v', β', tr') →
      eval_agg bt f env l (Some ((β', tr', tp, proxy), ValuePrimitive _ (v', Some new_id)))
.

(*
  Eval : (ℕ × Expr × 𝔹 × Γ) × Maybe (Γ' × Val) 
    where 
  - ℕ is the number of steps to evaluate the expression.
  - Expr is the expression to evaluate.
  - 𝔹 is a boolean flag indicating whether the evaluation is performed within an aggregation context.
    - If it is `true`, we need to evaluate the expression on groupby proxy rather than the current tuple.
  - is the current environment.
  - Maybe (Γ' × Val) is the result of the evaluation:
    - If it is `None`, the evaluation results in an error.
    - If it is `Some (Γ', Val)`, the evaluation is finished with an updated environment Γ',
      and the result is `Val`.
*)
Inductive eval: nat → expression → bool → eval_env → option (eval_env * e_value) → Prop :=
  (* The evaluation hangs and we have to force termination. *)
  | EvalNoStep: ∀ e b env step, step = O → eval step e b env None
  (* Evaluating a constant value is simple: we just return it. *)
  | EvalConst: ∀ step step' b bt v e tr β tp proxy,
      step = S step' →
      e = ExprConst bt v →
      eval step e b (β, tr, tp, proxy) (Some ((β, tr, tp, proxy), ValuePrimitive bt (v, None)))
  (* Extracts the value from the tuple if we are not inside an aggregation context. *)
  | EvalColumnNotAgg: ∀ step step' b id n e s tp t β tr proxy,
      step = S step' →
      e = ExprCol id →
      tp = TupleWrapped s t →
      b = false →
      (* We locate this column by its identifier `id` using the comparison function. *)
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s id 0 = Some n),
        let col := 
          (Tuple.nth_col_tuple (♭ s) n
            (eq_sym (schema_to_no_name_length s) ♯
              (elem_find_index_bounded_zero _ _ _ _ find)) t) in
        eval step e b (β, tr, tp, proxy)
          (Some (((β, tr, tp, proxy), ValuePrimitive _ (fst (fst col), Some (snd (fst col))))))
  | EvalColumnNotAggFail: ∀ step step' b id e c s tp t proxy,
      step = S step' →
      e = ExprCol id →
      b = false →
      tp = TupleWrapped s t →
      (* The requested column identifier is not found. *)
      find_index (λ x y, Nat.eqb (snd x) y) s id 0 = None →
      eval step e b (c, tp, proxy) None
  (* Extracts the value from the groupby proxy if we are inside an aggregation context. *)
  | EvalColumnInAggProxyMissing: ∀ step step' b id e c tp proxy,
      step = S step' →
      e = ExprCol id →
      b = true →
      proxy = None →
      eval step e b (c, tp, proxy) None
  | EvalColumnInAgg: ∀ step step' b id n e c s1 s2 tp proxy r gb_keys gb_indices,
      step = S step' →
      e = ExprCol id →
      b = true →
      proxy = Some (GroupbyProxy s1 s2 r gb_keys gb_indices) →
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s1 id 0 = Some n),
        let col' := extract_column_as_list s1 r n (elem_find_index_bounded_zero _ _ _ _ find) in
          let col := map (fun elem => (fst elem, Some (snd elem))) col' in
            eval step e b (c, tp, proxy) (Some ((c, tp, proxy), ValuePrimitiveList _ col))
  | EvalColumnInAggFail: ∀ step step' b id e c s1 s2 tp proxy r gb_keys gb_indices,
      step = S step' →
      e = ExprCol id →
      b = true →
      proxy = Some (GroupbyProxy s1 s2 r gb_keys gb_indices) →
      find_index (λ x y, Nat.eqb (snd x) y) s1 id 0 = None →
      eval step e b (c, tp, proxy) None
  | EvalUnary: ∀ step step' bt b e f e' env v v' res tp β tr proxy,
      step = S step' →
      e = ExprUnary f e' →
      b = false →
      eval step' e' b (β, tr, tp, proxy) (Some (env, v)) →
      v = ValuePrimitive bt v' →
      eval_unary_expression_prim bt f env v' res →
      eval step e b (β, tr, tp, proxy) res
  | EvalUnaryInAgg: ∀ step step' bt b e f e' env v v' res tp β tr proxy,
      step = S step' →
      e = ExprUnary f e' →
      b = true →
      eval step' e' b (β, tr, tp, proxy) (Some (env, v)) →
      v = ValuePrimitiveList bt v' →
      eval_unary_expression_list bt f env v' res →
      eval step e b (β, tr, tp, proxy) res
  (*
    There are still many other cases for us to deal with:

    - Type coercion.
    - Scalar value + vector value -> This means we need to propagate to lists.
    - Not implemented yet??
   *)
  | EvalBinary: ∀ step step' bt1 bt2 b e f e1 e2 env1 env2 env v1 v1' v2 v2' res tp β tr proxy,
      step = S step' →
      e = ExprBinary f e1 e2 →
      b = false →
      eval step' e1 b (β, tr, tp, proxy) (Some (env1, v1)) →
      eval step' e2 b (β, tr, tp, proxy) (Some (env2, v2)) →
      (* Need to merge env1 and env2 *)
      v1 = ValuePrimitive bt1 v1' →
      v2 = ValuePrimitive bt2 v2' →
      eval_binary_expression_prim bt1 bt2 f env v1' v2' res →
      eval step e b (β, tr, tp, proxy) res
  | EvalBinaryInAgg: ∀ step step' bt1 bt2 b e f e1 e2 env v1 v1' v2 v2' res tp β tr proxy,
      step = S step' →
      e = ExprBinary f e1 e2 →
      b = true →
      eval step' e1 b (β, tr, tp, proxy) (Some (env, v1)) →
      eval step' e2 b (β, tr, tp, proxy) (Some (env, v2)) →
      v1 = ValuePrimitiveList bt1 v1' →
      v2 = ValuePrimitiveList bt2 v2' →
      eval_binary_expression_list bt1 bt2 f env v1' v2' res →
      eval step e b (β, tr, tp, proxy) res
  (* Nested aggregation makes no sense. *)
  | EvalNestedAgg: ∀ step step' b e agg body tp β tr proxy s r s_key gb_keys gb_indices,
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = true →
      eval step e b (β, tr, tp, proxy) None
  | EvalAggProxyMissing: ∀ step step' b e agg body tp β tr proxy,
      step = S step' →
      proxy = None →
      b = false →
      e = ExprAgg agg body →
      eval step e b (β, tr, tp, proxy) None
  | EvalAggError: ∀ step step' b e agg body tp β tr proxy s r s_key gb_keys gb_indices,
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = false →
      eval step' body b (β, tr, tp, proxy) None →
      eval step e b (β, tr, tp, proxy) None
  | EvalAggArgError: ∀ step step' b e agg body tp β tr proxy s r s_key gb_keys gb_indices v bt l,
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = false →
      eval step' body b (β, tr, tp, proxy) (Some v) →
      snd v ≠ ValuePrimitiveList bt l →
      eval step e b (β, tr, tp, proxy) None
  | EvalAgg: ∀ step step' b e agg body tp β tr proxy s r s_key gb_keys gb_indices v bt l res,
      step = S step' →
      proxy = Some (GroupbyProxy s s_key r gb_keys gb_indices) →
      e = ExprAgg agg body →
      b = false →
      eval step' body b (β, tr, tp, proxy) (Some v) →
      snd v = ValuePrimitiveList bt l →
      eval_agg bt agg (β, tr, tp, proxy) l res →
      eval step e b (β, tr, tp, proxy) res
.

Inductive eval_expr:
  bool → (budget * trace) → tuple_wrapped → option groupby → expression → option (eval_env * e_value) → Prop :=
  | EvalExpr: ∀ b tp proxy β e env,
    eval 100 e b (β, tp, proxy) env → eval_expr b β tp proxy e env
.

Section Facts.

Import Bool.

Lemma get_new_policy_lower: ∀ p1 p2 op,
  Policy.valid_policy p1 ∧ Policy.valid_policy p2 →
  p1 ⪯ p2 →
  get_new_policy p1 op ⪯ p2.
Proof.
  intros; intuition; inversion H0; subst.
  - simpl. assumption.
  - destruct p1; simpl.
    + destruct H. discriminate.
    + destruct H, H3. inversion H. subst.
      destruct Policy.can_declassify_dec.
      * apply Policy.preceq_implies in H0. assumption.
      * assumption.
Qed.

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
