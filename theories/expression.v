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
  | expr_type_basic: basic_type → expr_type
  | expr_type_func: expr_type → expr_type → expr_type
.

Fixpoint expr_type_eqb (τ1 τ2: expr_type): bool :=
  match τ1, τ2 with
    | expr_type_basic bt1, expr_type_basic bt2 => type_matches bt1 bt2
    | expr_type_func τ1a τ1b, expr_type_func τ2a τ2b =>
      andb (expr_type_eqb τ1a τ2a) (expr_type_eqb τ1b τ2b)
    | _, _ => false
  end.

(* There is no `let xxx in yyy` because it is unnecessary. *)
Inductive expression: Type :=
  (* x *)
  | expression_var: string → expression
  (* v *)
  | expression_const: ∀ bt, type_to_coq_type bt → expression
  (* a *)
  | expression_column: ∀ (n: nat), expression
  (* λ (x: τ). e *)
  | expression_abs: string → expr_type → expression → expression
  (* e1 e2 *)
  | expression_app: expression → expression → expression
  (* ∘ e *)
  | expression_unary: unary_func → expression → expression
  (* e1 ⊗ e2 *)
  | expression_binary: binary_func → expression → expression → expression
  (* fold *)
  | expression_agg: agg_func → expression → expression
.

(*
  The following is the lexed version of the expression.
  The reason why we need this is because we need to parse the expression from a string.

  A lexed lambda calculus expression is a lambda calculus expression with all the variables
  replaced by their indices in the original string. For example, the expression `λ x. x` will
  be lexed to `λ 0`. This is de Bruijn index.

  One reason for this is that we can eliminate the need for alpha conversion and substitution
  by using de Bruijn indices. So that looking up a variable is just a matter of looking up the
  index in the environment.
*)
Inductive expression_lexed: Type :=
  (* x *)
  | expression_lexed_var: nat → expression_lexed
  (* v *)
  | expression_lexed_const: ∀ bt, type_to_coq_type bt → expression_lexed
  (* a *)
  | expression_lexed_column: ∀ (n: nat), expression_lexed
  (* λ x. e *)
  | expression_lexed_abs: expr_type → expression_lexed → expression_lexed
  (* e1 e2 *)
  | expression_lexed_app: expression_lexed → expression_lexed → expression_lexed
  (* ∘ e *)
  | expression_lexed_unary: unary_func → expression_lexed → expression_lexed
  (* e1 ⊗ e2 *)
  | expression_lexed_binary: binary_func → expression_lexed → expression_lexed → expression_lexed
  (* fold *)
  | expression_lexed_agg: agg_func → expression_lexed → expression_lexed
.

Inductive e_value: Type :=
  | ValueFunc: expr_type → expression_lexed → list e_value → e_value
  (*
    A value can be associated with a unique identifier for looking up in the context;
    if it is not associated with an identifier, the identifier is `None` which means
    that it is just a "safe" value (like the value obtained by projecting a constant).
  *)
  | ValuePrimitive: ∀ bt, (type_to_coq_type bt * option nat) → e_value
  (* This is the argument for the aggregation expression because it operates on list of values. *)
  | ValuePrimitiveList: ∀ bt, list (type_to_coq_type bt * option nat) → e_value
.

(* TODO: How to evaluate expressions like (sum (a + b)) where a and b are columns? *)
(*
  My idea is:

  - First we will know that the groupby information.
  - Upon invoking `sum` we need to walk `a + b` but at this timepoint we have set
    `in_agg` to be true.
  - We will then evaluate `a + b` on the groupby proxy.
  - Thus `a + b` returns a list of values rather than a single value.

*)

(* `groupby` list is just a list of indices of the original data frame that should be chosen as keys. *)
Definition groupby_list := (list nat)%type.
(* simple_agg_expression := (AggOp * agg_func * nat) *)
Definition agg_list := (list (expression * nat))%type.
(* This represents a range of groups within the original data frame. *)
Definition group := (list nat)%type.

(*
  A groupby_proxy can be visualized as a pair:
  
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
  | groupby_proxy: ∀ s1 s2, relation s1 → Tuple.tuple s2 → group → groupby
.

Inductive tuple_wrapped: Type :=
  | TupleWrapped: ∀ s, Tuple.tuple (♭ s) → tuple_wrapped
.

Definition symbol_lookup_table := (list e_value)%type.

(*
  The evaluation environment for the lambda calculus is a list of:
  - The current configuration.
  - The current active tuple (for non-aggregate expressions).
  - The symbol lookup table.
  - The current groupby proxy (optional).
*)
Definition eval_env := (config * tuple_wrapped * symbol_lookup_table * option groupby)%type.

Fixpoint index (x: string) (env: list string): nat :=
  match env with
    | h :: t => if string_dec h x then 0 else 1 + index x t
    | _ => 0
  end.

Fixpoint lex (e: expression) (env: list string): expression_lexed :=
  match e with
  | expression_var x => expression_lexed_var (index x env)
  | expression_const bt v => expression_lexed_const bt v
  | expression_column n => expression_lexed_column n
  | expression_abs x τ e => expression_lexed_abs τ (lex e (x :: env))
  | expression_app e1 e2 => expression_lexed_app (lex e1 env) (lex e2 env)
  | expression_unary f e => expression_lexed_unary f (lex e env)
  | expression_binary f e1 e2 => expression_lexed_binary f (lex e1 env) (lex e2 env)
  | expression_agg f e => expression_lexed_agg f (lex e env)
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
  | E_UnaryLabelNotFound: ∀ bt f (arg: type_to_coq_type bt) id c tr lookup proxy db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      label_lookup Γ id = None ∨
      label_lookup p id = None →
      eval_unary_expression_in_cell bt f (arg, id) (c, tr, lookup, proxy) None
  | E_UnaryTypeError: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id c tr lookup proxy,
      f = unary_function op bt' lambda →
      bt ≠ bt' →
      eval_unary_expression_in_cell bt f (arg, id) (c, tr, lookup, proxy) None
  | E_UnaryPolicyError: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id db c tr lookup proxy Γ β p p_cur,
      c = ⟨ db Γ β p ⟩ →
      label_lookup Γ id = Some p_cur →
      f = unary_function op bt' lambda →
      bt = bt' → 
      let p_f := ∘ (Policy.policy_transform ((unary_trans_op op) :: nil)) in
        ¬ (p_cur ⪯ p_f) →
        eval_unary_expression_in_cell bt f (arg, id) (c, tr, lookup, proxy) None
  | E_UnaryPolicyOk: ∀ bt bt' f op lambda (arg: type_to_coq_type bt) id c tr lookup proxy
                       db Γ Γ' β β' p p' p_cur prov_cur,
      c = ⟨ db Γ β p ⟩ →
      label_lookup Γ id = Some p_cur →
      label_lookup p id = Some prov_cur →
      f = unary_function op bt' lambda →
      ∀ (eq: bt = bt'), let p_f := (Policy.policy_transform ((unary_trans_op op) :: nil)) in
        p_cur ⪯ (∘ p_f) →
          let p_new := get_new_policy p_cur p_f in
            let prov_new := prov_list (prov_trans_unary op) ((id, prov_cur) :: nil) in
              Γ' = update_label Γ id p_new →
              p' = update_label p id prov_new →
              eval_unary_expression_in_cell bt f (arg, id) (c, tr, lookup, proxy)
                (Some ((⟨ db Γ' β' p' ⟩, tr, lookup, proxy), ValuePrimitive bt' (lambda (eq ♯ arg), Some id)))
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
    f = unary_function op bt' lambda →
    (* We cannot cast it. *)
    try_cast bt bt' v' = None →
    eval_unary_expression_prim bt f env v None
  (* If a value does not carry any id, then it is just a value without any policy. *)
  | EvalUnaryValue: ∀ f op env bt bt' v v' v'' lambda,
    v = (v', None) →
    f = unary_function op bt' lambda →
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

(* bt1: the input type; bt2: the output type. *)
Inductive do_eval_agg:
  ∀ bt1 bt2, agg_func → Policy.context → prov_ctx → list (type_to_coq_type bt1 * option nat) →
    option (Policy.policy * prov * (type_to_coq_type bt2)) → Prop :=
  (* When the list being folded is empty, we shall return the initial value. *)
  | EvalDoAggNil: ∀ f op bt1 bt2 f' init_val Γ p l,
      l = nil →
      f = aggregate_function op bt1 bt2 f' init_val →
      do_eval_agg bt1 bt2 f Γ p l (Some (∎, ∅, init_val))
  | EvalDoAggLabelNotFound: ∀ f op bt1 bt2 f' init_val Γ p l hd hd_v id tl,
      l = hd :: tl →
      f = aggregate_function op bt1 bt2 f' init_val →
      hd = (hd_v, Some id) →
      label_lookup Γ id = None ∨
      label_lookup p id = None →
      do_eval_agg bt1 bt2 f Γ p l None
  | EvalDoAggPolicyError: ∀ f op bt1 bt2 f' init_val Γ p l hd hd_v id tl p_cur p_f,
      l = hd :: tl →
      f = aggregate_function op bt1 bt2 f' init_val →
      hd = (hd_v, Some id) →
      label_lookup Γ id = Some p_cur →
      p_f = ∘ (Policy.policy_agg (op :: nil)) →
      ¬ (p_cur ⪯ p_f) →
      do_eval_agg bt1 bt2 f Γ p l None
  | EvalDoAggPolicyConsError: ∀ bt1 bt2 f Γ p l hd tl,
      l = hd :: tl →
      do_eval_agg bt1 bt2 f Γ p tl None →
      do_eval_agg bt1 bt2 f Γ p l None
  | EvalDoAggOk: ∀ f op bt1 bt2 f' init_val Γ p l hd hd_v id tl tl_v p_cur p_f prov_cur p_tl p_final prov_tl,
      l = hd :: tl →
      f = aggregate_function op bt1 bt2 f' init_val →
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

(*
  This is just a simple wrapper around `do_eval_agg` that does the policy job.
*)
Inductive eval_agg: ∀ bt, agg_func → eval_env → list (type_to_coq_type bt * option nat) →
  option (eval_env * e_value) → Prop :=
  | EvalAggErr: ∀ bt f env db Γ β p l res,
      fst (fst (fst env)) = ⟨ db Γ β p ⟩ →
      do_eval_agg bt bt f Γ p l None →
      eval_agg bt f env l res
  | EvalAggOk: ∀ bt f env c tr proxy lookup db Γ β p l v policy provenance,
      env = (c, tr, lookup, proxy) →
      c = ⟨ db Γ β p ⟩ →
      do_eval_agg bt bt f Γ p l (Some (policy, provenance, v)) →
      let new_id := next_available_id Γ 0 in
      let Γ' := (new_id, policy) :: Γ in
      let p' := (new_id, provenance) :: p in
      let v' := (ValuePrimitive bt (v, Some new_id)) in
        eval_agg bt f env l (Some ((⟨ db Γ' β p' ⟩, tr, lookup, proxy), v'))
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
Inductive eval: nat → expression_lexed → bool → eval_env → option (eval_env * e_value) → Prop :=
  (* The evaluation hangs and we have to force termination. *)
  | EvalNoStep: ∀ e b env step, step = O → eval step e b env None
  (* Evaluating a variable value is simple: we just lookup it. *)
  | EvalVar: ∀ step step' n e b c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_var n →
      eval step e b (c, tr, lookup, proxy)
        (option_map (fun x => ((c, tr, lookup, proxy), x)) (List.nth_error lookup n))
  (* Evaluating a constant value is simple: we just return it. *)
  | EvalConst: ∀ step step' b bt v e c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_const bt v →
      eval step e b (c, tr, lookup, proxy) (Some ((c, tr, lookup, proxy), ValuePrimitive bt (v, None)))
  (* Extracts the value from the tuple if we are not inside an aggregation context. *)
  | EvalColumnNotAgg: ∀ step step' b id n e c s tr t lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_column id →
      tr = TupleWrapped s t →
      b = false →
      (* We locate this column by its identifier `id` using the comparison function. *)
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s id 0 = Some n),
        let col := 
          (Tuple.nth_col_tuple (♭ s) n
            (eq_sym (schema_to_no_name_length s) ♯
              (elem_find_index_bounded_zero _ _ _ _ find)) t) in
        eval step e b (c, tr, lookup, proxy)
          (Some (((c, tr, lookup, proxy), ValuePrimitive _ (fst (fst col), Some (snd (fst col))))))
  | EvalColumnNotAggFail: ∀ step step' b id e c s tr t lookup proxy,
      step = S step' →
      e = expression_lexed_column id →
      b = false →
      tr = TupleWrapped s t →
      (* The requested column identifier is not found. *)
      find_index (λ x y, Nat.eqb (snd x) y) s id 0 = None →
      eval step e b (c, tr, lookup, proxy) None
  (* Extracts the value from the groupby proxy if we are inside an aggregation context. *)
  | EvalColumnInAggProxyMissing: ∀ step step' b id e c tr lookup proxy,
      step = S step' →
      e = expression_lexed_column id →
      b = true →
      proxy = None →
      eval step e b (c, tr, lookup, proxy) None
  | EvalColumnInAgg: ∀ step step' b id n e c s1 s2 tr lookup proxy r gb_keys gb_indices,
      step = S step' →
      e = expression_lexed_column id →
      b = true →
      proxy = Some (groupby_proxy s1 s2 r gb_keys gb_indices) →
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s1 id 0 = Some n),
        let col' := extract_column_as_list s1 r n (elem_find_index_bounded_zero _ _ _ _ find) in
          let col := map (fun elem => (fst elem, Some (snd elem))) col' in
            eval step e b (c, tr, lookup, proxy) (Some ((c, tr, lookup, proxy), ValuePrimitiveList _ col))
  | EvalColumnInAggFail: ∀ step step' b id e c s1 s2 tr lookup proxy r gb_keys gb_indices,
      step = S step' →
      e = expression_lexed_column id →
      b = true →
      proxy = Some (groupby_proxy s1 s2 r gb_keys gb_indices) →
      find_index (λ x y, Nat.eqb (snd x) y) s1 id 0 = None →
      eval step e b (c, tr, lookup, proxy) None
  (* Evaluating a lambda expression is simple: we just return it. *)
  | EvalAbs: ∀ step step' b τ e' e env c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_abs τ e' →
      eval step e b (c, tr, lookup, proxy) (Some (env, ValueFunc τ e' lookup))
  | EvalApp: ∀ step step' b e1 e2 e ev env env' v c tr lookup lookup' τ body f_env res db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_app e1 e2 →
      (* We first evaluate the function and obtain the updated environment and result. *)
      eval step' e1 b (c, tr, lookup, proxy) (Some (env, ValueFunc τ body f_env)) →
      (* We then evaluate the argument. *)
      eval step' e2 b (c, tr, lookup, proxy) (Some (env', v)) →
      env' = (ev, lookup', proxy) →
      (* Then we add the argument to the environment. *)
      eval step' body b (ev, v :: f_env, proxy) res →
      eval step e b (c, tr, lookup, proxy) res
  | EvalAppFail: ∀ step step' b e e1 e2 res1 res2 c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_app e1 e2 →
      eval step' e1 b (c, tr, lookup, proxy) res1 →
      eval step' e2 b (c, tr, lookup, proxy) res2 →
      res1 = None ∨ res2 = None →
      eval step e b (c, tr, lookup, proxy) None
  | EvalUnary: ∀ step step' bt b e f e' env v v' res c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_unary f e' →
      b = false →
      eval step' e' b (c, tr, lookup, proxy) (Some (env, v)) →
      v = ValuePrimitive bt v' →
      eval_unary_expression_prim bt f env v' res →
      eval step e b (c, tr, lookup, proxy) res
  | EvalUnaryInAgg: ∀ step step' bt b e f e' env v v' res c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_unary f e' →
      b = true →
      eval step' e' b (c, tr, lookup, proxy) (Some (env, v)) →
      v = ValuePrimitiveList bt v' →
      eval_unary_expression_list bt f env v' res →
      eval step e b (c, tr, lookup, proxy) res
  (*
    There are still many other cases for us to deal with:

    - Type coercion.
    - Scalar value + vector value -> This means we need to propagate to lists.
   *)
  | EvalBinary: ∀ step step' bt1 bt2 b e f e1 e2 env v1 v1' v2 v2' res c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_binary f e1 e2 →
      b = false →
      eval step' e1 b (c, tr, lookup, proxy) (Some (env, v1)) →
      eval step' e2 b (c, tr, lookup, proxy) (Some (env, v2)) →
      v1 = ValuePrimitive bt1 v1' →
      v2 = ValuePrimitive bt2 v2' →
      eval_binary_expression_prim bt1 bt2 f env v1' v2' res →
      eval step e b (c, tr, lookup, proxy) res
  | EvalBinaryInAgg: ∀ step step' bt1 bt2 b e f e1 e2 env v1 v1' v2 v2' res c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_binary f e1 e2 →
      b = true →
      eval step' e1 b (c, tr, lookup, proxy) (Some (env, v1)) →
      eval step' e2 b (c, tr, lookup, proxy) (Some (env, v2)) →
      v1 = ValuePrimitiveList bt1 v1' →
      v2 = ValuePrimitiveList bt2 v2' →
      eval_binary_expression_list bt1 bt2 f env v1' v2' res →
      eval step e b (c, tr, lookup, proxy) res
  (* Nested aggregation makes no sense. *)
  | EvalNestedAgg: ∀ step step' b e agg body c tr lookup db Γ β p proxy s r s_key gb_keys gb_indices,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (groupby_proxy s s_key r gb_keys gb_indices) →
      e = expression_lexed_agg agg body →
      b = true →
      eval step e b (c, tr, lookup, proxy) None
  | EvalAggProxyMissing: ∀ step step' b e agg body c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = None →
      b = false →
      e = expression_lexed_agg agg body →
      eval step e b (c, tr, lookup, proxy) None
  | EvalAggError: ∀ step step' b e agg body c tr lookup db Γ β p proxy s r s_key gb_keys gb_indices,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (groupby_proxy s s_key r gb_keys gb_indices) →
      e = expression_lexed_agg agg body →
      b = false →
      eval step' body b (c, tr, lookup, proxy) None →
      eval step e b (c, tr, lookup, proxy) None
  | EvalAggArgError: ∀ step step' b e agg body c tr lookup db Γ β p proxy s r s_key gb_keys gb_indices v bt l,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (groupby_proxy s s_key r gb_keys gb_indices) →
      e = expression_lexed_agg agg body →
      b = false →
      eval step' body b (c, tr, lookup, proxy) (Some v) →
      snd v ≠ ValuePrimitiveList bt l →
      eval step e b (c, tr, lookup, proxy) None
  | EvalAgg: ∀ step step' b e agg body c tr lookup db Γ β p proxy s r s_key gb_keys gb_indices v bt l res,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (groupby_proxy s s_key r gb_keys gb_indices) →
      e = expression_lexed_agg agg body →
      b = false →
      eval step' body b (c, tr, lookup, proxy) (Some v) →
      snd v = ValuePrimitiveList bt l →
      eval_agg bt agg (c, tr, lookup, proxy) l res →
      eval step e b (c, tr, lookup, proxy) res
.

Inductive eval_expr:
  bool → config → tuple_wrapped → option groupby → expression → option (eval_env * e_value) → Prop :=
  | EvalExpr: ∀ b c tr proxy e env,
    eval 100 (lex e nil) b (c, tr, nil, proxy) env → eval_expr b c tr proxy e env
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
