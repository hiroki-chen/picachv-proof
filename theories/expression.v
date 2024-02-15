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
.

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
  - Tuple.tuple s is the tuple of s, which represents the grouped columns.
  - group_range represents the range of each group.

  We define it as an inductive type because we want to be able to "hide" s; making it
  a dependent type would introduce undue complexity.
*)
Inductive groupby :=
  | groupby_proxy: ∀ s, Tuple.tuple s → group → groupby
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
*)
Inductive eval_unary_expression: unary_func → eval_env → e_value → option (eval_env * e_value) → Prop :=
  (* We only allow the argument to a unary function to be either a relation and a constant. *)
  | EvalUnaryNonEvaluable: ∀ τ f env v body f_e,
    v = ValueFunc τ body f_e  →
    eval_unary_expression f env v None
  | EvalUnaryValueTypeMismatch: ∀ f op env bt bt' v v' id lambda,
    v = ValuePrimitive bt (v', id) →
    f = unary_function op bt' lambda →
    (* We cannot cast it. *)
    try_cast bt bt' v' = None →
    eval_unary_expression f env v None
  | EvalUnaryValue: ∀ f op env bt bt' v v' v'' lambda,
    v = ValuePrimitive bt (v', None) →
    f = unary_function op bt' lambda →
    try_cast bt bt' v' = Some v'' →
    eval_unary_expression f env v (Some (env, ValuePrimitive bt' (lambda v'', None)))
  | EvalUnaryValueWithId: ∀ f env bt v v' id res,
    v = ValuePrimitive bt (v', Some id) →
    eval_unary_expression_in_cell bt f (v', id) env res →
    eval_unary_expression f env v res
.

(*
  Eval : (ℕ × Expr × Γ) × Maybe (Γ' × Val) 
    where 
  - ℕ is the number of steps to evaluate the expression.
  - Expr is the expression to evaluate.
  - Γ is the current environment.
  - Maybe (Γ' × Val) is the result of the evaluation:
    - If it is `None`, the evaluation results in an error.
    - If it is `Some (Γ', Val)`, the evaluation is finished with an updated environment Γ',
      and the result is `Val`.
*)
Inductive eval: nat → expression_lexed → eval_env → option (eval_env * e_value) → Prop :=
  (* The evaluation hangs and we have to force termination. *)
  | EvalNoStep: ∀ e env step, step = O → eval step e env None
  (* Evaluating a variable value is simple: we just lookup it. *)
  | EvalVar: ∀ step step' n e env c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_var n →
      eval step e (c, tr, lookup, proxy)
        (option_map (fun x => (env, x)) (List.nth_error lookup n))
  (* Evaluating a constant value is simple: we just return it. *)
  | EvalConst: ∀ step step' bt v e env c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_const bt v →
      eval step e (c, tr, lookup, proxy) (Some (env, ValuePrimitive bt (v, None)))
  | EvalColumn: ∀ step step' id n e env c s tr t lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_column id →
      tr = TupleWrapped s t →
      (* We locate this column by its identifier `id` using the comparison function. *)
      ∀ (find: find_index (λ x y, Nat.eqb (snd x) y) s id 0 = Some n),
        let col := 
          (Tuple.nth_col_tuple (♭ s) n
            (eq_sym (schema_to_no_name_length s) ♯
              (elem_find_index_bounded_zero _ _ _ _ find)) t) in
        eval step e (c, tr, lookup, proxy)
          (Some ((env, ValuePrimitive _ (fst (fst col), Some (snd (fst col))))))
  | EvalColumnFail: ∀ step step' id e c s tr t lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_column id →
      tr = TupleWrapped s t →
      (* The requested column identifier is not found. *)
      find_index (λ x y, Nat.eqb (snd x) y) s id 0 = None →
      eval step e (c, tr, lookup, proxy) None
  | EvalAbs: ∀ step step' τ e' e env c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_abs τ e' →
      eval step e (c, tr, lookup, proxy) (Some (env, ValueFunc τ e' lookup))
  | EvalApp: ∀ step step' e1 e2 e ev env env' v c tr lookup lookup' τ body f_env res db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_app e1 e2 →
      (* We first evaluate the function and obtain the updated environment and result. *)
      eval step' e1 (c, tr, lookup, proxy) (Some (env, ValueFunc τ body f_env)) →
      (* We then evaluate the argument. *)
      eval step' e2 (c, tr, lookup, proxy) (Some (env', v)) →
      env' = (ev, lookup', proxy) →
      (* Then we add the argument to the environment. *)
      eval step' body (ev, v :: f_env, proxy) res →
      eval step e (c, tr, lookup, proxy) res
  | EvalAppFail: ∀ step step' e e1 e2 res1 res2 c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_app e1 e2 →
      eval step' e1 (c, tr, lookup, proxy) res1 →
      eval step' e2 (c, tr, lookup, proxy) res2 →
      res1 = None ∨ res2 = None →
      eval step e (c, tr, lookup, proxy) None
  | EvalUnary: ∀ step step' e f e' env v res c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_unary f e' →
      eval step' e' (c, tr, lookup, proxy) (Some (env, v)) →
      eval_unary_expression f env v res →
      eval step e (c, tr, lookup, proxy) res
  | EvalAggProxyMissing: ∀ step step' e agg body c tr lookup db Γ β p proxy,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = None →
      e = expression_lexed_agg agg body →
      eval step e (c, tr, lookup, proxy) None
  | EvalAggProxy: ∀ step step' e agg body c tr lookup db Γ β p proxy s_key gb_keys gb_indices,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      proxy = Some (groupby_proxy s_key gb_keys gb_indices) →
      e = expression_lexed_agg agg body →
      (* TODO: Implement this. *)
      eval step e (c, tr, lookup, proxy) None
.

Inductive eval_expr:
  config → tuple_wrapped → option groupby → expression → option (eval_env * e_value) → Prop :=
  | EvalExpr: ∀ c tr proxy e env,
    eval 100 (lex e nil) (c, tr, nil, proxy) env → eval_expr c tr proxy e env
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
