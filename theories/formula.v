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

Inductive expression: Type :=
  (* x *)
  | expression_var: string → expression
  (* v *)
  | expression_const: ∀ bt, type_to_coq_type bt → expression
  (* a *)
  | expression_column: ∀ (n: nat), expression
  (* λ x. e *)
  | expression_abs: string → expression → expression
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
  | expression_lexed_abs: expression_lexed → expression_lexed
  (* e1 e2 *)
  | expression_lexed_app: expression_lexed → expression_lexed → expression_lexed
  (* ∘ e *)
  | expression_lexed_unary: unary_func → expression_lexed → expression_lexed
  (* e1 ⊗ e2 *)
  | expression_lexed_binary: binary_func → expression_lexed → expression_lexed → expression_lexed
  (* fold *)
  | expression_lexed_agg: agg_func → expression_lexed → expression_lexed
.

(* `groupby` list is just a list of indices of the original data frame that should be chosen as keys. *)
Definition groupby_list := (list nat)%type.
(* simple_agg_expression := (AggOp * agg_func * nat) *)
Definition agg_list := (list (expression * string))%type.

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
*)
Definition groupby_proxy s := (Tuple.tuple (♭ s) * group)%type.

Inductive EResult: Type :=
  | EResultError: EResult
  | EResultFunction: expression_lexed → list EResult → EResult
  | EResultValue: ∀ bt, type_to_coq_type bt → EResult
  | EResultRelation: relation_wrapped → EResult
.

Definition symbol_lookup_table := (list EResult)%type.

(*
  The evaluation environment Γ for the lambda calculus is a list of:
  - The current configuration.
  - The current active relation.
  - The symbol lookup table.
*)
Definition eval_env := (config * relation_wrapped * symbol_lookup_table)%type.

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
  | expression_abs x e => expression_lexed_abs (lex e (x :: env))
  | expression_app e1 e2 => expression_lexed_app (lex e1 env) (lex e2 env)
  | expression_unary f e => expression_lexed_unary f (lex e env)
  | expression_binary f e1 e2 => expression_lexed_binary f (lex e1 env) (lex e2 env)
  | expression_agg f e => expression_lexed_agg f (lex e env)
  end.

Inductive eval_unary_expression_in_relation: ∀ (s: schema) (r: relation s),
  unary_func → eval_env → (eval_env * EResult) → Prop :=
.

(*
  This function evaluates a unary expression with a given function.
*)
Inductive eval_unary_expression: unary_func → eval_env → EResult → (eval_env * EResult) → Prop :=
  | EvalUnaryNonEvaluable: ∀ f env v body f_e,
    v = EResultError ∨ v = EResultFunction body f_e →
    eval_unary_expression f env v (env, EResultError)
  | EvalUnaryValueTypeMismatch: ∀ f op env bt bt' v v' lambda,
    v = EResultValue bt v' →
    f = unary_function op bt' lambda →
    bt' ≠ bt →
    eval_unary_expression f env v (env, EResultError)
  | EvalUnaryValue: ∀ f op env bt bt' v v' lambda,
    v = EResultValue bt v' →
    f = unary_function op bt' lambda →
      ∀ (eq: bt = bt'),
        eval_unary_expression f env v (env, EResultValue bt' (lambda (eq ♯ v')))
  | EvalUnaryRelation: ∀ f env env' v s r,
    v = relation_output s r →
    eval_unary_expression_in_relation s r f env env' →
    eval_unary_expression f env (EResultRelation v) env'
.

Inductive eval: nat → expression_lexed → eval_env → (eval_env * EResult) → Prop :=
  (* The evaluation hangs and we have to force termination. *)
  | EvalNoStep: ∀ e env step, step = O → eval step e env (env, EResultError)
  (* Evaluating a variable value is simple: we just lookup it. *)
  | EvalVar: ∀ step step' n e env c r lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_var n →
      eval step e (c, r, lookup) (env, nth_default EResultError n lookup)
  (* Evaluating a constant value is simple: we just return it. *)
  | EvalConst: ∀ step step' bt v e env c r lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_const bt v →
      eval step e (c, r, lookup) (env, EResultValue bt v)
  | EvalColumn: ∀ step step' n e env c s r r' lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_column n →
      r = relation_output s r' →
      ∀ ok: n < List.length s,
        eval step e (c, r, lookup) (env, EResultRelation (relation_output _ (extract_column s r' n ok)))
  | EvalColumnFail: ∀ step step' n e env c s r r' lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_column n →
      r = relation_output s r' →
      ¬ (n < List.length s) →
      eval step e (c, r, lookup) (env, EResultError)
  | EvalAbs: ∀ step step' e' e env c r lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_abs e' →
      eval step e (c, r, lookup) (env, EResultFunction e' lookup)
  | EvalApp: ∀ step step' e1 e2 e ev env env' v c r lookup lookup' body f_env res db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_app e1 e2 →
      (* We first evaluate the function and obtain the updated environment and result. *)
      eval step' e1 (c, r, lookup) (env, EResultFunction body f_env) →
      (* We then evaluate the argument. *)
      eval step' e2 (c, r, lookup) (env', v) →
      v ≠ EResultError →
      env' = (ev, lookup') →
      (* Then we add the argument to the environment. *)
      eval step' body (ev, v :: f_env) res →
      eval step e (c, r, lookup) res
  | EvalAppFail: ∀ step step' e e1 e2 env env' f body f_env v c r lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_app e1 e2 →
      eval step' e1 (c, r, lookup) (env, f) →
      eval step' e2 (c, r, lookup) (env', v) →
      v = EResultError ∨ f ≠ EResultFunction body f_env →
      eval step e (c, r, lookup) (env, EResultError)
  | EvalUnary: ∀ step step' e f e' env v res c r lookup db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      step = S step' →
      e = expression_lexed_unary f e' →
      eval step' e' (c, r, lookup) (env, v) →
      eval_unary_expression f env v res →
      eval step e (c, r, lookup) res
.

Inductive eval_expr:
  config → relation_wrapped → expression → (eval_env * EResult) → Prop :=
  | EvalExpr: ∀ c r e env,
    eval 100 (lex e nil) (c, r, nil) env → eval_expr c r e env
.

(*
  This module needs some refactor because evaluating formula w.l.o.g. can be made as STLC.
  The environment for evaluation contains the policy, privacy parameter as well as the provenance context.

  There are two places where we need to evaluate the formula:
  1. For projections, we need to evaluate the formula to perform some transform on the data. 
*)

Inductive atomic_expression (ty: Tuple.tuple_type) : basic_type → Set :=
  (* v *)
  | atomic_expression_const:
      ∀ bt (c: type_to_coq_type bt), atomic_expression ty bt
  (* a *)
  | atomic_expression_column:
      ∀ n (extract: n < List.length ty), atomic_expression ty (Tuple.nth_np ty n extract)
  (* f(list e) *)
  | atomic_expression_func:
      ∀ bt (c: type_to_coq_type bt),
        transform_func bt → list (atomic_expression ty bt) → atomic_expression ty bt
.

Inductive agg_expression (ty: Tuple.tuple_type) (bt: basic_type): Set :=
  (* e *)
  | agg_atomic_expression: atomic_expression ty bt → agg_expression ty bt
  (* agg(e) *)
  | agg_aggregate: aggregate_func bt → atomic_expression ty bt → agg_expression ty bt
  (* f(A) *)
  | agg_function: transform_func bt → list (agg_expression ty bt)  → agg_expression ty bt
.

Inductive simple_atomic_expression: Set :=
  (* v *)
  | simple_atomic_expression_const:
      ∀ (bt: basic_type), type_to_coq_type bt → simple_atomic_expression
  (* a *)
  | simple_atomic_expression_column:
      ∀ (n: nat), simple_atomic_expression
  (*
    Without loss of generality, we assume functions only take either:
    1. One argument, or
    2. Two arguments (I am not sure if we really need this).

    This is because we can always transform a function with more than two arguments
    into a function with two arguments by *currying*.

    For example, we can transform `f(a, b, c)` into `f'(a, f''(b, c))`, although we
    do not actually do this in the code; we assume someone else has done this for us.

    There is, however, a problem with this approach: we need to know the type of the
    arguments and the return type.
  *)
  | simple_atomic_expression_func_unary:
      UnOp → simple_atomic_expression → simple_atomic_expression
  | simple_atomic_expression_func_binary:
      BinOp → simple_atomic_expression → simple_atomic_expression → simple_atomic_expression
  .

Definition stf_id := simple_atomic_expression_func_unary Identity.
Definition simple_agg_expression := (AggOp * agg_func * nat)%type.
Inductive predicate (ty: Tuple.tuple_type) (bt: basic_type): Type :=
  | predicate_true: predicate ty bt
  | predicate_false: predicate ty bt
  | predicate_com: ComOp → agg_expression ty bt → agg_expression ty bt→ predicate ty bt
  | predicate_not: predicate ty bt → predicate ty bt
.

Inductive simple_predicate: Set :=
  | simple_predicate_true: simple_predicate
  | simple_predicate_false: simple_predicate
  (* cell ? basic_type *)
  | simple_predicate_com: ComOp → simple_atomic_expression → simple_atomic_expression → simple_predicate
  | simple_predicate_not: simple_predicate → simple_predicate
.

Inductive formula (ty: Tuple.tuple_type) :=
  | formula_con: LogOp → formula ty → formula ty → formula ty
  | formula_predicate: ∀ bt, predicate ty bt → formula ty
.

Inductive simple_formula :=
  | simple_formula_con: LogOp → simple_formula → simple_formula → simple_formula
  | simple_formula_predicate: simple_predicate → simple_formula
.

Definition atomic_expression_denote (ty: Tuple.tuple_type) (t: basic_type) (a: atomic_expression ty t):
  Tuple.tuple ty → type_to_coq_type t.
Proof.
  refine (
    match a in atomic_expression _ t' return Tuple.tuple ty → type_to_coq_type t' with
      | atomic_expression_const _ _ v => fun _ => v
      | atomic_expression_column _ _ v  => fun x => _
      | atomic_expression_func _ _ _ f args => fun x => _
    end
  ).
  pose (Tuple.nth_col_tuple_np ty n v x).
  simpl in t0.
  exact (fst t0).
  exact t0.
Defined.

Fixpoint agg_denote (ty: Tuple.tuple_type) (t: basic_type) (a: agg_expression ty t):
  Tuple.tuple ty → type_to_coq_type t.
Proof.
  refine (
    match a in agg_expression _ _ return Tuple.tuple ty → type_to_coq_type _ with
      | agg_atomic_expression _ _ a => fun x => atomic_expression_denote ty t a x
      | agg_aggregate _ _ f a => fun x => _
      | agg_function _ _ f args => fun x => _
    end
  ).
  - exact (atomic_expression_denote ty t a x).
  - apply (List.map (fun arg => agg_denote ty t arg x)) in args.
    induction args.
    (* Should never happen? *)
    + destruct t.
      * simpl. exact 0.
      * simpl. exact false.
      * simpl. exact String.EmptyString.
    + exact IHargs.
Defined.

Fixpoint predicate_denote (bt: basic_type) (ty: Tuple.tuple_type) (p: predicate ty bt):
  Tuple.tuple ty → bool.
  intros. destruct p as [ | |op lhs rhs| ].
  - exact true.
  - exact false.
  - rename H into tp. destruct op.
  (* Determined by the operator type. *)
  (* Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.*)
  (* We are actually doing a match between `lt lhs rhs` and `com_op`. *)
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact false.
      * exact false.
      * exact true.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact true.
      * exact false.
      * exact false.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact false.
      * exact true.
      * exact true.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact true.
      * exact true.
      * exact false.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact false.
      * exact true.
      * exact false.
    + destruct (cmp (agg_denote ty bt lhs tp) (agg_denote ty bt rhs tp)).
      * exact true.
      * exact false.
      * exact true.
  - rename H into tp. exact (negb (predicate_denote bt ty p tp)).
Defined.
(* 
Fixpoint simple_predicate_denote (bt: basic_type) (p: simple_predicate bt): type_to_coq_type bt → bool.
  intros. destruct p.
  - exact true.
  - exact false.
  (* Inductive ComOp: Type := Gt | Lt | Ge | Le | Eq | Neq.*)
  - destruct c. destruct (cmp lhs rhs).
      * exact false.
      * exact false.
      * exact true.

      * exact true.
      * exact false.
      * exact false.

      * exact false.
      * exact true.
      * exact true.

      * exact true.
      * exact true.
      * exact false.

      * exact false.
      * exact true.
      * exact false.

      * exact true.
      * exact false.
      * exact true.
  - exact (negb (simple_predicate_denote bt p H)).
Defined. *)

Fixpoint formula_denote (ty: Tuple.tuple_type) (f: formula ty) {struct f}: Tuple.tuple ty → bool :=
match f with
  | formula_predicate _ c pred => predicate_denote c ty pred
  | formula_con _ op lhs rhs =>
    match op with
      | And => fun t => andb (formula_denote ty lhs t) (formula_denote ty rhs t)
      | Or => fun t => orb (formula_denote ty lhs t) (formula_denote ty rhs t)
    end
end.

Fixpoint bounded_list' (l: list simple_atomic_expression) (ty: Tuple.tuple_type) : Prop :=
  match l with
    | h :: t => match h with
                  | simple_atomic_expression_column n => n < List.length ty
                  | _ => True
                end ∧ bounded_list' t ty
    | _ => False
  end.

Require Import String.
Require Import List.
Require Import Lia.
(* Some tests. *)
Example example_formula: formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty BoolType (predicate_true Tuple.example_tuple_ty BoolType)).
Example example_formula': formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty IntegerType
      (predicate_com Tuple.example_tuple_ty IntegerType Eq
        (agg_atomic_expression Tuple.example_tuple_ty IntegerType
          (atomic_expression_const Tuple.example_tuple_ty IntegerType 1))
        (agg_atomic_expression Tuple.example_tuple_ty IntegerType
          (atomic_expression_const Tuple.example_tuple_ty IntegerType 1))
      )
    ).

Example can_index: 0 < List.length Tuple.example_tuple_ty.
Proof.
  simpl. lia.
Qed.
Example example_formula'': formula Tuple.example_tuple_ty :=
    (formula_predicate Tuple.example_tuple_ty StringType
      (predicate_com Tuple.example_tuple_ty StringType Eq
        (agg_atomic_expression Tuple.example_tuple_ty StringType
          (atomic_expression_column Tuple.example_tuple_ty 0 can_index))
        (agg_atomic_expression Tuple.example_tuple_ty StringType
          (atomic_expression_const Tuple.example_tuple_ty StringType "233"%string))
      )
    ).

(* fun _ : Tuple.tuple Tuple.example_tuple_ty => true *)
Compute ((formula_denote Tuple.example_tuple_ty example_formula) Tuple.example_tuple_lhs).
(* fun _ : Tuple.tuple Tuple.example_tuple_ty => false *)
Definition foo: bool := ((formula_denote Tuple.example_tuple_ty example_formula') Tuple.example_tuple_lhs).
Lemma foo_is_true: foo = true.
Proof.
  unfold foo.
  simpl.
  destruct (cmp 1 1).
  - apply order_is_irreflexive in l. contradiction.
  - destruct (nat_dec 1 1).
    destruct s. inversion l. inversion H0.
    reflexivity. inversion l.
    inversion H0.
  - apply order_is_irreflexive in l. contradiction.
Qed.

Definition foo': bool := ((formula_denote Tuple.example_tuple_ty example_formula'') Tuple.example_tuple_lhs).
Lemma foo'_is_false: foo' = false.
Proof.
  unfold foo'.
  simpl.
  destruct (nat_dec _ _).
  destruct s.
  - reflexivity.
  - inversion e.
  - reflexivity.
Qed.
