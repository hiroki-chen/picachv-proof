Require Import Arith.
Require Import Arith.Compare.
Require Import Lia.
Require Import List.
Require Import ListSet.
Require Import Logic.Eqdep_dec Logic.EqdepFacts.
Require Import String.
Require Import Unicode.Utf8.

Require Import config.
Require Import data_model.
Require Import finite_bags.
Require Import formula.
Require Import types.
Require Import lattice.
Require Import ordering.
Require Import prov.
Require Import relation.
Require Import util.

Inductive project_list: Set :=
  (* Denotes a "*" projection list. *)
  | project_star: project_list
  (*
    Dentoes a project list consisting function applications, column names, and constants.
    For example, if we have a schema `(IntegerType :: StringType :: BoolType :: nil)%type`,
    then the following project list is valid:
    ```
    (simple_atomic_expression_func stf_id
      (cons (simple_atomic_expression_column 0) nil)
    )
    ::
    (simple_atomic_expression_func stf_id
      (cons (simple_atomic_expression_column 1) nil)
    )
    ::
    (simple_atomic_expression_func stf_id
      (cons (simple_atomic_expression_column 2) nil)
    )
    ```

    Elements in the projection list will be added with an explicit column name.
  *)
  | project: list (simple_atomic_expression * string) → project_list
.
Hint Constructors project_list: core.

(*

  This function checks whether an expression is properly normalized. For an expression `expr`
  to be normalized, it must satisfy the following conditions:
  * If it is a function application, then either:
    - The function contains only one argument and the argument is a column name, or
    - The function contains more than one argument and all arguments are normalized.
  * If it is a column name, then it is not normalized (because no identity function is applied).
  * If it is a constant, then it is normalized.

  Normalization is just ensure that each column is applied with a function so that we can easily
  determine the basic type of the column as well as the label provenance of the column.
*)
Fixpoint normalized_expr (expr: simple_atomic_expression): Prop :=
  match expr with
  | simple_atomic_expression_column _ => False
  | simple_atomic_expression_const _ _ => True
  | simple_atomic_expression_func_unary _ expr' =>
      match expr' with
      | simple_atomic_expression_column _ => True
      | simple_atomic_expression_const _ _ => True
      | _ => normalized_expr expr'
      end
  | simple_atomic_expression_func_binary _ lhs rhs => normalized_expr lhs ∧ normalized_expr rhs
  end.

Definition normalized (pl: project_list): Prop :=
  match pl with
    | project_star => False
    | project ℓ =>
        (fix normalized' ℓ :=
          match ℓ with
          | nil => True
          | (h, _) :: t => normalized_expr h ∧ normalized' t
          end
        ) ℓ
  end.

(** 
  @param s The schema, which is a list of attributes.
  @param arg The simple atomic expression to evaluate.
  @return An optional basic type that represents the type of the evaluated expression.

  [bt_from_expr] is a function that takes a schema [s] and a simple atomic expression [arg], and returns an optional basic
  type that represents the type of the evaluated expression.

  The function works by pattern matching on the simple atomic expression [arg]. If [arg] is a column, it uses the [Tuple
  nth_nocheck] function to get the type of the column from the schema. If [arg] is a constant, it simply returns the type of
  the constant. If [arg] is a unary function, it recursively calls [determine_bt_from_expr] on the argument of the function.
  If [arg] is a binary function, it recursively calls [determine_bt_from_expr] on both arguments of the function and checks if
  their types match. If they do, it returns the type of the first argument. If they don't, it returns None.
*)
Fixpoint determine_bt_from_expr (s: schema) (arg: simple_atomic_expression): option basic_type :=
  match arg with
    | simple_atomic_expression_column c => Tuple.nth_nocheck (♭ s) c
    | simple_atomic_expression_const bt _ => Some bt
    | simple_atomic_expression_func_unary _ expr => determine_bt_from_expr s expr
    | simple_atomic_expression_func_binary _ lhs rhs =>
      match determine_bt_from_expr s lhs, determine_bt_from_expr s rhs with
      | Some ty1, Some ty2 =>
        if type_matches ty1 ty2 then Some ty1 else None
      | _, _ => None
      end
  end.

(*
  `determine_schema` is a function that takes a schema and a project list and returns a schema.
  This function calculates the output schema for the project operation given the input schema
  and the project list.

  * Note *
  This project list must be first normalized.

  For example, if we have a schema `(IntegerType :: StringType :: BoolType :: nil)%type` and
  a project list `(simple_atomic_expression_column 0) :: (simple_atomic_expression_column 2) :: nil`,
  then the result of `determine_schema` is `(IntegerType :: BoolType :: nil)%type`.
*)
Definition determine_schema (s: schema) (pl: project_list): schema :=
  match pl with
    | project_star => s
    | project ℓ =>
        (fix determine ℓ :=
          match ℓ with
          | nil => nil
          | (x, name) :: ℓ' => match x with
                        | simple_atomic_expression_column c => 
                          match Tuple.nth_nocheck (♭ s) c with
                              | Some bt => (bt, name) :: determine ℓ'
                              | None => determine ℓ'
                            end
                        | simple_atomic_expression_const bt _ => (bt, name) :: determine ℓ'
                        | simple_atomic_expression_func_unary _ expr =>
                          match determine_bt_from_expr s expr with
                            | Some ty => (ty, name) :: determine ℓ'
                            | None => determine ℓ'
                            end
                        | simple_atomic_expression_func_binary _ lhs rhs =>
                          match determine_bt_from_expr s lhs, determine_bt_from_expr s rhs with
                          | Some ty1, Some ty2 =>
                            if type_matches ty1 ty2 then (ty1, name) :: determine ℓ' else determine ℓ'
                          | _, _ => determine ℓ'
                          end
                      end
          end) ℓ
  end.

Lemma determine_schema_length_le: ∀ s pl,
  List.length (determine_schema s (project pl)) ≤ List.length pl.
Proof.
  induction pl.
  - auto.
  - apply Nat.lt_eq_cases in IHpl. destruct IHpl; destruct a.
    + destruct s0.
      * simpl in *. apply le_n_S. lia.
      * simpl in *. destruct (Tuple.nth_nocheck (♭ s) n); try lia; auto.
      * simpl in *. destruct (determine_bt_from_expr s s0); try lia; auto.
      * simpl in *.
        destruct (determine_bt_from_expr s s0_1); 
        destruct (determine_bt_from_expr s s0_2);
        try destruct (type_matches b0 b1); try lia; auto.
    + destruct s0.
      * simpl in *. lia.
      * simpl in *. destruct (Tuple.nth_nocheck (♭ s) n).
        -- simpl in *. apply le_n_S. lia.
        -- simpl in *. lia.
      * simpl in *. destruct (determine_bt_from_expr s s0).
        -- simpl in *. apply le_n_S. lia.
        -- simpl in *. lia.
      * simpl in *. destruct (determine_bt_from_expr s s0_1);
        destruct (determine_bt_from_expr s s0_2);
        try destruct (type_matches b0 b1); simpl in *; lia.
Qed.

Lemma determine_schema_nil: ∀ s,
  determine_schema s (project nil) = nil.
Proof.
  intros. simpl. auto.
Qed.

Lemma determine_schema_concat: ∀ s a ℓ,
  determine_schema s (project (a :: @nil (simple_atomic_expression * string))) ++
    determine_schema s (project ℓ) =
  determine_schema s (project (a :: ℓ)).
Proof.
  induction a; induction a; auto; intros.
  - simpl. destruct (Tuple.nth_nocheck (♭ s) n); auto.
  - simpl. destruct (determine_bt_from_expr s a); auto.
  - simpl. destruct (determine_bt_from_expr s a1);
           destruct (determine_bt_from_expr s a2);
           try destruct (type_matches b1 b2); auto.
Qed.

(** 
  @param s The schema, which is a list of tuples where each tuple contains a type and a name.
  @param n The starting index.
  @return A list of tuples. Each tuple contains a simple atomic expression and a string.

  [normalize_project_star] is a function that takes a schema [s] and a natural number [n], and returns a list of tuples. Each
  tuple contains a simple atomic expression and a string.

  The function works by iterating over the schema. For each attribute in the schema, it creates a new tuple. The first element of
  the tuple is a simple atomic expression that represents the attribute's column in the relation, and the second element is the
  attribute's name. The function uses the natural number [n] to keep track of the current column index. If the schema is empty,
  it returns an empty list.
*)
Fixpoint normalize_project_star (s: schema) (n: nat): list (simple_atomic_expression * string) :=
  match s with
    | nil => nil
    | (_, name) :: s' =>
      ((stf_id (simple_atomic_expression_column n)), name)
          :: normalize_project_star s' (S n)
  end.

(*
  @param e The simple atomic expression to normalize.
  @return The normalized simple atomic expression.

  [normalize_expr] is a function that takes a simple atomic expression [e] and returns a normalized version of it.

  The function works by pattern matching on the simple atomic expression [e]. If [e] is a column, it applies the Identity unary function to it. If [e] is a constant, it returns [e] as it is. If [e] is a unary function, it checks if the argument of the function is a column or a constant. If it is, it returns [e] as it is. If it's not, it recursively calls [normalize_expr] on the argument. If [e] is a binary function, it recursively calls [normalize_expr] on both arguments of the function.
*)
Fixpoint normalize_expr (e: simple_atomic_expression): simple_atomic_expression :=
  match e with
  | simple_atomic_expression_column c => 
        (stf_id (simple_atomic_expression_column c))
  | simple_atomic_expression_const _ _ => e
  | simple_atomic_expression_func_unary f arg =>
      match arg with
        | simple_atomic_expression_column _ => e
        | simple_atomic_expression_const _ _ => e
        | _ => simple_atomic_expression_func_unary f (normalize_expr arg)
      end
  | simple_atomic_expression_func_binary f arg1 args2 =>
      simple_atomic_expression_func_binary f (normalize_expr arg1) (normalize_expr args2)
  end.

(* 
  `normalize_project_list_list` is a function that takes a schema and a list of simple atomic
  expressions and returns a list of simple atomic expressions. The list of simple atomic
  expressions is the same length as the schema.

  This function converts from
  - column names to function applications of the identity function to the column name,
  - constants to constants, and
  - functions to functions (by normalizing all its arguments).

  We will later prove that this function preserves the semantics of the project operation.
*)
Fixpoint normalize_project_list_list
  (s: schema) (pl: list (simple_atomic_expression * string)): list (simple_atomic_expression * string) :=
  match pl with
    | nil => nil
    | (e, name) :: pl' =>
        let e' := (normalize_expr e) in (e', name) :: normalize_project_list_list s pl'
  end.

Lemma normalize_project_star_length: ∀ s n,
  List.length (normalize_project_star s n) = List.length s.
Proof.
  induction s.
  - auto.
  - intros. simpl. destruct a.
    specialize IHs with (n := S n). rewrite <- IHs. auto.
Qed.

Definition normalize_project_list (s: schema) (pl: project_list): project_list :=
  project
  (match pl with
    | project_star => normalize_project_star s 0
    | project ℓ => normalize_project_list_list s ℓ
  end).

Lemma normalize_preserve_length: ∀ s pl,
  List.length pl = List.length (normalize_project_list_list s pl).
Proof.
  induction s; induction pl; try destruct a; try destruct a0; simpl; auto with *.
Qed.

Example sample_schema: schema :=
  (IntegerType, "foo"%string) ::
    (IntegerType, "bar"%string) ::
      (IntegerType, "baz"%string) :: nil.
Compute normalize_project_list sample_schema project_star.
Compute normalize_project_list
  sample_schema
  (project
    (((simple_atomic_expression_func_unary Lower
      (simple_atomic_expression_column 0)
    ), "foo"%string) :: nil)).

Lemma normalize_star_normalized: ∀ s n, normalized (project (normalize_project_star s n)).
Proof.
  induction s.
  - simpl. auto.
  - intros. simpl.  destruct a.
    specialize IHs with (n := S n).
    simpl in IHs. auto. intuition. unfold normalized_expr. simpl. auto.
Qed.

Lemma normalized_cons: ∀ e pl, normalized (project (e :: pl)) →
  normalized_expr (fst e) ∧ normalized (project pl).
Proof.
  induction pl; destruct e.
  - simpl. auto.
  - intros. simpl in *. intuition.
Qed.

Lemma normalized_implies_each_expr: ∀ ℓ,
  normalized (project ℓ) →
  ∀ e, List.In e ℓ → normalized_expr (fst e).
Proof.
  induction ℓ.
  - intros. simpl in H0. inversion H0.
  - intros. simpl in H0. intuition; destruct a.
    + rewrite <- H1. simpl in H. intuition.
    + apply IHℓ; auto.
      simpl in H. intuition.
Qed.

Lemma normalized_list_cons: ∀ e ℓ,
  normalized_expr (fst e) → normalized (project ℓ) → normalized (project (e :: ℓ)).
Proof.
  induction ℓ; destruct e.
  - intros. simpl. auto.
  - intros; destruct a.
    apply normalized_cons in H0. intuition.
    simpl. intuition.
Qed.

Lemma normalized_list_list_cons: ∀ s pl e,
  normalized (project (normalize_project_list_list s (e :: pl))) →
  normalized (project (normalize_project_list_list s pl)).
Proof.
  induction pl; destruct e.
  - intros. simpl in *. auto.
  - intros. simpl in *. intuition.
Qed.

Lemma normalize_expr_is_normalized: ∀ e, normalized_expr (normalize_expr e).
Proof.
  intros. subst. induction e; simpl; auto.
  - induction e.
    + simpl. auto.
    + simpl. auto.
    + induction e.
      * simpl. auto.
      * simpl. auto.
      * intuition.
      * intuition.
    + induction e1; induction e2; intuition.
Qed.

Lemma normalize_is_normalized: ∀ s ℓ ℓ', ℓ' = (normalize_project_list s ℓ) → normalized ℓ'.
Proof.
  intros. subst. destruct ℓ.
  - apply normalize_star_normalized.
  - induction l.
    + simpl. auto.
    + simpl. destruct a.
      intuition. apply normalize_expr_is_normalized.
Qed.

(* Some helper lemmas for manipulating dependent types. *)
Section DtFacts.

Lemma tuple_single_eq: ∀ ty, Tuple.tuple (♭ (ty :: nil)) = (prod (prod (type_to_coq_type (fst ty)) nat) unit).
Proof.
  intros. simpl. auto.
  destruct ty.
  simpl.
  reflexivity.
Qed.

Lemma schema_const_ty_eq: ∀ expr ty c name s, expr = (simple_atomic_expression_const ty c, name) →
  (ty, name) :: nil = determine_schema s (project (expr :: nil)).
Proof.
  intros.
  destruct expr; inversion H; subst; intuition.
Qed.

Axiom nth_type_eq: ∀ s n (ok: n < List.length s) expr name, expr = simple_atomic_expression_column n →
  nth s n ok :: nil = determine_schema s (project ((expr, name) :: nil)).

(* By now, we can utilize `transport` or `eq_rect` to cast types: this is Leibniz equality. *)
Example makes_no_sense: ∀ ty (r: relation (ty :: nil)) (t: list (prod (prod (type_to_coq_type (fst ty)) nat) unit)),
  t = transport (tuple_single_eq ty) r.
Admitted.

End DtFacts.

(*
  @param s The schema, which is a list of tuples where each tuple contains a type and a name.
  @param op The unary operation to be applied.
  @param arg The simple atomic expression to evaluate.
  @param name The name of the attribute.
  @return A proposition that asserts the type of the evaluated expression remains the same when a
          unary function is applied.
=
  [unary_function_preserves_type] is a lemma that asserts that applying a unary function [op] to a
  simple atomic expression [arg] does not change the type of the evaluated expression. This is
  demonstrated by showing that the schema determined by projecting the evaluated expression with the
  unary function applied is the same as the schema determined by projecting the evaluated expression
  without the unary function applied.
*)
Lemma unary_function_preserves_type: ∀ s op arg name,
  (determine_schema s (project (
    (simple_atomic_expression_func_unary op arg, name) :: nil
  ))) =
  (determine_schema s (project (<< (arg); (name) >> :: nil))).
Proof.
  intros. simpl.
  destruct (determine_bt_from_expr s arg) eqn: Heq; destruct arg eqn: Harg.
  - inversion Heq. subst. reflexivity.
  - inversion Heq. subst. simpl in *.
    destruct (Tuple.nth_nocheck (♭ s)).
    + inversion Heq. subst. reflexivity.
    + inversion Heq.
  - destruct (determine_bt_from_expr s s0) eqn: Heq'.
    + simpl in *.
      assert (Some b = Some b0).
      {
        eapply trans_eq. symmetry in Heq. eauto. eauto.
      }
      inversion H. subst. reflexivity.
    + assert (Some b = None).
      {
        eapply trans_eq. symmetry in Heq. eauto. eauto.
      }
      inversion H.
  - inversion Heq.
    destruct (determine_bt_from_expr s s0_1) eqn: Heq1;
    destruct (determine_bt_from_expr s s0_2) eqn: Heq2.
    try destruct (type_matches b1 b2) eqn: Heq3; inversion H0.
    + apply type_matches_eq in Heq3. subst. inversion H0. reflexivity.
    + inversion H0.
    + inversion H0.
    + inversion H0.
  - inversion Heq.
  - inversion Heq. rewrite H0. reflexivity.
  - inversion Heq. rewrite H0. reflexivity.
  - inversion Heq.
    destruct (determine_bt_from_expr s s0_1) eqn: Heq1;
    destruct (determine_bt_from_expr s s0_2) eqn: Heq2;
    try destruct (type_matches b0 b1) eqn: Heq3; try inversion H0; reflexivity.
Defined.

Lemma unary_function_preserves_type': ∀ expr s op arg name,
  expr = (simple_atomic_expression_func_unary op arg, name) →
  (determine_schema s (project (expr :: nil))) =
  (determine_schema s (project (<< (arg); (name) >> :: nil))).
Proof.
  intros. subst. apply unary_function_preserves_type.
Qed.

Fixpoint determine_agg_schema (al: agg_list): schema.
  refine (
    match al with
      | nil => nil
      | (cur, name) :: tl => _
    end
  ).
Admitted.

Example determine_agg_schema_correct: determine_agg_schema
  ((((Count, (aggregate_function IntegerType IntegerType (fun x y => x + y)), 0)), "foo"%string) :: (((Count, (aggregate_function IntegerType IntegerType (fun x y => x + y)), 0)), "foo"%string) :: nil) =
  (IntegerType, "foo"%string) :: (IntegerType, "foo"%string) :: nil.
Proof. reflexivity. Qed.


Inductive operator: Type :=
  | operator_empty: operator
  (* `nat` means the index of the relation it wants to access inside `db`. *)
  | operator_relation: nat → operator
  | operator_union: operator → operator → operator
  | operator_join: operator → operator → operator
  | operator_project: project_list → operator → operator
  | operator_select: ∀ s, formula (♭ s) → operator → operator
  | operator_groupby_having: ∀ s, groupby_list → agg_list → formula s → operator → operator
.

(*
  @param s The schema, which is a list of tuples where each tuple contains a type and a name.
  @param n The length of the relation to be created.
  @param t The tuple to be repeated.
  @return A relation of length [n] where each tuple is [t].

  [tuple_of_length_n] returns a relation of length [n] where each tuple is [t]. The function
  works by recursively appending [t] to the relation until it reaches the desired length.
*)
Fixpoint tuple_of_length_n s (n: nat) (t: Tuple.tuple (♭ s)): relation s :=
match n with
  | O => nil
  | S n' => t :: tuple_of_length_n s n' t
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

(*
  @param bt The base type of the cell.
  @param f_type The type of the unary function.
  @param f The unary function to be applied.
  @param arg A tuple containing the cell value and its index.
  @param Γ The policy context.
  @param p The provenance context.
  @return An optional tuple containing the result of applying the unary function to the cell
          value, the updated policy context, and the updated provenance context.

  This function applies a unary function to a cell in a relation. If the unary function can
  be successfully applied, it returns a tuple containing the result of the function applica-
  tion, the updated policy context, and the updated provenance context. If the unary function
  cannot be applied (for example, if the function is not defined for the base type of the
  cell), the function returns `None`.
*)
Inductive apply_unary_function_in_cell bt:
  UnOp → unary_func → (type_to_coq_type bt * nat) → Policy.context → prov_ctx
       → option (type_to_coq_type bt * Policy.context * prov_ctx) → Prop :=
  | E_LabelNotFound: ∀ op f arg Γ p,
      label_lookup Γ (snd arg) = None ∨
      label_lookup p (snd arg) = None →
      apply_unary_function_in_cell bt op f arg Γ p None
  | E_PolicyErr: ∀ op f arg Γ p p_cur p_f,
      label_lookup Γ (snd arg) = Some p_cur →
      p_f = ∘ (Policy.policy_transform ((unary_trans_op op) :: nil)) →
      ¬ (p_cur ⪯ p_f) →
      apply_unary_function_in_cell bt op f arg Γ p None
  | E_PolicyOk: ∀ op f lambda arg Γ p p_cur prov_cur p_new prov_new ℓ p_f res Γ' p',
      label_lookup Γ (snd arg) = Some p_cur →
      label_lookup p (snd arg) = Some prov_cur →
      ℓ = (Policy.policy_transform ((unary_trans_op op) :: nil)) →
      p_f = (∘ ℓ) →
      p_cur ⪯ p_f →
      p_new = get_new_policy p_cur ℓ →
      prov_new = prov_list (prov_trans_unary op) ((snd arg, prov_cur) :: nil) →
      f = (unary_function bt lambda) →
      lambda (fst arg) = res →
      Γ' = update_label Γ (snd arg) p_new →
      p' = update_label p (snd arg) prov_new →
      apply_unary_function_in_cell bt op f arg Γ p (Some (res, Γ', p'))
.

(*
  @param ty An attribute containing a type and a name.
  @param r The relation, which is a list of tuples where each tuple contains a single type.
         Somehow we must calculate the type of `r`.
  @param Γ The policy context.
  @param p The proof context.
  @return An optional tuple containing the relation, the policy context, and the proof context.

  This function does the actual function application on a relation containing only one column on
  which the unary function should be applied.
*)
Inductive do_apply_unary_function (ty: Attribute) (r: relation (ty :: nil)):
  UnOp → unary_func → Policy.context → prov_ctx
       → option (relation (ty :: nil) * Policy.context * prov_ctx) → Prop :=
  | E_EmptyRelation: ∀ op f Γ p,
      r = nil →
      do_apply_unary_function ty r op f Γ p (Some (nil, Γ, p))
  | E_ApplyError: ∀ op f arg id tl Γ p,
      (tuple_single_eq ty) ♯ r = [[ (arg, id) ]] :: tl →
      apply_unary_function_in_cell (fst ty) op f (arg, id) Γ p None →
      do_apply_unary_function ty r op f Γ p None
   | E_ApplyErrorTail: ∀ op f arg id tl Γ p,
      (tuple_single_eq ty) ♯ r = [[ (arg, id) ]] :: tl →
      do_apply_unary_function ty (eq_sym (tuple_single_eq ty) ♯ tl) op f Γ p None →
      do_apply_unary_function ty r op f Γ p None
  | E_ApplyOk: ∀ op f arg id tl tl' Γ p ret Γ1 Γ2 p1 p2 res,
      (tuple_single_eq ty) ♯ r = [[ (arg, id) ]] :: tl →
      apply_unary_function_in_cell (fst ty) op f (arg, id) Γ p (Some (ret, Γ1, p1)) →
      (* Since this operation is sequential, we can just feed the updated env to cons. *)
      do_apply_unary_function ty (eq_sym (tuple_single_eq ty) ♯ tl) op f Γ1 p1 (Some (tl', Γ2, p2)) →
      res = (Some (eq_sym (tuple_single_eq ty) ♯ ([[ (ret, id) ]] ::
                  ((tuple_single_eq ty) ♯ tl')),
                  Γ2, p2)) →
      do_apply_unary_function ty r op f Γ p res
.

(*
  @param ty An attribute containing a type and a name.
  @param op The unary operation to be applied.
  @param ok A proof that the length of the schema [s] is 1.
  @param ctx A tuple containing the relation, the policy context, and the proof context.
  @return An optional tuple containing the relation, the policy context, and the proof context
          after applying the unary operation.

  [apply_unary_function_in_relation] is a function that takes a schema [s], a unary operation
  [op], a proof [ok] that the length of the schema is 1, and a context [ctx] that contains the
  relation, the policy context, and the proof context. It applies the unary operation [op] to
  the relation in the context and returns an optional tuple containing the updated relation,
  policy context, and proof context. If the operation cannot be applied, it returns None.

  This is just an entrypoint for the actual function [do_apply_unary_function].
*)
Inductive apply_unary_function_in_relation ty (r: relation (ty :: nil)):
  UnOp → Policy.context → prov_ctx → 
    option (relation (ty :: nil) * Policy.context * prov_ctx) → Prop :=
  | E_ApplyEmptyRelation: ∀ op Γ p,
      r = nil →
      apply_unary_function_in_relation ty r op Γ p None
  | E_ApplyIdentity: ∀ op r' tp tp_tl Γ Γ' p p',
      r = tp :: tp_tl →
      op = Identity →
      do_apply_unary_function ty r op (unary_function (fst ty) (fun x => x)) Γ p (Some (r', Γ', p')) →
      apply_unary_function_in_relation ty r op Γ p (Some (r', Γ', p'))
  (* Others are not defined. *)
.

(*
  @param s The schema of the relation.
  @param r The relation, which is a list of tuples where each tuple corresponds to a row in the relation.
  @param expr A tuple containing a simple atomic expression and a string. The simple atomic expression
              represents a column in the relation, and the string is the name of the column.
  @param Policy.context The policy context.
  @param prov_ctx The proof context.
  @return An optional tuple containing the relation, the policy context, and the proof context.
*)
Inductive apply_proj_elem s (r: relation s) (expr: simple_atomic_expression * string):
  Policy.context → prov_ctx →
    option (relation (determine_schema s (project (expr :: nil))) * basic_type * Policy.context * prov_ctx) → Prop :=
    (* We forbid directly reading from a column; this may violate the security policy. *)
  | E_ApplyColumn: ∀ Γ p n name
                  (case_column: expr = (simple_atomic_expression_column n, name)),

        apply_proj_elem s r expr Γ p None
    (* If we are doing projection of constants, we directly construct a column without any modification. *)
  | E_ApplyConst: ∀ Γ p ty val name res
                 (case_expr: expr = (simple_atomic_expression_const ty val, name)),

        let res_tmp := (tuple_of_length_n ((ty, name) :: nil) (List.length r) ((val, 0), tt)) in
          (* A transportation for type casting. *)
          res = (schema_const_ty_eq expr ty val name s case_expr ♯ res_tmp) →
          apply_proj_elem s r expr Γ p (Some (res, ty, Γ, p))
  | E_ApplyUnaryFunctionColumnError: ∀ Γ p op arg n name 
                          (case_expr: expr = (simple_atomic_expression_func_unary op arg, name)),

        arg = (simple_atomic_expression_column n) →
        n >= List.length s →
        apply_proj_elem s r expr Γ p None
  | E_ApplyUnaryFunctionColumnError2: ∀ Γ p op arg n (ok: n < List.length s) name tuples 
                          (case_expr: expr = (simple_atomic_expression_func_unary op arg, name))
                          (case_arg: arg = (simple_atomic_expression_column n)),
        tuples = extract_column s r n ok →
        apply_unary_function_in_relation _ tuples op Γ p None →
        apply_proj_elem s r expr Γ p None
  | E_ApplyUnaryFunctionColumnOk: ∀ Γ p op arg n (ok: n < List.length s) name tuples res_tmp res_tmp' res Γ' p'
                          (case_expr: expr = (simple_atomic_expression_func_unary op arg, name))
                          (case_arg: arg = (simple_atomic_expression_column n)),

        tuples = extract_column s r n ok →
        apply_unary_function_in_relation _ tuples op Γ p (Some (res_tmp, Γ', p')) →
        res_tmp' = (nth_type_eq s n ok arg name case_arg ♯ res_tmp) →
        (* Do a type casting. *)
        res = (eq_sym (unary_function_preserves_type' expr s op arg name case_expr) ♯ res_tmp') →
        apply_proj_elem s r expr Γ p (Some (res, (fst (nth s n ok)), Γ', p'))
  | E_ApplyUnaryFunctionOtherOk: ∀ Γ Γ' Γ'' p p' p'' op arg ty1 ty2 n name arg' res_tmp res
                            (case_expr: expr = (simple_atomic_expression_func_unary op arg, name))
                            (* We can prove this later. *)
                            (type_matches: determine_schema s (project (<< (arg); (name) >> :: nil)) = (ty1 :: nil)),
        arg ≠ (simple_atomic_expression_column n) →
        (* We first recursively evaluate the argument. *)
        apply_proj_elem s r (arg, name) Γ p (Some (arg', ty2, Γ', p')) →
        (fst ty1) = ty2 →
        (* Then we apply the unary function to the argument. *)
        apply_unary_function_in_relation _ (type_matches ♯ arg') op Γ' p' (Some (res_tmp, Γ'', p'')) →
        res = (eq_sym (unary_function_preserves_type' expr s op arg name case_expr) ♯ (eq_sym type_matches ♯ res_tmp)) →
        apply_proj_elem s r expr Γ p (Some (res, ty2, Γ'', p''))
  | E_ApplyUnaryFunctionOtherErr1: ∀ Γ p op arg n name
                            (case_expr: expr = (simple_atomic_expression_func_unary op arg, name)),
        arg ≠ (simple_atomic_expression_column n) →
        (* We first recursively evaluate the argument. *)
        apply_proj_elem s r (arg, name) Γ p None →
        apply_proj_elem s r expr Γ p None
  | E_ApplyUnaryFunctionOtherNoSchema: ∀ Γ p op arg n name
                            (case_expr: expr = (simple_atomic_expression_func_unary op arg, name)),
                            (* We can prove this later. *)
        determine_bt_from_expr s arg = None →
        arg ≠ (simple_atomic_expression_column n) →
        apply_proj_elem s r expr Γ p None
  | E_ApplyUnaryFunctionOtherErr2: ∀ Γ Γ' p p' op arg ty1 ty2 n name arg'
                            (case_expr: expr = (simple_atomic_expression_func_unary op arg, name))
                            (* We can prove this later. *)
                            (type_matches: determine_schema s (project (<< (arg); (name) >> :: nil)) = (ty1 :: nil)),
        arg ≠ (simple_atomic_expression_column n) →
        (* We first recursively evaluate the argument. *)
        apply_proj_elem s r (arg, name) Γ p (Some (arg', ty2, Γ', p')) →
        apply_unary_function_in_relation _ (type_matches ♯ arg') op Γ' p' None →
        apply_proj_elem s r expr Γ p None
  | E_ApplyUnaryFunctionOtherTypeMismatch: ∀ Γ Γ' p p' op arg ty1 ty2 n name arg'
                            (case_expr: expr = (simple_atomic_expression_func_unary op arg, name))
                            (* We can prove this later. *)
                            (type_matches: determine_schema s (project (<< (arg); (name) >> :: nil)) = (ty1 :: nil)),
        arg ≠ (simple_atomic_expression_column n) →
        (* We first recursively evaluate the argument. *)
        apply_proj_elem s r (arg, name) Γ p (Some (arg', ty2, Γ', p')) →
        (fst ty1) ≠ ty2 →
        apply_proj_elem s r expr Γ p None
  | E_Nonimplemented: ∀ Γ p op arg1 arg2 name
                     (case_expr: expr = (simple_atomic_expression_func_binary op arg1 arg2, name)),
      apply_proj_elem s r expr Γ p None
  .

(*
  @param s The schema of the relation.
  @param r The relation, which is a list of tuples where each tuple contains a single type.
  @param ℓ A list of simple atomic expressions and their corresponding string identifiers.
  @param Policy.context The policy context.
  @param prov_ctx The proof context.
  @return An optional tuple containing the relation, the policy context, and the proof context.

  This function applies a projection operation to a relation. The projection operation is specified by the list of
  simple atomic expressions `ℓ`. Each simple atomic expression in `ℓ` represents a column in the relation `r` that
  should be included in the result. The function returns an optional value. If the projection operation can be
  successfully applied, the function returns `Some` with a tuple containing the resulting relation, the updated
  policy context, and the updated proof context. If the projection operation cannot be applied (for example, if a
  simple atomic expression in `ℓ` does not correspond to a column in `r`), the function returns `None`.
*)
Inductive apply_proj_in_relation s (r: relation s) (ℓ: list (simple_atomic_expression * string)):
  Policy.context → prov_ctx → 
    option (relation (determine_schema s (project ℓ)) * Policy.context * prov_ctx) → Prop :=
  (* We do not accept lists that are not normalized. *)
  | E_Unnormalized: ∀ Γ p,
      ¬ (normalized (project ℓ)) →
      apply_proj_in_relation s r ℓ Γ p None
  | E_ApplyElemEmpty: ∀ Γ p,
      ℓ = nil ∨ r = nil →
      apply_proj_in_relation s r ℓ Γ p (Some (nil, Γ, p))
  | E_ApplyElemErrHead: ∀ Γ p hd tl (proj_case: ℓ = hd :: tl),
      r ≠ nil →
      apply_proj_elem s r hd Γ p None →
      apply_proj_in_relation s r ℓ Γ p None
  | E_ApplyElemErrTail: ∀ hd hd' Γ Γ' p p' tl (proj_case: ℓ = hd :: tl),
      r ≠ nil →
      apply_proj_elem s r hd Γ p (Some (hd', Γ', p')) →
      apply_proj_in_relation s r tl Γ' p' None →
      apply_proj_in_relation s r ℓ Γ p None
  | E_ApplyElemOk: ∀ Γ Γ' Γ'' p p' p'' hd hd' tl tl' col
                (proj_case: ℓ = hd :: tl),
      r ≠ nil →
      apply_proj_elem s r hd Γ p (Some (hd', Γ', p')) →
      apply_proj_in_relation s r tl Γ' p' (Some (tl', Γ'', p'')) →
      (*
        Goal:
        (determine_schema s (project (hd :: nil)) ++
        determine_schema s (project tl)) = determine_schema s (project ℓ)
        -------------------------------
        project ℓ = project (hd :: tl) by ℓ = hd :: tl with ♯
        --–----------------------------
        Then by determine_schema_concat we have:
        (determine_schema s (project (hd :: nil)) ++
        determine_schema s (project tl)) = determine_schema s (project (hd :: tl))
        -------------------------------
      *)
      let col_tmp := (relation_product _ _ (fst hd') tl') in
        let col_proxy := ((determine_schema_concat s hd tl) ♯ col_tmp) in
          col = ((eq_sym proj_case) ♯ col_proxy) →
          apply_proj_in_relation s r ℓ Γ p (Some (col, Γ'', p''))
.

Lemma apply_unary_function_in_relation_terminate: ∀ s r op Γ p,
  ∃ res, apply_unary_function_in_relation s r op Γ p res.
Proof.
Admitted.

Lemma apply_proj_elem_terminate: ∀ s r expr Γ p, ∃ res,
  apply_proj_elem s r expr Γ p res.
Proof.
  intros s r expr.
  refine (
    match expr with
    | (exp, name) =>
        (*
          The trick is to split the tuple into just its left part to pass the termination checker.

          This is because reducing *only* the left part of the tuple will not convince Coq that
          the function will terminate; but we do not use the right part, so we just throw it away
          and do not use it as a principle argument of recursion. 
        *)
        (fix proof e :=
          match e as e' return e = e' → _ with 
            | simple_atomic_expression_const ty val => _
            | simple_atomic_expression_column n => _
            | _ => _
          end eq_refl) exp
    end); intros.
  - pose (res := (schema_const_ty_eq (simple_atomic_expression_const ty val, name) ty val name s eq_refl ♯
      tuple_of_length_n (<< (ty); (name) >> :: nil) (Datatypes.length r) (val, 0, tt))).
    subst. exists (Some (res, ty, Γ, p)).

    eapply E_ApplyConst with (val := val) (name := name) (case_expr := eq_refl); eauto.
  - exists None. eapply E_ApplyColumn; eauto.
  - specialize proof with (e := s0) (Γ := Γ) (p := p).
    destruct proof.
    destruct x.
    + (* Some *)
      destruct p0 as [ [ [ r' ty ] Γ'] p'].
      destruct s0.
      * destruct (apply_unary_function_in_relation_terminate _ (eq_refl ♯ r') u Γ' p').
       (* destructing the nested evaluation. *)
       destruct x.
       -- (* Some *)
         destruct p0 as [ [ r'' Γ'' ] p''].
         destruct (basic_type_eq_dec ty bt).
         ++ simpl in *. specialize E_ApplyUnaryFunctionOtherOk with
                (expr := (simple_atomic_expression_func_unary u (simple_atomic_expression_const bt t), name))
                (case_expr := eq_refl)
                (ty1 := (bt, name))
                (ty2 := ty)
                (n := 0)
                (res_tmp := r'').
            intros.
            exists (Some (((eq_sym (unary_function_preserves_type' 
              (simple_atomic_expression_func_unary u (simple_atomic_expression_const bt t), name) s u
                (simple_atomic_expression_const bt t) name eq_refl) ♯ (eq_sym eq_refl ♯ r''))),
                  ty, Γ'', p'')).
            eapply H2; eauto.
            ** red. intros. discriminate.
            ** simpl in *. auto.

        ++ (* Type mismatch! *)
          exists None. eapply E_ApplyUnaryFunctionOtherTypeMismatch with (ty1 := (bt, name)) (n := 0); eauto.
          red. intros. discriminate.
      -- (* None *)
          exists None. eapply E_ApplyUnaryFunctionOtherErr2 with (n := 0); eauto.
          red. intros. discriminate.
      * (* This happens when the inner argument is a column type. *)
         destruct (lt_dec n (List.length s)) as [ok | not_ok]. 
         -- pose (tuple := extract_column s r n ok).
            destruct (apply_unary_function_in_relation_terminate _ tuple u Γ p).
            destruct x as [ [ [res_tmp Γ_tmp ] p_tmp ] | ].
            ++ (* Some *)
               pose ((nth_type_eq s n ok (simple_atomic_expression_column n) name eq_refl) ♯ res_tmp) as res_tmp'.
               pose (eq_sym (unary_function_preserves_type' (simple_atomic_expression_func_unary u (simple_atomic_expression_column n), name) s u (simple_atomic_expression_column n) name eq_refl) ♯ res_tmp') as res.
               exists (Some (res, (fst (nth s n ok)), Γ_tmp, p_tmp)).
               eapply E_ApplyUnaryFunctionColumnOk with (tuples := tuple) (n := n) (arg := simple_atomic_expression_column n)(ok := ok) (res_tmp := res_tmp) (res_tmp' := res_tmp') (case_arg := eq_refl) (case_expr := eq_refl); eauto.
            ++ exists None. eapply E_ApplyUnaryFunctionColumnError2 with (n := n); eauto.
          -- exists None. eapply E_ApplyUnaryFunctionColumnError with (n := n); eauto. lia.
      * 
      (* Let us again use dependent pattern matching. *)
        refine (
          match determine_bt_from_expr s s0 as t return t = determine_bt_from_expr s s0 -> _ with
            | None => _
            | Some ty => _
          end eq_refl
        ); intros.
        -- assert (<< ty ; name >> :: nil = determine_schema s (
              project (<< (simple_atomic_expression_func_unary u 
                (simple_atomic_expression_func_unary u0 s0)); (name) >> :: nil))).
          {
            simpl. rewrite <- H1. reflexivity.
          }
          (* Now this tactic type-checks. *)
          destruct (apply_unary_function_in_relation_terminate _ (eq_sym H2 ♯ r') u Γ' p').
          destruct x as [ [ [res_tmp Γ_tmp ] p_tmp ] | ].
          ++ (* Transport the type to make Coq happy. *)
            destruct (basic_type_eq_dec ty ty0).
            (* Π (A: U) Π (a b: A) (a = b) → P (a) -> P(b) *)
            ** exists (Some ((eq_sym (unary_function_preserves_type'
                  (simple_atomic_expression_func_unary u (simple_atomic_expression_func_unary u0 s0), name) s u
                    (simple_atomic_expression_func_unary u0 s0) name eq_refl) ♯ (H2 ♯ res_tmp)),
                      ty, Γ_tmp, p_tmp)).
             eapply E_ApplyUnaryFunctionOtherOk with (n := 0) (case_expr := eq_refl); eauto.
              --- red. intros. discriminate.
              --- subst. auto.
              --- auto.
              --- rewrite eq_sym_involutive. auto.
           ** exists None. eapply E_ApplyUnaryFunctionOtherTypeMismatch; eauto. instantiate (1 := 0).
              red. intros. discriminate.
          ++ exists None. eapply E_ApplyUnaryFunctionOtherErr2 with (n := 0); eauto.
              red. intros. discriminate.
        -- exists None. eapply E_ApplyUnaryFunctionOtherNoSchema with (n := 0); eauto.
           red. intros. discriminate.
      * refine (
          match determine_bt_from_expr s s0_1 as ty1', determine_bt_from_expr s s0_2 as ty2'
            return determine_bt_from_expr s s0_1 = ty1' → determine_bt_from_expr s s0_2 = ty2' → _
          with
          | Some ty1, Some ty2 =>
            match type_matches ty1 ty2 as bt return type_matches ty1 ty2 = bt → _ with
            | true => _
            | false => _
            end eq_refl
          | _, _ => _
          end eq_refl eq_refl
        ); intros.
        -- assert (determine_schema s (project ((simple_atomic_expression_func_binary b s0_1 s0_2, name) :: nil)) = << ty1 ; name >> :: nil).
        {
          simpl. rewrite H2. rewrite H3. rewrite H1. reflexivity.
        }
        destruct (apply_unary_function_in_relation_terminate _ (H4 ♯ r') u Γ' p').
        destruct x as [ [ [res_tmp Γ_tmp ] p_tmp ] | ].
          ++ destruct (basic_type_eq_dec ty ty1).
            ** exists (Some ((eq_sym (unary_function_preserves_type'
                  (simple_atomic_expression_func_unary u (simple_atomic_expression_func_binary b s0_1 s0_2), name) s u
                    ((simple_atomic_expression_func_binary b s0_1 s0_2)) name eq_refl) ♯ (eq_sym H4 ♯ res_tmp)),
                      ty, Γ_tmp, p_tmp)).
               eapply E_ApplyUnaryFunctionOtherOk with (n := 0) (case_expr := eq_refl); eauto.
               --- red. intros. discriminate.
               --- subst. auto.
            ** exists None. eapply E_ApplyUnaryFunctionOtherTypeMismatch; eauto. instantiate (1 := 0).
               red. intros. discriminate.
         ++ exists None. eapply E_ApplyUnaryFunctionOtherErr2 with (n := 0); eauto.
              red. intros. discriminate.
        -- exists None. eapply E_ApplyUnaryFunctionOtherNoSchema; eauto. 
           simpl. rewrite H2. rewrite H3. rewrite H1. reflexivity. instantiate (1 := 0).
           red. intros. discriminate.
        -- exists None. eapply E_ApplyUnaryFunctionOtherNoSchema; eauto. 
           simpl. rewrite H2. rewrite H1. reflexivity. instantiate (1 := 0).
           red. intros. discriminate.
        -- exists None. eapply E_ApplyUnaryFunctionOtherNoSchema; eauto. 
           simpl. rewrite H1. reflexivity. instantiate (1 := 0).
           red. intros. discriminate.
    + (* None *)
      destruct s0.
      * exists None. eapply E_ApplyUnaryFunctionOtherErr1; eauto. simpl.
        instantiate (1 := 0). red. intros. discriminate.
      * (* `apply_proj_elem` has nothing to do with f(c); we just need to dicuss this case alone. *)
        destruct (lt_dec n (List.length s)) as [ok | not_ok].
        -- pose (tuple := extract_column s r n ok).
           destruct (apply_unary_function_in_relation_terminate _ tuple u Γ p).
           destruct x as [ [ [res_tmp Γ_tmp ] p_tmp ] | ].
           ++ pose ((nth_type_eq s n ok (simple_atomic_expression_column n) name eq_refl) ♯ res_tmp) as res_tmp'.
               pose (eq_sym (unary_function_preserves_type' (simple_atomic_expression_func_unary u (simple_atomic_expression_column n), name) s u (simple_atomic_expression_column n) name eq_refl) ♯ res_tmp') as res.
               exists (Some (res, (fst (nth s n ok)), Γ_tmp, p_tmp)).
               eapply E_ApplyUnaryFunctionColumnOk with (tuples := tuple) (n := n) (arg := simple_atomic_expression_column n)(ok := ok) (res_tmp := res_tmp) (res_tmp' := res_tmp') (case_arg := eq_refl) (case_expr := eq_refl); eauto.
            ++ exists None. eapply E_ApplyUnaryFunctionColumnError2 with (n := n); eauto.
        -- exists None. eapply E_ApplyUnaryFunctionColumnError with (n := n); eauto. lia.
      * exists None. eapply E_ApplyUnaryFunctionOtherErr1; eauto. simpl.
        instantiate (1 := 0). red. intros. discriminate.
      * exists None. eapply E_ApplyUnaryFunctionOtherErr1; eauto. simpl.
        instantiate (1 := 0). red. intros. discriminate.
  - exists None. apply E_Nonimplemented with (op := b) (arg1 := s0) (arg2 := s1) (name := name); eauto.
Qed.

Lemma apply_proj_in_relation_terminate: ∀ s r ℓ Γ p,
  ∃ res, apply_proj_in_relation s r ℓ Γ p res.
Proof.
  intros s r.
  destruct r.
  - intros. exists (Some (nil, Γ, p)). econstructor; eauto.
  - refine (
    fix proof ℓ Γ p :=
      (*
        Interestingly `induction n eqn: H` tactic messes up the dependent variables;
        we instead use refine to do the induction.
      *)
      match ℓ as ℓ' return ℓ = ℓ' → _ with
      | nil => fun _ => _
      | hd :: tl => fun _ => _
      end eq_refl
  ).
    + exists (Some (nil, Γ, p)). econstructor; eauto.
    + destruct (apply_proj_elem_terminate s (t :: r) hd Γ p).
      destruct x as [ [ [r' Γ'] p' ] |] eqn: Hx1.
      * specialize proof with (ℓ := tl) (Γ := Γ') (p := p').
        destruct proof.
        destruct x0 as [ [ [r'' Γ''] p''] |] eqn: Hx2.
        -- pose (col := (eq_sym eq_refl ♯
                        (determine_schema_concat s hd tl ♯
                          relation_product (determine_schema s (project (hd :: nil)))
                              (determine_schema s (project tl)) (fst r') r''))).
          exists (Some (col, Γ'', p'')).
          specialize E_ApplyElemOk with (r := (t :: r)) (ℓ := ℓ) (hd := hd) (tl := tl) (hd' := r') (tl' := r'') (Γ := Γ) (Γ' := Γ') (Γ'' := Γ'') (p := p) (p' := p') (p'' := p'') (proj_case := e).
          intros. subst.
          eapply H1; eauto. red. intros. discriminate.
        -- exists None. eapply E_ApplyElemErrTail; eauto. red. intros. discriminate.
      * exists None. eapply E_ApplyElemErrHead; eauto. red. intros. discriminate.
Qed.

Lemma apply_proj_elem_deterministic: ∀ s r expr Γ p res1 res2,
  apply_proj_elem s r expr Γ p res1 →
  apply_proj_elem s r expr Γ p res2 →
  res1 = res2.
Proof.
Admitted.

Lemma apply_proj_in_relation_deterministic: ∀ s r ℓ Γ p res1 res2,
  normalized (project ℓ) →
  apply_proj_in_relation s r ℓ Γ p res1 →
  apply_proj_in_relation s r ℓ Γ p res2 →
  res1 = res2.
Proof.
  induction ℓ; intros; inversion H0; subst; try contradiction; try discriminate.
  - inversion H1; subst; try contradiction; try discriminate; auto.
  - subst. intuition.
    + discriminate.
    + subst. inversion H1; subst; try contradiction. intuition.
  - inversion H1; subst; try contradiction; try discriminate; auto.
    intuition. discriminate.
    inversion proj_case. subst. inversion proj_case0. subst.
    eapply apply_proj_elem_deterministic with (res1 := None) in H5; try assumption.
    discriminate.
  - inversion proj_case. subst.
    inversion H1; subst; intuition; try discriminate; try contradiction.
    inversion proj_case0. subst.
    eapply apply_proj_elem_deterministic with (res1 := (Some (hd', Γ', p'))) in H6; try assumption.
    inversion H6; subst.
    specialize IHℓ with (Γ := Γ'0) (p := p'0).
    assert (None = (Some (tl', Γ'', p''))).
    {
      apply IHℓ. apply normalized_cons in H. destruct H. assumption. assumption. assumption.
    }
    discriminate.
  - inversion proj_case. subst.
    inversion H1; subst; intuition; try discriminate; try contradiction.
    inversion proj_case0. subst.
    eapply apply_proj_elem_deterministic with (res1 := (Some (hd', Γ', p'))) in H6; try assumption.
    inversion H6; subst.
    inversion proj_case0. subst.
    eapply apply_proj_elem_deterministic with (res1 := (Some (hd', Γ', p'))) in H6; try assumption.
    inversion H6; subst.  
    + specialize IHℓ with (Γ := Γ'0) (p := p'0).
      assert (None = (Some (tl', Γ'', p''))).
      {
        apply IHℓ. apply normalized_cons in H. destruct H. assumption. assumption. assumption.
      }
      discriminate.
    + inversion proj_case0. subst.
      eapply apply_proj_elem_deterministic with (res1 := (Some (hd', Γ', p'))) in H6; try assumption.
      inversion H6; subst.
      specialize IHℓ with (Γ := Γ'0) (p := p'0).
      assert ((Some (tl'0, Γ''0, p''0)) = (Some (tl', Γ'', p''))).
      {
        apply IHℓ. apply normalized_cons in H. destruct H. assumption. assumption. assumption.
      }
      inversion H8. subst.
      (* 
          We need to leverage Streicher'K theorem in the intensional MLTT version so that we
          can derive the fact that all equality proofs are essentially identical, i.e.,

          ∀ (A: U) ∀ (a b: A) (p q: a = b) → p = q

          This holds only if equality is decidable for type A, so that A degrades into a set.
          For non-sets that manifest complex high-order groupoid structures, adding K as an
          axiom will break univalance axiom in HoTT.

          Thus there is a paper discussing pattern matching without K in IFCP'14.

          Cockx, Jesper, Dominique Devriese, and Frank Piessens. "Pattern matching without K."
          In Proceedings of the 19th ACM SIGPLAN international conference on Functional programming. 2014.
      *)
      repeat f_equal. apply Eqdep.EqdepTheory.UIP.
Qed.

(*
  @param s The schema of the relation.
  @param Policy.context The policy context.
  @param budget The budget for the evaluation.
  @param prov_ctx The provenance context.
  @param formula The formula to be evaluated.
  @param relation The relation in which the formula is to be evaluated.
  @param returns option A tuple containing the resulting relation, the updated policy context, the remaining
                       budget, and the updated provenance context.

  The `eval_expr_in_relation` inductive type represents the evaluation of a formula in a relation. The evalua-
  tion is performed in the context of a given policy context and provenance context, and it may consume certain
  amount of budget. If the evaluation is successful, the function returns `Some` with a tuple containing the
  resulting relation, the updated policy context, the remaining budget, and the updated provenance context. If
  the evaluation is not successful (for example, if the budget is exhausted), the function returns `None`.

  FIXME: Will selection consume budget?
*)
Inductive eval_expr_in_relation:
  ∀ s, Policy.context → budget → prov_ctx → formula (♭ s) → relation s →
    option (relation s * Policy.context * budget * prov_ctx) → Prop :=
  | E_EvalExprRelationNil: ∀ s Γ β p f r,
      r = nil →
      eval_expr_in_relation s Γ β p f r (Some (nil, Γ, β, p))
  | E_EvalExprConsTrue: ∀ s Γ Γ' β β' p p' f f_denote r hd tl tl',
      r = hd :: tl →
      f_denote = formula_denote (♭ s) f →
      eval_expr_in_relation s Γ β p f tl (Some (tl', Γ', β', p')) →
      f_denote hd = true →
      eval_expr_in_relation s Γ β p f r (Some (hd :: tl', Γ', β', p'))
  | E_EvalExprConsFalse: ∀ s Γ Γ' β β' p p' f f_denote r hd tl tl',
      r = hd :: tl →
      f_denote = formula_denote (♭ s) f →
      eval_expr_in_relation s Γ β p f tl (Some (tl', Γ', β', p')) →
      f_denote hd = false →
      eval_expr_in_relation s Γ β p f r (Some (tl', Γ', β', p'))
.

Lemma eval_expr_in_relation_terminate: ∀ s Γ β p f r, ∃ res,
  eval_expr_in_relation s Γ β p f r res.
Proof.
  intros.
  induction r.
  - exists (Some (nil, Γ, β, p)). econstructor; eauto.
  - destruct IHr. destruct x.
    + (* Some *)
      destruct p0 as [ [ [tl Γ'] β'] p' ].
      destruct (formula_denote (♭ s) f a) eqn: Hdenote.
      * exists (Some (a :: tl, Γ', β', p')). econstructor; eauto.
      * exists (Some (tl, Γ', β', p')). econstructor; eauto.
    + (* None *)
      inversion H.
Qed.

(* This first creates for each tuple a `groupby_proxy` which can later be `gathered` for our convenience. *)
Definition get_group_proxy_helper s (r: relation s) (gb_keys: groupby_list) (bounded: bounded_list s gb_keys):
  list (groupby_proxy (ntypes s gb_keys bounded)) :=
  let gb_keys_extracted := (extract_columns s r gb_keys bounded) in
    (fix create_group_proxy keys n :=
      match keys with
      | nil => nil
      | hd :: tl => (hd, (n :: nil)) :: (create_group_proxy tl (S n))
      end
    ) gb_keys_extracted 0.

(* This function does the actual job by "gathering" all groups together. *)
(* TODO: Perhaps we also need to take provenance into consideration? *)
Definition get_group_proxy s (r: relation s) (gb_keys: groupby_list) (bounded: bounded_list s gb_keys):
  list (groupby_proxy (ntypes s gb_keys bounded)).
  pose (intermediate_gb_proxy := get_group_proxy_helper s r gb_keys bounded).
  induction intermediate_gb_proxy.
  - exact nil.
  - rename IHintermediate_gb_proxy into rest.
    (*
       For each of the element `a` in the intermediate result, we need to check if this can be "found"
       in this rest. If yes, we need to merge it into the rest and then return the merged one. If not,
       we need to remain as is.
     *)
     pose (gather := fix gather (elem: groupby_proxy (ntypes s gb_keys bounded))
                      (proxy: list (groupby_proxy (ntypes s gb_keys bounded))) :=
       match proxy with
       | nil => elem :: nil
       | hd :: tl => 
          let (key , indices) := hd in
          let (key', indices') := elem in
          if (Tuple.tuple_value_eqb _ key key') then
            (key, indices ++ indices') :: (gather elem tl)
          else
            hd :: (gather elem tl)
       end
     ).

     exact (gather a rest).
Defined.

(*
  @param s The type of the elements in the resulting relation.
  @param s_gb The type of the elements in the groupby_proxy list; the `groupby` keys because they are dependent types.
  @param Policy.context The policy context.
  @param budget The budget for the operation.
  @param prov_ctx The provenance context.
  @param list (groupby_proxy s_gb) The list of groupby_proxy elements.
  @param agg_list The list of aggregation operations to be applied.
  @param relation s The initial relation.
  @param option (relation s * Policy.context * budget * prov_ctx) The expected result of the operation.
  @returns Prop A proposition that is true if the operation is correctly applied, false otherwise.

  The `apply_fold_on_groups` inductive type represents the application of a list of aggregation operations on a list of `groupby_proxy` elements. The operation is performed in the context of a given policy context and provenance context,
  and it may consume a certain amount of budget. If the operation is successful, the function returns `Some` with a tuple
  containing the resulting relation, the updated policy context, the remaining budget, and the updated provenance context.
*)
Inductive apply_fold_on_groups:
  ∀ s s_gb agg, Policy.context → budget → prov_ctx → list (groupby_proxy s_gb)  → relation s →
    option (relation (s ++ determine_agg_schema agg) * Policy.context * budget * prov_ctx) → Prop :=
.

Inductive eval_aggregate:
  ∀ s agg, Policy.context → budget → prov_ctx → groupby_list  → relation s →
    option (relation (s ++ determine_agg_schema agg) * Policy.context * budget * prov_ctx) → Prop :=
  | E_EvalAggregateNotBounded: ∀ s Γ β p gb_list agg r,
      ¬ bounded_list s gb_list →
      eval_aggregate s agg Γ β p gb_list r None
  | E_EvalAggregateError: ∀ s Γ β p gb_list (bounded: bounded_list s gb_list)
                       gb_proxy agg r,
      get_group_proxy s r gb_list bounded = gb_proxy →
      apply_fold_on_groups s _ agg Γ β p gb_proxy r None →
      eval_aggregate s agg Γ β p gb_list r None
  | E_EvalAggregateOk: ∀ s Γ Γ' β β' p p' gb_list (bounded: bounded_list s gb_list)
                    gb_proxy agg r r',
      get_group_proxy s r gb_list bounded = gb_proxy →
      apply_fold_on_groups s _ agg Γ β p gb_proxy r (Some (r', Γ', β', p')) →
      eval_aggregate s agg Γ β p gb_list r (Some (r', Γ', β', p'))
.

(* 
  `step_config` is an inductive type representing the transition rules for configurations. 
  It defines how a configuration changes from one state to another by the query.

  If an update is successfully performed, then we need to:
  * Update the environment.
  * Update the policy environment.
  * Update the privacy budget.
  * Update the cell in the tuple.
  * Update the tuple in the environment.
  * Update the relation.
*)
Reserved Notation "'⟦' c op '⟧' '⇓' '⟦' c' '⟧'"
  (at level 10, c at next level, op at next level, c' at next level).
Inductive step_config: (config * operator) → config → Prop :=
  | E_Already: ∀ c c' o r,
      c = config_output r c' →
      ⟦ c o ⟧ ⇓ ⟦ c ⟧
  | E_ErrorState: ∀ o,
      ⟦ config_error o ⟧ ⇓ ⟦ config_error ⟧
  (* Empty operator returns nothing and does not affect the configuration. *)
  | E_Empty: ∀ c c' db Γ β p,
      c = ⟨ db Γ β p ⟩ →
      c' = config_output (relation_output nil nil) c →
      ⟦ (⟨ db Γ β p ⟩) operator_empty ⟧ ⇓ ⟦ c' ⟧
  (* Getting the relation is an identity operation w.r.t. configurations. *)
  | E_GetRelation: ∀ c c' db o n r Γ Γ' β p p',
      db ≠ database_empty →
      o = operator_relation n →
      c = ⟨ db Γ β p ⟩ →
      database_get_contexts db n = Some (r, Γ', p') →
      c' = config_output r (⟨ db Γ' β p' ⟩) →
      ⟦ c (operator_relation n) ⟧ ⇓ ⟦ c' ⟧
  (* The given relation index is not found in the database. *)
  | E_GetRelationError: ∀ c c' db o n Γ β p,
      db ≠ database_empty →
      o = operator_relation n →
      c = ⟨ db Γ β p ⟩ →
      database_get_contexts db n = None →
      c' = config_error →
      ⟦ c (operator_relation n) ⟧ ⇓ ⟦ c' ⟧
  (* Database is empty! *)
  | E_GetRelationDbEmpty: ∀ c c' db Γ β p o n,
      db = database_empty →
      o = operator_relation n →
      c = ⟨ db Γ β p ⟩ →
      c' = config_error →
      ⟦ c (operator_relation n) ⟧ ⇓ ⟦ c' ⟧
  (* If the operator returns an empty relation, we do nothing. *)
  | E_ProjEmpty: ∀ c c' db db' Γ Γ' β β' p p' s r o pl,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ → 
      c' = config_output (relation_output s r) (⟨ db' Γ' β' p' ⟩) →
      r = nil ∨ s = nil →
      ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ c' ⟧
  (* If the operator returns a valid relation, we can then apply projection. *)
  | E_ProjOk: ∀ c c' c'' db db' pl pl' s'
                Γ Γ' Γ'' β β' p p' p'' r' r'' o,
      c = ⟨ db Γ β p ⟩ →
      (* We first evaluate the inner operator and get the output. *)
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      (* We then destruct the output. *)
      c' = config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩) →
      s' ≠ nil ∧ r' ≠ nil →
      (* `pl'` means a normalized project list. *)
        normalize_project_list s' pl = project pl' →
        (* We then apply projection inside the environment. *)
        apply_proj_in_relation _ r' pl' Γ p (Some (r'', Γ'', p'')) →
        c'' = config_output (relation_output _ r'') (⟨ db' Γ'' β' p'' ⟩) →
        ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ c'' ⟧
  (*
     If the operator returns a valid environment, we can then apply projection. Then if the
     projection fails, we return `config_error`.
  *)
  | E_ProjError: ∀ c c' db db' pl pl' s'
                Γ Γ' β β' p p' r' o,
      c = ⟨ db Γ β p ⟩ →
      (* We first evaluate the inner operator and get the output. *)
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      (* We then destruct the output. *)
      c' = config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩) →
      s' ≠ nil ∧ r' ≠ nil →
      (* `pl'` means a normalized project list. *)
      normalize_project_list s' pl = project pl' →
        (* We then apply projection inside the environment. *)
        apply_proj_in_relation _ r' pl' Γ p None →
        ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ config_error ⟧
      (*
     If the operator returns a valid environment, we can then apply projection. Then if the
     projection fails, we return `config_error`.
  *)
  | E_ProjError2: ∀ c db Γ β p pl o,
      c = ⟨ db Γ β p ⟩ →
      (* We first evaluate the inner operator and get the output. *)
      ⟦ c o ⟧ ⇓ ⟦ config_error ⟧ →
      ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectError: ∀ c c' db db' Γ Γ' β β' p p' s' r' o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩) →
      eval_expr_in_relation s' Γ' β' p' expr r' None →
      ⟦ c (operator_select s' expr o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectError2: ∀ c db Γ β p s o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ config_error ⟧ →
      ⟦ c (operator_select s expr o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectError3: ∀ c c' db db' Γ Γ' β β' p p' s1 s2 r' o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s2 r') (⟨ db' Γ' β' p' ⟩) →
      s1 ≠ s2 →
      ⟦ c (operator_select s1 expr o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectOk: ∀ c c' c'' db db' Γ Γ' Γ'' β β' β'' p p' p'' s' r' r'' o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩) →
      eval_expr_in_relation s' Γ' β' p' expr r' (Some (r'', Γ'', β'', p'')) →
      c'' = config_output (relation_output s' r'') (⟨ db' Γ'' β'' p'' ⟩) →
      ⟦ c (operator_select s' expr o)⟧ ⇓ ⟦ c'' ⟧
  | E_UnionError: ∀ c c' c'' db Γ β p o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c' = config_error ∨ c'' = config_error →
      ⟦ c (operator_union o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_UnionSchemaError: ∀ c c' c'' db db' db'' Γ Γ' Γ'' β β' β'' p p' p'' s1 s2 r' r'' o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      s1 ≠ s2 →
      ⟦ c (operator_union o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_UnionOk: ∀ c c' c'' db db' db'' Γ Γ' Γ'' β β' β'' p p' p'' s r' r'' o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (relation_output s r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      (*
        We ensure that cells are always assigned new ids;
        so it is safe for us to just append them together.
      *)
      let merged_p := merge_env p' p'' in
        let merged_Γ := merge_env Γ' Γ'' in
          let merged_β := calculate_budget β' β'' in
          (* TODO: How to deal with privacy budget? *)
          ⟦ c (operator_union o1 o2) ⟧ ⇓
          ⟦ config_output (relation_output s (r' ++ r'')) (⟨ db'' merged_Γ merged_β merged_p ⟩) ⟧
  | E_JoinError: ∀ c c' c'' db Γ β p o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c' = config_error ∨ c'' = config_error →
      ⟦ c (operator_join o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_JoinError2: ∀ c c' c'' db db' db'' Γ Γ' Γ'' β β' β'' p p' p'' s1 s2 r' r'' o1 o2,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      let join_by := (natural_join_list s1 s2) in
        (relation_join_by_prv s1 s2 join_by r' r'' Γ' Γ'' β' β'' p' p'')
        None →
        ⟦ c (operator_join o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_JoinOk: ∀ c c' c'' db db' db'' Γ Γ' Γ'' Γout β β' β'' βout p p' p'' pout s1 s2 r' r'' r rout o1 o2,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      let join_by := (natural_join_list s1 s2) in
        (relation_join_by_prv s1 s2 join_by r' r'' Γ' Γ'' β' β'' p' p'')
        (Some (rout, Γout, βout, pout))→
        r = relation_output _ rout →
        ⟦ c (operator_join o1 o2) ⟧ ⇓
        (* TODO: Should join. *)
        ⟦ config_output r (⟨ db'' Γout βout pout ⟩) ⟧
  | E_AggEmpty: ∀ c c' db Γ β p o s r gl al f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s r) c' →
      s = nil ∨ r = nil →
      ⟦ c (operator_groupby_having (♭ s) gl al f o) ⟧ ⇓ ⟦ c' ⟧
  | E_AggError: ∀ c db Γ β p o s gl al f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ config_error ⟧ →
      ⟦ c (operator_groupby_having (♭ s) gl al f o) ⟧ ⇓ ⟦ config_error ⟧
  | E_AggError2: ∀ s c c' db db' Γ Γ' β β' p p' o r gl al f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s r) (⟨ db' Γ' β' p' ⟩) →
      s ≠ nil ∧ r ≠ nil →
      eval_aggregate s al Γ' β' p' gl r None →
      ⟦ c (operator_groupby_having (♭ s) gl al f o) ⟧ ⇓ ⟦ config_error ⟧
  | E_AggOk: ∀ c c' c'' db db' Γ Γ' β β' p p' s al r r' o gl f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (relation_output s r) (⟨ db' Γ' β' p' ⟩) →
      s ≠ nil ∧ r ≠ nil →
      eval_aggregate s al Γ' β' p' gl r (Some (r', Γ', β', p')) →
      c'' = config_output (relation_output _ r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c (operator_groupby_having (♭ s) gl al f o) ⟧ ⇓ ⟦ c'' ⟧
where "'⟦' c op '⟧' '⇓' '⟦' c' '⟧'" := (step_config (c, op) c').
Hint Constructors step_config: core.

(* For Hongbo: can you help me prove this theorem? *)
Theorem operator_deterministic: ∀ c o c1 c2, 
  ⟦ c o ⟧ ⇓ ⟦ c1 ⟧ →
  ⟦ c o ⟧ ⇓ ⟦ c2 ⟧ →
  c1 = c2.
Proof.
  induction o; intros.
  - inversion H0; inversion H; subst; auto; try discriminate.
    inversion H5. subst. reflexivity.
  - inversion H0; inversion H; subst; auto; try discriminate.
    + inversion H13. subst. rewrite H14 in H6. inversion H6. subst. reflexivity.
    + inversion H13. subst. rewrite H14 in H6. inversion H6.
    + inversion H13. subst. discriminate.
    + inversion H13. subst. rewrite H14 in H6. inversion H6.
    + inversion H12. subst. discriminate.
  - destruct c1; destruct c2.
    + reflexivity.
    + inversion H0; subst; try discriminate.
    + inversion H; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * destruct H7; subst.
        -- inversion H0; subst.
           specialize IHo1 with (c1 := (config_output (relation_output s r') (⟨ db' Γ' β' p' ⟩))) (c2 := config_error).
           apply IHo1 in H9.
           ++ discriminate.
           ++ assumption.
        -- inversion H0; subst.
           specialize IHo2 with (c1 := config_error) (c2 := (config_output (relation_output s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
           apply IHo2 in H11.
           ++ discriminate.
           ++ assumption.
      * inversion H0; subst; try discriminate.
        inversion H8. subst.
        (* The contradiction occurs when s1 ≠ s2 where s = s1 ∧ s = s2. *)
        specialize IHo1 with (c1 := (config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩)))
                             (c2 := (config_output (relation_output s r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩))).
        specialize IHo2 with (c1 := (config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩)))
                             (c2 := (config_output (relation_output s r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩))).
        apply IHo2 in H7. inversion H7. subst.
        apply IHo1 in H5. inversion H5. subst.
        -- exfalso. apply H9. reflexivity.
        -- assumption.
        -- assumption.
    + inversion H; subst; try discriminate.
    + inversion H0; subst; try discriminate.
    + inversion H; subst; try discriminate.
    + inversion H0; subst; try discriminate.
      * inversion H; subst; try discriminate.
      * destruct H7; subst.
        -- inversion H; subst; try discriminate.
           specialize IHo1 with (c1 := (config_output (relation_output s r') (⟨ db' Γ' β' p' ⟩))) (c2 := config_error).
           apply IHo1 in H9.
           ++ discriminate.
           ++ assumption.
        -- inversion H; subst.
           specialize IHo2 with (c1 := config_error) (c2 := (config_output (relation_output s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
           apply IHo2 in H11.
           ++ discriminate.
           ++ assumption.
      * inversion H; subst; try discriminate.
        inversion H8. subst.
        (* The contradiction occurs when s1 ≠ s2 where s = s1 ∧ s = s2. *)
        specialize IHo1 with (c1 := (config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩)))
                             (c2 := (config_output (relation_output s r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩))).
        specialize IHo2 with (c1 := (config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩)))
                             (c2 := (config_output (relation_output s r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩))).
        apply IHo2 in H7. inversion H7. subst.
        apply IHo1 in H5. inversion H5. subst.
        -- exfalso. apply H9. reflexivity.
        -- assumption.
        -- assumption.
    + inversion H0; subst; try discriminate.
    + inversion H; inversion H0; subst; try discriminate.
      * inversion H8. subst. inversion H4. subst. assumption.
      * inversion H16. subst.
        specialize IHo2 with (c1 := (config_output (relation_output s0 r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩)))
                             (c2 := (config_output (relation_output s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
        specialize IHo1 with (c1 := (config_output (relation_output s0 r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩)))
                             (c2 := (config_output (relation_output s r') (⟨ db' Γ' β' p' ⟩))).
        intuition. inversion H3. inversion H1. subst.
        (*
          Now we have some weird equality over dependent types:
                    existT P p a = existT P p b
                    ^^^^^: ∀ [A : Type] (P : A → Type) (x : A), P x → {x : A & P x}
        
           The reason for that is that the index `s` appears on the types of `a`
           and `b` cannot be generalized when typing the equality `a = b` which
           is required for `inversion` tactic.
           
           `existT` is the constructor for the dependent pair type, which "hides"
           the index and allows Coq to avoid this problem in the general case,
           producing a statement which is slightly similar.

           `inj_pair2_eq_dec` is a lemma that allows us to `inversion` equality of
            dependent pairs given that the index is decidable.
         *)

        apply inj_pair2_eq_dec in H5, H13; subst; try reflexivity;
        apply list_eq_dec; apply attribute_eq_dec.
  - inversion H0; inversion H; subst; try discriminate; auto.
    + intuition; subst.
      * apply (IHo1 config_error) in H13. discriminate. assumption.
      * apply (IHo2 config_error) in H15. discriminate. assumption.
    + inversion H14. subst. clear H14.
      apply (IHo1 (config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩))) in H15.
      apply (IHo2 (config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H17.
      inversion H15. inversion H17. subst.
      apply inj_pair2_eq_dec in H3, H12; subst. 
      * eapply relation_join_by_prv_deterministic with (res2 := None) in H20.
        inversion H20. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
    + intuition; inversion H15; subst.
      * apply (IHo1 config_error) in H5. discriminate. assumption.
      * apply (IHo2 config_error) in H7. discriminate. assumption.
    + inversion H15. subst. clear H15.
      apply (IHo1 (config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩))) in H16.
      apply (IHo2 (config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H18.
      inversion H16. inversion H18. subst.
      apply inj_pair2_eq_dec in H3, H12; subst. 
      * eapply relation_join_by_prv_deterministic with (res2 := None) in H10.
        inversion H10. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
    + apply (IHo1 (config_output (relation_output s1 r') (⟨ db' Γ' β' p' ⟩))) in H16.
      apply (IHo2 (config_output (relation_output s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H18.
      inversion H15. inversion H18. inversion H16. subst.
      apply inj_pair2_eq_dec in H9, H19. subst.
      eapply relation_join_by_prv_deterministic with (res2 := (Some (rout, Γout, βout, pout))) in H21.
      * inversion H21. subst. reflexivity.
      * assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
  - inversion H0; inversion H; subst; intuition; auto; subst; try discriminate.
    + inversion H12. subst. clear H12.
      apply (IHo (config_output (relation_output s nil) (⟨ db' Γ' β' p' ⟩))) in H13.
      inversion H13. subst. apply inj_pair2_eq_dec in H6. subst.
      * inversion H18; subst. exfalso. apply H2. auto. exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + inversion H12. subst. clear H12.
      apply (IHo (config_output (relation_output nil r) (⟨ db' Γ' β' p' ⟩))) in H13.
      inversion H13. subst. apply inj_pair2_eq_dec in H6. subst. clear H13.
      inversion H18; subst. intuition.
      * exfalso. apply H1. auto.
      * exfalso. apply H1. auto.
      * assumption.
    + inversion H12. subst. clear H12.
      apply (IHo (config_output (relation_output s nil) (⟨ db' Γ' β' p' ⟩))) in H13.
      inversion H13. subst.  apply inj_pair2_eq_dec in H6. subst. clear H13.
      * exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + inversion H12. subst. clear H12.
      apply (IHo (config_output (relation_output nil r) (⟨ db' Γ' β' p' ⟩))) in H13; try assumption.
      inversion H13. subst. apply inj_pair2_eq_dec in H6; subst; clear H13;
      try (apply list_eq_dec; apply attribute_eq_dec).
      exfalso. apply H1. auto.
    + inversion H15. subst. clear H15.
      apply (IHo (config_output (relation_output s nil) (⟨ db'0 Γ'0 β'0 p'0 ⟩))) in H5; try assumption.
      inversion H5. subst. apply inj_pair2_eq_dec in H6. subst. clear H5.
      * exfalso. apply H2. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
    + inversion H15. subst. clear H15.
      apply (IHo (config_output (relation_output nil r) (⟨ db'0 Γ'0 β'0 p'0 ⟩))) in H5.
      inversion H5. subst. apply inj_pair2_eq_dec in H6. subst. clear H5.
      * exfalso. apply H1. auto.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + inversion H15. subst. clear H15.
      apply (IHo (config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩))) in H16.
      inversion H16. subst. apply inj_pair2_eq_dec in H9. subst. clear H16.
      * inversion H10. inversion H23. subst. inversion H14. inversion H24. subst.
        clear H14. clear H24.
        inversion H15; subst.
        rewrite H8 in H21. inversion H21. subst. intuition; subst.
        -- eapply apply_proj_in_relation_deterministic with (res1 := Some (r'1, Γ''0, p''0)) in H15.
          ++ inversion H15. subst. reflexivity.
          ++ assumption.
          ++ assumption.
        -- inversion H15; subst; intuition.
          ++ discriminate.
          ++ rewrite H8 in H21. inversion H21. subst.
             inversion proj_case. subst. 
             eapply apply_proj_in_relation_deterministic with (res1 := (Some (r'1, Γ''0, p''0))) in H15.
            ** inversion H15. subst. auto.
            ** assumption.
            ** assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      (* Similar proof. *)
    + inversion H17. subst. clear H17.
      apply (IHo (config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩))) in H18.
      inversion H18. subst. apply inj_pair2_eq_dec in H9. subst. clear H18.
      * inversion H24. inversion H7. subst. clear H7.
        inversion H9. subst.
        -- contradiction.
        -- rewrite H8 in H21. inversion H21. subst.
           (* Seems to be stuck on the induction case. *)
           inversion H10. inversion H18. subst. clear H18.
           eapply apply_proj_in_relation_deterministic with (res1 := None) in H19.
           ++ discriminate.
           ++ assumption.
           ++ assumption.
        -- rewrite H8 in H21. inversion H21; subst.
           inversion H10. inversion H19. subst. clear H19.
           eapply apply_proj_in_relation_deterministic with (res1 := None) in H20.
           ++ discriminate.
           ++ assumption.
           ++ assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply (IHo config_error) in H5. discriminate. assumption.
    + (*For this case, the proof looks similar. *)
      inversion H15. subst. clear H15.
      apply (IHo (config_output (relation_output s nil) (⟨ db'0 Γ'0 β'0 p'0 ⟩))) in H5.
      inversion H5. subst. apply inj_pair2_eq_dec in H6. subst. clear H5.
      * inversion H11. subst. inversion H4. subst. clear H4. inversion H5.
        -- contradiction.
        -- subst. exfalso. apply H4. auto.
        -- subst. exfalso. apply H4. auto.
      * apply inj_pair2_eq_dec in H6. subst. clear H5.
        apply list_eq_dec; apply attribute_eq_dec.
        apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + inversion H15. subst. clear H15.
      apply (IHo (config_output (relation_output nil r) (⟨ db'0 Γ'0 β'0 p'0 ⟩))) in H5.
      inversion H5. subst. apply inj_pair2_eq_dec in H6. subst. clear H5.
      * inversion H11. subst. inversion H4. subst. clear H4. inversion H5.
        -- contradiction.
        -- subst. exfalso. apply H1. auto.
        -- exfalso. apply H1. auto.
      * apply inj_pair2_eq_dec in H6. subst. clear H5.
        apply list_eq_dec; apply attribute_eq_dec.
        apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + inversion H15. subst. clear H15.
      apply (IHo (config_output (relation_output s' r') (⟨ db' Γ' β' p' ⟩))) in H16.
      inversion H16. subst. apply inj_pair2_eq_dec in H9. subst. 
      rewrite H8 in H19. inversion H19. subst. clear H19.
      * inversion H11. inversion H21. inversion H7. inversion H20. subst.
        clear H7. clear H20.
        apply apply_proj_in_relation_deterministic with (res1 := None) in H22.
        -- discriminate.
        -- assumption.
        -- assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
    + apply (IHo config_error) in H11. discriminate. assumption.
  - (* TODO: Proof for `select`. *)
Admitted.
 
(* This theorem ensures the "sanity" of the semantics to ensure that operators won't get stuck.
  For Hongbo: also can you finish the remaining part?
 *)
Theorem operator_always_terminate: ∀ c o, c ≠ config_error → ∃ c', ⟦ c o ⟧ ⇓ ⟦ c' ⟧.
Proof.
  induction o; unfold not; intros; destruct c.
  - exfalso. auto.
  - (* Although we don't need `s`, we need to introduce this term into the context. *)
    pose (s := @nil Attribute).
    exists (config_output (relation_output nil nil) (⟨ d c b p ⟩)).
    econstructor; reflexivity.
  - pose (s := @nil Attribute). exists (config_output r c).
    eapply E_Already with (r := r) (c := (config_output r c)) (c' := c). reflexivity.
  - exfalso. auto.
  - destruct d eqn: Hdb.
    + exists config_error. eapply E_GetRelationDbEmpty with (o := operator_relation n); reflexivity.
    + destruct (database_get_contexts d n) as [ [ [ r' Γ' ] p' ] | ] eqn: Hget.
      * exists (config_output r' (⟨ d Γ' b p' ⟩)).
        eapply E_GetRelation with (db := d) (o := operator_relation n) (Γ := c) (β := b) (p := p).
        -- red. intros. subst. inversion H0.
        -- reflexivity.
        -- subst. reflexivity.
        -- eapply Hget.
        -- reflexivity.
      * exists config_error.
        eapply E_GetRelationError with (db := d) (o := operator_relation n) (Γ := c) (β := b) (p := p).
        -- red. intros. subst. inversion H0.
        -- reflexivity.
        -- subst. reflexivity.
        -- assumption.
        -- reflexivity.
  - pose (s := @nil Attribute). exists (config_output r c).
    eapply E_Already with (r := r) (c := (config_output r c)) (c' := c). reflexivity.
  - contradiction.
  - (* We now introduce the existential variables into the context. *)
    intuition. destruct H0. destruct H1.
    destruct x; destruct x0.
    + exists config_error. econstructor; try eauto.
    + exists config_error. econstructor; try eauto.
    + exists config_error. econstructor; try eauto.
    + exists config_error. econstructor; try eauto.
    + inversion H0; subst; try discriminate.
    + inversion H0; subst; try discriminate.
    + exists config_error. econstructor; try eauto.
    + inversion H1; subst; try discriminate.
    + destruct r, r0, x, x0; subst.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H1; subst; try discriminate.
      * destruct (list_eq_dec (attribute_eq_dec) s0 s).
        -- subst.
          pose (merged_p := merge_env p0 p1).
          pose (merged_Γ := merge_env c0 c1).
          pose (merged_β := calculate_budget b0 b1).
          exists (config_output (relation_output s (r ++ r0)) (⟨ d1 merged_Γ merged_β merged_p ⟩)).
          econstructor; try reflexivity; eauto.
        -- exists config_error. eapply E_UnionSchemaError with (s1 := s) (s2 := s0); try eauto.
      * (* There should be no rule for constructing nested output. *)
        inversion H1; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H1; subst; try discriminate.
  - exists (config_output r c). eapply E_Already; reflexivity.
  - exists config_error. eapply E_ErrorState.
  - destruct IHo1; destruct IHo2; intuition.
    destruct x; destruct x0.
    + exists config_error. econstructor; try eauto.
    + exists config_error. econstructor; try eauto.
    + exists config_error. econstructor; try eauto.
    + exists config_error. econstructor; try eauto.
    + inversion H0; subst; try discriminate.
    + inversion H0; subst; try discriminate.
    + exists config_error; econstructor; try eauto.
    + inversion H1; subst; try discriminate.
    + destruct r; destruct r0; destruct x; destruct x0; subst.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H1; subst; try discriminate.
      * 
        (* TODO: prove that this relation is decidable.  *)
        destruct (relation_join_by_prv_terminate s s0 (natural_join_list s s0) r r0 c0 c1 b0 b1 p0 p1).
        destruct x as[ [ [ [rjoin cjoin ] bjoin] pjoin] |].
        -- (* x = Some *)
          pose (rout := relation_output _ rjoin).
          exists (config_output rout (⟨ d1 cjoin bjoin pjoin ⟩)).
          econstructor; eauto.
        -- exists config_error. eapply E_JoinError2; eauto.
      * inversion H1; subst; try discriminate.
      * inversion H1; subst; try discriminate.
      * inversion H0; subst; try discriminate.
      * inversion H0; subst; try discriminate.
  - exists (config_output r c). eapply E_Already; reflexivity.
  - intuition.
  - intuition. destruct H0. clear H.
    destruct x.
    + exists config_error. eapply E_ProjError2; eauto.
    + inversion H0; subst; try discriminate.
    + destruct r. destruct (normalize_project_list s p) as [|pl] eqn: Hpl.
      * inversion Hpl.
      * destruct x.
        -- inversion H0; subst; try discriminate.
        -- destruct (apply_proj_in_env_terminate s (r, nil, nil, nil) pl c p0).
           eapply normalize_is_normalized. symmetry. eauto.
           destruct s eqn: Hs; destruct r eqn: Hr.
           ++ exists (config_output (relation_output nil nil) (⟨ d0 c0 b0 p1 ⟩)).
                 eapply E_ProjEmpty; eauto.
           ++ exists (config_output (relation_output nil r) (⟨ d0 c0 b0 p1 ⟩)).
                 eapply E_ProjEmpty; subst; eauto.
           ++ exists (config_output (relation_output s nil) (⟨ d0 c0 b0 p1 ⟩)).
                 eapply E_ProjEmpty; subst; eauto.
           ++ destruct x as [ [ [e' Γ''] p'']|].
              ** pose (r'' := env_get_relation _ e').
                 pose (c'' := config_output (relation_output _ r'') (⟨ d0 Γ'' b0 p'' ⟩)).
              exists c''. eapply E_ProjOk; eauto; try reflexivity.
              split; red; intros; try discriminate.
           ** exists config_error. eapply E_ProjError; eauto. split; intuition; discriminate.
        -- inversion H0; subst; try discriminate.
  - intuition. exists (config_output r c). eapply E_Already; eauto.
  - contradiction.
  - intuition. destruct H0. clear H.
    destruct x.
    + exists config_error. eapply E_SelectError2; eauto.
    + inversion H0; subst; try discriminate.
    + destruct r; destruct x.
      * inversion H0; subst; try discriminate.
      * destruct (list_eq_dec (attribute_eq_dec) s s0).
        -- subst. destruct (eval_expr_in_relation_terminate _ c0 b0 p0 f r).
           destruct x as [ [ [ [ r' c'] b' ] p'] | ].
           ++ (* Some. *)
              exists (config_output (relation_output _ r') (⟨ d0 c' b' p' ⟩)).
              eapply E_SelectOk; eauto; try reflexivity.
           ++ exists config_error. eapply E_SelectError; eauto.
        -- exists config_error. eapply E_SelectError3; eauto.
      * inversion H0; subst; try discriminate.
  - intuition. exists (config_output r c). eapply E_Already; eauto.
  - contradiction.
  - intuition.
  (* TODO: operator_groupby_having *)
Admitted.

Example simple_project_list := project ((simple_atomic_expression_column 0, "foo"%string) :: nil).
Example simple_project_list_res := normalize_project_list sample_schema simple_project_list.
Example simple_project_list_res_correct : simple_project_list_res = project ((simple_atomic_expression_func_unary Identity (simple_atomic_expression_column 0), "foo"%string) :: @nil (simple_atomic_expression * string)).
Proof.
  reflexivity.
Qed.

Example simple_project_list' := project (
  (stf_id (simple_atomic_expression_column 0), "foo"%string) ::
  (stf_id (simple_atomic_expression_column 1), "bar"%string) ::
  (stf_id (simple_atomic_expression_column 2), "baz"%string) ::
  nil
).

Example simple_project_list_res' := normalize_project_list sample_schema simple_project_list'.
Example simple_project_list_res_correct' : simple_project_list_res' = simple_project_list_res'.
Proof.
  reflexivity.
Qed.
