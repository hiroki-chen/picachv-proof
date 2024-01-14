Require Import Arith.
Require Import Arith.Compare.
Require Import Lia.
Require Import List.
Require Import ListSet.
Require Import String.
Require Import Unicode.Utf8.

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
    | simple_atomic_expression_column c => Tuple.nth_nocheck (schema_to_no_name s) c
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
                          match Tuple.nth_nocheck (schema_to_no_name s) c with
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

Lemma extract_column_type_eq: ∀ s expr n (ok: n < List.length s) name,
  expr = (simple_atomic_expression_column n) →
  (nth s n ok :: nil) = determine_schema s (project ((expr, name) :: nil)).
Admitted.

Lemma determine_schema_length_le: ∀ s pl,
  List.length (determine_schema s (project pl)) ≤ List.length pl.
Proof.
  induction pl.
  - auto.
  - apply Nat.lt_eq_cases in IHpl. destruct IHpl; destruct a.
    + destruct s0.
      * simpl in *. apply le_n_S. lia.
      * simpl in *. destruct (Tuple.nth_nocheck (schema_to_no_name s) n); try lia; auto.
      * simpl in *. destruct (determine_bt_from_expr s s0); try lia; auto.
      * simpl in *.
        destruct (determine_bt_from_expr s s0_1); 
        destruct (determine_bt_from_expr s s0_2);
        try destruct (type_matches b0 b1); try lia; auto.
    + destruct s0.
      * simpl in *. lia.
      * simpl in *. destruct (Tuple.nth_nocheck (schema_to_no_name s) n).
        -- simpl in *. apply le_n_S. lia.
        -- simpl in *. lia.
      * simpl in *. destruct (determine_bt_from_expr s s0).
        -- simpl in *. apply le_n_S. lia.
        -- simpl in *. lia.
      * simpl in *. destruct (determine_bt_from_expr s s0_1);
        destruct (determine_bt_from_expr s s0_2);
        try destruct (type_matches b0 b1); simpl in *; lia.
Qed.

Lemma determine_schema_concat: ∀ s a ℓ,
  determine_schema s (project (a :: @nil (simple_atomic_expression * string))) ++
    determine_schema s (project ℓ) =
  determine_schema s (project (a :: ℓ)).
Proof.
  induction a; induction a; auto; intros.
  - simpl. destruct (Tuple.nth_nocheck (schema_to_no_name s) n); auto.
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

Lemma tuple_single_eq: ∀ ty, Tuple.tuple (schema_to_no_name (ty :: nil)) = (prod (prod (type_to_coq_type (fst ty)) nat) unit).
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
    destruct (Tuple.nth_nocheck (schema_to_no_name s)).
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

Definition groupby_list := (list nat)%type.
Definition agg_list s := (list (∀ bt, agg_expression s bt))%type.

(* Do we really need `list nat` to represent the lists? *)
Definition env_slice s := (relation s * list nat * groupby_list * list (Tuple.tuple (schema_to_no_name s)))%type.

(*
  `env` is a definition for an environment in a given schema `s`. 
  It is a list of tuples, where each tuple consists of a relation, 
  a list of 'selected' attributes, a groupby list, and a list of tuples.

  - The relation is a list of tuples of type `Tuple.tuple s` for determing the concrete relation
    that is used for the expression evaluation.
  - The selected attributes is a list of natural numbers, which are the indices of the attributes
    in the schema that are used for the expression evaluation.
  - The groupby list is a list of natural numbers, which are the indices of the attributes in the
    schema that are used for grouping.
  - The list of tuples is a list of tuples of type `Tuple.tuple s`.

  This environment is used in the context of database query operations.

  Note that this is a dependent type (heterogeneous list). This is because we need to know the schema
  of each active relation, but the schema of each relation is different. Consider this case:

  ```
  a: (IntegerType :: StringType :: nil)%type
  b: (IntegerType :: BoolType :: nil)%type
  ```

  We now have a `join` operator:

  ```
  join a b
  ```

  After `a` and `b` are evaluated, we have two relations of different schemas.
*)
Fixpoint ℰ (s: list schema) : Type :=
  match s with
    | nil => unit
    | s :: s' => (env_slice s * ℰ s')%type
  end.

Definition fuse_env {s1 s2} (e1: ℰ s1) (e2: ℰ s2) : ℰ (s1 ++ s2).
  induction s1.
  - simpl. exact e2.
  - simpl. destruct e1 as [es1 e1]. exact (es1, IHs1 e1).
Defined.

Definition lift_env_slice s (es: env_slice s) : ℰ (s :: nil).
  exact (es, tt).
Defined.

(* =============================== Some utility functions =================================== *)
Definition get_env_slice s (e: ℰ s) (non_empty: List.length s > 0) : env_slice (hd_ok s non_empty).
  destruct s; simpl in *.
  - lia.
  - exact (fst e).
Defined.

Definition env_slice_get_tuples s (es: env_slice s) : list (Tuple.tuple (schema_to_no_name s)) :=
  match es with
    | (r, _, _, t) => t
  end.

Definition env_slice_get_groupby s (es: env_slice s) : groupby_list :=
  match es with
    | (_, _, g, _) => g
  end.  

Definition env_slice_get_selected s (es: env_slice s) : list nat :=
  match es with
    | (_, s, _, _) => s
  end.

Definition env_slice_get_relation s (es: env_slice s) : relation s :=
  match es with
    | (r, _, _, _) => r
  end.
(* ========================================================================================= *)

(*
  `config` is an inductive type that defines a configuration for the query evaluation.
  It is either:
  * `config_terminal` => The query evaluation is done.
  * `config_error` => An error has occurred.
  * `config_ok` => The query evaluation is ok. It consists of:
    - `s` => The schema.
    - `Γ` => The policy environment.
    - `β` => The privacy budget.
    - `ℰ` => The environment.
    - `p` => The provenance context.
*)
Inductive config: Type :=
  (* Terminal wraps a configuration by which we can easily analyze the final state. *)
  | config_terminal: config → config
  | config_error: config
  | config_ok: ∀ s, Policy.context → Configuration.privacy → ℰ s → prov_ctx -> config
.

Notation "'⟨' s Γ β ℰ p '⟩'":= (config_ok s Γ β ℰ p)
  (at level 10, s at next level, Γ at next level, β at next level, ℰ at next level,
  p at next level,
  no associativity).

Inductive Operator: Type :=
  | operator_empty: Operator
  | operator_relation: config →  Operator
  | operator_union: Operator → Operator → Operator
  | operator_join: Operator → Operator → Operator
  | operator_project: project_list → Operator → Operator
  | operator_select: ∀ s, formula s → Operator → Operator
  | operator_grouby_having: ∀ s, groupby_list → agg_list s → formula s → Operator → Operator
.

(*
  @param s The schema, which is a list of tuples where each tuple contains a type and a name.
  @param n The length of the relation to be created.
  @param t The tuple to be repeated.
  @return A relation of length [n] where each tuple is [t].

  [tuple_of_length_n] returns a relation of length [n] where each tuple is [t]. The function
  works by recursively appending [t] to the relation until it reaches the desired length.
*)
Fixpoint tuple_of_length_n s (n: nat) (t: Tuple.tuple (schema_to_no_name s)): relation s :=
match n with
  | O => nil
  | S n' => t :: tuple_of_length_n s n' t
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
  | E_PolicyNotFound: ∀ op f arg Γ p,
      Policy.label_lookup (snd arg) Γ = None →
      apply_unary_function_in_cell bt op f arg Γ p None
  | E_PolicyErr: ∀ op f arg Γ p p_cur p_f,
      Policy.label_lookup (snd arg) Γ = Some p_cur →
      p_f = ∘ (Policy.policy_transform ((unary_trans_op op) :: nil)) →
      ¬ (p_cur ⪯ p_f) →
      apply_unary_function_in_cell bt op f arg Γ p None
  (* TODO: Not finished yet. *)
  | E_PolicyOk: ∀ op f lambda arg Γ p p_cur p_f res Γ' p',
      Policy.label_lookup (snd arg) Γ = Some p_cur →
      p_f = (∘ (Policy.policy_transform ((unary_trans_op op) :: nil))) →
      p_cur ⪯ p_f → f = (unary_function bt lambda) →
      lambda (fst arg) = res →
      Γ' = Policy.update_label (snd arg) Γ p_f →
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
  | E_ApplyOk: ∀ op f arg id tl tl' Γ p ret Γ1 Γ2 Γ' p1 p2 p' res,
      (tuple_single_eq ty) ♯ r = [[ (arg, id) ]] :: tl →
      apply_unary_function_in_cell (fst ty) op f (arg, id) Γ p (Some (ret, Γ1, p1)) →
      do_apply_unary_function ty (eq_sym (tuple_single_eq ty) ♯ tl) op f Γ p (Some (tl', Γ2, p2)) →
      Γ' = merge Γ1 Γ2 → p' = merge p1 p2 →
      res = (Some (eq_sym (tuple_single_eq ty) ♯ ([[ (ret, id) ]] ::
                  ((tuple_single_eq ty) ♯ tl')),
                  Γ', p')) →
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
  | E_ApplyConst: ∀ Γ p ty val name res_tmp res
                 (case_expr: expr = (simple_atomic_expression_const ty val, name)),

        res_tmp = (tuple_of_length_n ((ty, name) :: nil) (List.length r) ((val, 0), tt)) →
        (* A transportation for type casting. *)
        res = (schema_const_ty_eq expr ty val name s case_expr ♯ res_tmp) →
        apply_proj_elem s r expr Γ p (Some (res, ty, Γ, p))
  | E_ApplyUnaryFunctionColumnError: ∀ Γ p op arg n name 
                          (case_expr: expr = (simple_atomic_expression_func_unary op arg, name)),

        arg = (simple_atomic_expression_column n) →
        n > List.length s →
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
  | E_ApplyUnaryFunctionOtherOk: ∀ Γ p op arg ty n name arg' res_tmp res_tmp' res Γ' p'
                            (case_expr: expr = (simple_atomic_expression_func_unary op arg, name))
                            (case_arg: arg ≠ (simple_atomic_expression_column n))
                            (* We can prove this later. *)
                            (type_matches: determine_schema s (project (<< (arg); (name) >> :: nil)) = (ty :: nil)),

        (* We first recursively evaluate the argument. *)
        apply_proj_elem s r (arg, name) Γ p (Some (arg', (fst ty), Γ', p')) →
        (* Then we apply the unary function to the argument. *)
        apply_unary_function_in_relation _ (type_matches ♯ arg') op Γ p (Some (res_tmp, Γ', p')) →
        res = (eq_sym (unary_function_preserves_type' expr s op arg name case_expr) ♯ res_tmp') →
        apply_proj_elem s r expr Γ p (Some (res, (fst ty), Γ', p'))

    (* TODO: Add other cases. *)
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
  | E_EmptyProjectList: ∀ Γ p,
      ℓ = nil →
      apply_proj_in_relation s r ℓ Γ p (Some (nil, Γ, p))
  | E_ApplyElemErrHead: ∀ Γ p  hd tl (proj_case: ℓ = hd :: tl),
      apply_proj_elem s r hd Γ p None →
      apply_proj_in_relation s r ℓ Γ p None
  | E_ApplyElemErrTail: ∀ Γ p hd tl res (proj_case: ℓ = hd :: tl),
      apply_proj_elem s r hd Γ p (Some res) →
      apply_proj_in_relation s r tl Γ p None →
      apply_proj_in_relation s r ℓ Γ p None
  | E_ApplyElemOk: ∀ Γ Γ' Γ'' Γfin p p' p'' pfin hd hd' tl tl' col_tmp col_proxy col
                (proj_case: ℓ = hd :: tl),
      apply_proj_elem s r hd Γ p (Some (hd', Γ', p')) →
      apply_proj_in_relation s r tl Γ p (Some (tl', Γ'', p'')) →
      Γfin = merge Γ' Γ'' →
      pfin = merge p' p'' →
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
      col_tmp = (relation_product _ _ (fst hd') tl') →
      col_proxy = ((determine_schema_concat s hd tl) ♯ col_tmp) →
      col = ((eq_sym proj_case) ♯ col_proxy) →
      apply_proj_in_relation s r ℓ Γ p (Some (col, Γfin, pfin))
.

Inductive apply_proj_in_env_slice s (es: env_slice s) (ℓ: list (simple_atomic_expression * string)):
  Policy.context → prov_ctx →
    option (env_slice (determine_schema s (project ℓ)) * Policy.context * prov_ctx) → Prop :=
  | E_ApplyInEnvSliceerr: ∀ Γ p r a b c,
      normalized (project ℓ) →
      es = (r, a, b, c) →
      apply_proj_in_relation s r ℓ Γ p None →
      apply_proj_in_env_slice s es ℓ Γ p None
  | E_ApplyInEnvSliceOk: ∀ Γ p Γ' p' r r' a b c,
      normalized (project ℓ) →
      es = (r, a, b, c) →
      apply_proj_in_relation s r ℓ Γ p (Some (r', Γ', p')) →
      apply_proj_in_env_slice s es ℓ Γ p (Some ((r', a, b, nil), Γ', p'))
.

(*
  @param s The schema of the relation.
  @param evidence The evidence, which is a list of tuples where each tuple corresponds to a row in the relation.
  @param ℓ A list of simple atomic expressions and their corresponding string identifiers.
  @param Policy.context The policy context.
  @param prov_ctx The proof context.
  @return An optional evidence.
*)
Inductive apply_proj_in_env s evidence ℓ: ℰ s → Policy.context → prov_ctx →
    option (ℰ ((determine_schema (hd_ok s evidence) ℓ) :: (tail s)) * Policy.context * prov_ctx) → Prop :=
  | E_ProjInEnv: ∀ l tl config' (env: ℰ s) Γ Γ' p p' env'
                 (case_s: s = (hd_ok s evidence) :: tl),
      ℓ = project l →
      apply_proj_in_env_slice (hd_ok s evidence) (fst (case_s ♯ env)) l Γ p (Some config') →
      apply_proj_in_env s evidence ℓ env Γ p (Some (env', Γ', p'))
  | E_ProjInEnvError: ∀ l tl Γ p (env: ℰ s) (case_s: s = (hd_ok s evidence) :: tl),
      ℓ = project l →
      apply_proj_in_env_slice (hd_ok s evidence) (fst (case_s ♯ env)) l Γ p None →
      apply_proj_in_env s evidence ℓ env Γ p None
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

Reserved Notation "c1 '=[' o ']=>' c2" (at level 50, left associativity).
Inductive step_config: Operator → config → config → Prop :=
  (* Empty operator clears the environment. *)
  | E_Empty1: ∀ s Γ β p (e: ℰ s),
      ⟨ s Γ β e p ⟩ =[ operator_empty ]=> ⟨ nil nil β tt nil ⟩
  (* If the operator returns an empty schema list or context, we do nothing. *)
  | E_Empty2: ∀ s Γ β p (e: ℰ s) o,
      s = nil ∨ p = nil ∨ Γ = nil →
      ⟨ s Γ β e p ⟩ =[ o ]=> ⟨ nil nil β tt nil ⟩
  (* Getting the relation is an identity operation w.r.t. configurations. *)
  | E_GetRelation: ∀ s s' Γ Γ' β β' p p' (e: ℰ s) (e': ℰ s') c,
      c = ⟨ s' Γ' β' e' p' ⟩ →
      ⟨ s Γ β e p ⟩ =[ operator_relation c]=> c
  (* If the operator returns an empty environment, we do nothing. *)
  | E_ProjEmpty: ∀ s1 s2 Γ Γ' β β' p p' (e: ℰ s1) (e': ℰ s2) project_list o,
      ⟨ s1 Γ β e p ⟩ =[ o ]=> ⟨ s2 Γ' β' e' p' ⟩ →
      List.length s2 = 0 →
      ⟨ s1 Γ β e p ⟩ =[ operator_project project_list o ]=> ⟨ nil Γ' β' tt nil ⟩
  (* If the operator returns a valid environment, we can then apply projection. *)
  | E_ProjOk: ∀ s1 s2 Γ Γ' β β' p p' (e: ℰ s1) (e'': ℰ s2) ℓ ℓ' o,
      ⟨ s1 Γ β e p ⟩ =[ o ]=> ⟨ s2 Γ' β' e'' p'⟩ →
      (* Introduce terms into the scope to avoid identifier problems. *)
        ∀ (evidence: List.length s2 > 0) e',
          let input_schema := (hd_ok s2 evidence) in
            let output_schema := determine_schema input_schema ℓ' in
                ℓ' = normalize_project_list input_schema ℓ →
                   apply_proj_in_env s2 evidence ℓ' e'' Γ p
                   (Some (e', Γ', p')) →
                    ⟨ s1 Γ β e p ⟩ =[ operator_project ℓ o]=>
                      ⟨ (output_schema :: (tail s2)) Γ' β' e' p' ⟩
  (*
     If the operator returns a valid environment, we can then apply projection. Then if the
     projection fails, we return `config_error`.
  *)
  | E_ProjError: ∀ s1 s2 Γ Γ' β β' p p' (e: ℰ s1) (e'': ℰ s2) ℓ ℓ' o,
      ⟨ s1 Γ β e p ⟩ =[ o ]=> ⟨ s2 Γ' β' e'' p'⟩ →
      (* Introduce terms into the scope to avoid identifier problems. *)
        ∀ (evidence: List.length s2 > 0),
          let input_schema := (hd_ok s2 evidence) in
            let output_schema := determine_schema input_schema ℓ' in
                  (*
                     Here, we use `option` rather than `config` since `config` is dependent
                     on schema, but we do need the evidence dependent on schema. This forces
                     us to pattern match on `config` to get the schema so that we cannot
                     pass `evidence` to `apply_proj_in_env` function.
                  *)
                  apply_proj_in_env s2 evidence ℓ' e'' Γ p None →
                    ⟨ s1 Γ β e p ⟩ =[ operator_project ℓ o]=> config_error
  | E_Union: ∀ s Γ Γ1 Γ2 β β1 β2 p p1 p2 e e1 e2 o1 o2,
      ⟨ s Γ β e p ⟩ =[ o1 ]=> ⟨ s Γ1 β1 e1 p1 ⟩ →
      ⟨ s Γ β e p ⟩ =[ o2 ]=> ⟨ s Γ2 β2 e2 p2 ⟩ →
      ⟨ s Γ β e p ⟩ =[ operator_union o1 o2 ]=> ⟨ s Γ1 β1 e1 p1 ⟩
where "c1 '=[' o ']=>' c2" := (step_config o c1 c2).
Hint Constructors step_config: core.

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
