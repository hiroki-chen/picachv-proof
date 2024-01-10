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

Inductive Operator: Type :=
  | operator_empty: Operator
  | operator_relation: forall s, relation s → Operator
  | operator_union: Operator → Operator → Operator
  | operator_join: Operator → Operator → Operator
  | operator_project: project_list → Operator → Operator
  | operator_select: ∀ s, formula s → Operator → Operator
  | operator_grouby_having: ∀ s, groupby_list → agg_list s → formula s → Operator → Operator
.

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
Definition apply_unary_function_in_cell bt (f_type: UnOp) (f: unary_func) (arg: type_to_coq_type bt * nat)
                                         (Γ: Policy.context) (p: prov_ctx)
  : option (type_to_coq_type bt * Policy.context * prov_ctx).
refine (
match arg with
  | (val, id) =>
    (* We need to first check the policy labels. *)
    match Policy.label_lookup id Γ with
    | None => None
    | Some pe =>
      match pe with
      | p_cur => _
      end
    end
  end
).
  pose (Policy.policy_transform ((unary_trans_op f_type) :: nil)) as p_func.
  destruct (Policy.policy_ord_dec p_cur (Policy.policy_atomic p_func)).
  - (* Allowed. *)


Admitted.

(*
  @param ty A tuple containing a type and a name.
  @param r The relation, which is a list of tuples where each tuple contains a single type.
  @param Γ The policy context.
  @param p The proof context.
  @return An optional tuple containing the relation, the policy context, and the proof context.

  This function does the actual function application on a relation containing only one column on
  which the unary function should be applied.
*)
Fixpoint do_apply_unary_function ty f_type (f: unary_func) (r: relation (ty :: nil))
                                    (Γ: Policy.context) (p: prov_ctx)
  : option (relation (ty :: nil) * Policy.context * prov_ctx).
refine (
  match r with
  | nil => Some (nil, Γ, p)
  | t :: r' => _
  end
).
  destruct ty as [bt name]. simpl in *.
  destruct t as [cell _].
  (* We obtain the current value as well as updated contexts. *)
  pose (apply_unary_function_in_cell bt f cell Γ p) as cell'.
  destruct cell' as [ [ [cell' Γ_cur ] p_cur] |].
  - (* Some *)
    specialize do_apply_unary_function with (ty := (bt, name)) (f := f) (r := r') (Γ := Γ_cur) (p := p_cur).
    rename do_apply_unary_function into tl. clear Γ. clear p. clear r'. clear r.

    destruct tl as [tl|].
    + (* Some *)
      destruct tl as [ [r' Γ'] p' ].
      (* We lift cell into a tuple. *)
      pose ((cell', (snd cell)), tt) as hd.
      exact (Some (hd :: r', Γ', p')).
    + (* None *)
      exact None.
  - (* None *)
    exact None.
Defined.

(*
  @param s The schema, which is a list of tuples where each tuple contains a type and a name.
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
Definition apply_unary_function_in_relation s (op: UnOp) (ok: List.length s = 1)
                                            (ctx: relation s * Policy.context * prov_ctx)
  : option (relation s * Policy.context * prov_ctx).
refine (
  match ctx with
    | (r, Γ, p) =>
      match s as s' return s = s' → _ with
        | nil => fun _ => _
        | ty :: nil => fun _ => _
        | _ => _
      end eq_refl
  end
); intros; subst; try inversion ok.
  destruct op eqn: Hop.
  (* Identity function. *)
  - exact (do_apply_unary_function _ (unary_function (fst ty) (fun x => x)) r Γ p).
  - destruct ty.
    (* We need to check the type now. *)
    destruct b eqn: Htype.
    + exact None.
    + exact None.
    (* We need to explicitly give the type to Coq. *)
    + exact (do_apply_unary_function << (StringType); (s) >> (unary_function StringType (fun x => redact_string x n false)) r Γ p).
  (* Not implemented yet. *)
  - exact None.
  - exact None.
  - exact None.
  - exact None.
Defined.

(*
  `apply_proj_elem` is a function that applies a projection operation to a
  single column of a relation. This will further consult the `c [ f ] c'` relation to determine the output relation.

  Note that if this function returns `None` then it means that something is wrong with the input.
  `None` does not imply that the policy is violated. For example, if the input relation is empty,
  then we cannot apply the projection operation to any column.
*)
Definition apply_proj_elem s (r: relation s) (expr: simple_atomic_expression * string)
                             (Γ: Policy.context) (p: prov_ctx)
                             (normalized: normalized_expr (fst expr))
  : option (relation (determine_schema s (project (expr :: nil))) * Policy.context * prov_ctx).
refine (
(fix eval_expr expr :=
    match expr with
    | (expr, name) =>
        match expr with
        (*
          This is not possible since e have already ensured that all columns must be applied
          with a function by a normalization function.
        *)
        | simple_atomic_expression_column _ => None
        | simple_atomic_expression_const ty c => _
        | simple_atomic_expression_func_unary op arg => _
        | simple_atomic_expression_func_binary op arg1 arg2 => _
        end
      end) expr
).
  - exact (let res := (tuple_of_length_n ((ty, name) :: nil) (List.length r) ((c, 0), tt)) in
              Some (res, Γ, p)).
  - destruct (determine_schema s (project (<< (arg); (name) >> :: nil))).
    + exact None.
    + pose (eval_expr (arg, name)) as arg'.
      assert (len: List.length (determine_schema s (project (<< (arg); (name) >> :: nil))) ≤ 1).
      {
        specialize determine_schema_length_le with (s := s) (pl := << (arg); (name) >> :: nil).
        intros. simpl in *. assumption. 
      }
      destruct arg' as [arg'|].
      * apply le_decide in len. destruct len.
        (* Len < 1. *)
        -- exact None.
        -- pose (apply_unary_function_in_relation _ op e arg') as arg''.
           specialize unary_function_preserves_type with (s := s) (op := op) (arg := arg) (name := name).
           intros.
           rewrite <- H in arg''.
           exact arg''.
      * exact None.
  (*
    The function has only one argument which is a column. In this case, we need to:
    1. Obtain the whole column from the relation.
    2. Obtain the label, provenance from the environment.
    3. Check the permission against the policy label.
    4. Evaluate the function.
    5. Update provenance and label.
  *)
  - pose (eval_expr (arg1, name)) as arg1'.
    pose (eval_expr (arg2, name)) as arg2'.
    destruct arg1' as [arg1'|]; destruct arg2' as [arg2'|].


Admitted.

(*
  Since `relation` is a dependent type, we need to apply a helper function to
  update the relation with regard to the schema. This means we cannot simply
  quantify over `s` in the definition since that would make the type of `relation`
  different in each case and hard to reason about.

  Instead, we know that the schema can be determined given the input schema
  and the project list. We can thus manipulate the output schema on which the
  output relation depends.
*)
Definition apply_proj_in_relation s (r: relation s) (ℓ: list (simple_atomic_expression * string))
                                    (Γ: Policy.context) (p: prov_ctx)
                                    (normalized: normalized (project ℓ))
  : option (relation (determine_schema s (project ℓ)) * Policy.context * prov_ctx).
Proof.
  induction ℓ.
  - exact (Some (nil, Γ, p)).
  - (* We apply `a` to the relation s and obtain the output. *)
    pose (normalized_implies_each_expr _ normalized a) as norm.
    pose (in_eq a ℓ) as pred. apply norm in pred.
    pose (apply_proj_elem s r a Γ p pred) as col.
    destruct col as [col | ].
    + pose (normalized_cons _ _ normalized) as norm'.
      destruct norm'. apply IHℓ in H0. clear IHℓ. rename H0 into IHℓ.

      destruct IHℓ as [IHℓ | ].
      * pose (fst (fst IHℓ)) as r'.
        pose (fst (fst col)) as r''.
        pose (snd (fst IHℓ)) as Γ'.
        pose (snd (fst col)) as Γ''.
        pose (snd IHℓ) as p'.
        pose (snd col) as p''.

        apply (merge p'') in p'.
        apply (merge Γ'') in Γ'.

        (* The next thing to do is merge relations, but this could
          be not so straightforward since we need to merge the
          schemas that are hidden in `determine_schema` function.

          We also need to prove that
            ```
            determine_schema s (project (a :: @nil simple_atomic_expression)) ++
            determine_schema s (project ℓ)
            =
            determine_schema s (project (a :: ℓ))
            ```
        *)
        apply (relation_product _ _ r'') in r'.
        rewrite (determine_schema_concat s a ℓ) in r'.
        exact (Some (r', Γ', p')).
      * exact None.
    + exact None.
Defined.

Definition apply_proj_in_env_slice s (es: env_slice s) (ℓ: list (simple_atomic_expression * string))
                                     (Γ: Policy.context) (p: prov_ctx)
                                     (norm: normalized (project ℓ))
  : option (env_slice (determine_schema s (project ℓ)) * Policy.context * prov_ctx) :=
  match es with
  | (r, a, b, _) =>
      let r := (apply_proj_in_relation s r ℓ Γ p norm) in
        match r with 
        | Some (r', Γ', p') => Some ((r', a, b, nil), Γ', p')
        | None => None
        end
  end.

(* 
  A helper function that applies the projection list in the environment.
  It returns a new environment, a new policy environment, and a new provenance context.

  Note that `ℓ` is the normalized projection list.
*)
Definition apply_proj_in_env s (evidence: List.length s > 0): ∀ (e: ℰ s)
                             (ℓ: project_list) (norm: normalized ℓ)
                             (Γ: Policy.context) (p: prov_ctx),
                             option (
                              ℰ ((determine_schema (hd_ok s evidence) ℓ) :: (tail s)) *
                              Policy.context * prov_ctx).
  destruct s.
  - simpl in evidence. lia.
  - intros. 
    simpl. intros.
    destruct ℓ.
    (* Since we have the evidence that `ℓ` is normalized, it cannot be a `project_star`. *)
    + inversion norm.
    (* We now apply the projection list in the environment slice. *)
    + pose (apply_proj_in_env_slice s (fst e) l Γ p norm) as config'.
      destruct config' as [config' | ].
      * exact (Some (fst (fst config'), snd e, (snd (fst config')), snd config')).
      * exact None.
Defined.

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
              ∀ (prop: ℓ' = normalize_project_list input_schema ℓ),
                  Some (e', Γ', p') = apply_proj_in_env s2 evidence e'' ℓ'
                                 (normalize_is_normalized _ _ _ prop) Γ p →
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
              ∀ (prop: ℓ' = normalize_project_list input_schema ℓ),
                  (*
                     Here, we use `option` rather than `config` since `config` is dependent
                     on schema, but we do need the evidence dependent on schema. This forces
                     us to pattern match on `config` to get the schema so that we cannot
                     pass `evidence` to `apply_proj_in_env` function.
                  *)
                  None = apply_proj_in_env s2 evidence e'' ℓ'
                         (normalize_is_normalized _ _ _ prop) Γ p →
                    ⟨ s1 Γ β e p ⟩ =[ operator_project ℓ o]=> config_error
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
