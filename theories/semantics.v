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
Require Import expression.
Require Import finite_bags.
Require Import types.
Require Import lattice.
Require Import ordering.
Require Import prov.
Require Import relation.
Require Import util.

(* A typing environment `Γ ⊢ ...` for evalauting the schema. *)
Definition ty_env := (list expr_type)%type.

Inductive project_list: Set :=
  (* Denotes a projection list that projects on *all*. *)
  | project_star: project_list
  (* Denotes a project list consisting of expressions, i.e., lambda terms; and new ids. *)
  | project: list (expression * nat) → project_list
.
Hint Constructors project_list: core.

(*
  @param s The schema of the expression.
  @param arg The expression for which the basic type is to be determined.
  @param env The list of basic types that form the environment for the expression.
  @returns option basic_type The basic type of the expression if it can be determined, `None` otherwise.

  The `determine_bt_from_expr_helper` function is a recursive function that determines the basic type of an
  expression given a schema and an environment of basic types. This function is used more like as a
  type checker.
*)
Fixpoint determine_bt_from_expr_helper (s: schema) (arg: expression_lexed) (env: ty_env):
  option expr_type :=
    match arg with
    (* Lookup in the environment. *)
    | expression_lexed_var n => nth_option env n
    (* For constants, we already know its type. *)
    | expression_lexed_const bt _ => Some (expr_type_basic bt)
    (* For columns, we need to extract it from the schema. *)
    | expression_lexed_column n =>
        let bt := find' (fun x y => (snd x) =? y) s n in
          option_map (fun x => expr_type_basic (fst x)) bt
    (* For function abstraction, we encode the argument type, so wecan extract it and evaluate its body. *)
    | expression_lexed_abs τ body =>
        option_map (fun x => expr_type_func τ x) (determine_bt_from_expr_helper s body (τ :: env))
    (* For function application, we need to evaluate the function and the argument and check if their types match. *)
    | expression_lexed_app f x =>
        match determine_bt_from_expr_helper s f env, determine_bt_from_expr_helper s x env with
          | Some (expr_type_func τ1 τ2), Some τ3 =>
            if expr_type_eqb τ1 τ3 then Some τ2 else None
          | _, _ => None
        end
    (*
      For binary operations, we need to evaluate the two arguments and check if their types match and
      the operation type is correct.
    *)
    | expression_lexed_binary op x y =>
        match determine_bt_from_expr_helper s x env, determine_bt_from_expr_helper s y env with
          | Some τ1, Some τ2 =>
            match op with
              | binary_function op _ _ =>
                match op with
                | Arithmetic _ =>
                  if expr_type_eqb τ1 (expr_type_basic IntegerType) then
                    if expr_type_eqb τ2 (expr_type_basic IntegerType) then
                      Some (expr_type_basic IntegerType)
                    else None
                  else None
                | Comparison _ =>
                  if expr_type_eqb τ1 τ2 then Some (expr_type_basic BoolType) else None
                | Logical _ =>
                  if expr_type_eqb τ1 (expr_type_basic BoolType) then
                    if expr_type_eqb τ2 (expr_type_basic BoolType) then
                      Some (expr_type_basic BoolType)
                    else None
                  else None
              end
            end
          | _, _ => None
        end
    | expression_lexed_unary op x =>
        match determine_bt_from_expr_helper s x env with
          | Some τ =>
            match op with
              | unary_function op ty _ =>
                if expr_type_eqb τ (expr_type_basic ty) then
                  match op with
                  | Not =>
                    if expr_type_eqb τ (expr_type_basic BoolType) then
                      Some (expr_type_basic BoolType)
                    else None
                  | _ =>
                    if expr_type_eqb τ (expr_type_basic ty) then
                      Some (expr_type_basic IntegerType)
                    else None
                  end
                else None
            end
          | _ => None
        end
    | expression_lexed_agg op x =>
        match determine_bt_from_expr_helper s x env with
          | Some τ =>
            match op with
            | aggregate_function _ _ τ _ => Some (expr_type_basic τ)
            end
          | _ => None
        end
    end.

Definition determine_bt_from_expr (s: schema) (arg: expression_lexed): option basic_type :=
  match determine_bt_from_expr_helper s arg nil with
    | Some (expr_type_basic bt) => Some bt
    | _ => None
  end.

Fixpoint determine_schema (s: schema) (pl: list (expression * nat)): option schema :=
  match pl with
  | nil => Some nil
  | (x, name) :: ℓ' =>
    let lexed_expr := lex x nil in
      match determine_bt_from_expr s lexed_expr with
        | Some bt =>
          match determine_schema s ℓ' with
            | Some sch => Some ((bt, name) :: sch)
            | None => None
          end
        | None => None
      end
  end.

(*
  @param s The schema of the relation.
  @param group_by The list of column indices to group by.
  @param agg The list of aggregation expressions, represented in the form of lambda calculus.
  @returns schema The schema resulting from the aggregation operation.

  This function computes the schema for the aggregation operation that consists of two components:

  - The `group_by` keys which are just a list of column indices.
    These indices determine the columns that will be used to group the data in the relation.
  - The `agg` aggregation expressions which are represented in the form of lambda calculus.
    These expressions determine how the data in each group should be aggregated.

  The resulting schema describes the structure of the data after the aggregation operation has been applied.

  # Examples

  ```
  (* We are now given a schema *)
  let s = [(IntegerType, "a"), (IntegerType, "b"), (IntegerType, "c")];
  let group_by = [0, 1];
  agg = [((λ x: x, "count"(x)) (col 2)), "count(c)"), ((λ x: x, "sum"(x)) (col 2), "sum(c)"))];

  (* The resulting schema will be *)
  determine_schema_agg s group_by agg =
    [(IntegerType, "a"), (IntegerType, "b"), (IntegerType, "count(c)"), (IntegerType, "sum(c)")];
  ```
*)
Definition determine_schema_agg (s: schema) (agg: agg_list) (gb: groupby_list):
  bounded_list s gb → option schema :=
  fun bounded =>
    let determine_from_agg :=
      (fix f agg :=
        match agg with
        | nil => Some nil
        | (x, name) :: ℓ' =>
          match determine_bt_from_expr s (lex x nil) with
          | Some bt =>
            match f ℓ' with
            | Some sch => Some ((bt, name) :: sch)
            | None => None
            end
          | None => None
          end
        end) in
    match determine_from_agg agg with
    | Some agg_schema =>
        let gb_schema := ntypes s gb bounded in
          Some (gb_schema ++ agg_schema)
    | None => None
    end.

(*
  @param s The schema of the relation.
  @return project_list The expanded project list.

  This function will expand `SELECT *` into its full project list.
*)
Definition project_all (s: schema): project_list :=
  let f := fix f s n :=
    match s with
    | nil => nil
    | hd :: tl => (expression_column n, snd hd) :: f tl (S n)
    end
  in project (f s 0).

Definition project_list_preprocess (s: schema) (pl: project_list): project_list :=
  match pl with
    | project_star => project_all s
    | _ => pl
  end.

(* This first creates for each tuple a `groupby_proxy` which can later be `gathered` for our convenience. *)
Definition get_group_proxy_helper s (r: relation s) (gb_keys: groupby_list) (bounded: bounded_list s gb_keys):
  list groupby :=
  let gb_keys_extracted := (extract_columns s r gb_keys bounded) in
    (fix create_group_proxy keys n :=
      match keys with
      | nil => nil
      | hd :: tl => groupby_proxy _ hd (n :: nil) :: (create_group_proxy tl (S n))
      end
    ) gb_keys_extracted 0.

Definition get_group_proxy s (r: relation s) (gb_keys: groupby_list) (bounded: bounded_list s gb_keys): list groupby.
  pose (intermediate_gb_proxy := get_group_proxy_helper s r gb_keys bounded).
  induction intermediate_gb_proxy.
  - exact nil.
  - rename IHintermediate_gb_proxy into rest.
    (*
       For each of the element `a` in the intermediate result, we need to check if this can be "found"
       in this rest. If yes, we need to merge it into the rest and then return the merged one. If not,
       we need to remain as is.
     *)
     pose (gather := fix gather (elem: groupby) (proxy: list groupby) :=
       match proxy with
       | nil => elem :: nil
       | hd :: tl =>
          match hd, elem with
          | groupby_proxy s key indices, groupby_proxy s' key' indices' =>
            match list_eq_dec basic_type_eq_dec s s' with
            | left eq => 
              if (Tuple.tuple_value_eqb _ key' (eq ♯ key)) then
                (groupby_proxy s key (indices ++ indices'):: gather elem tl)
              else
                hd :: (gather elem tl)
            | right _ => nil
            end
          end
       end
     ).

     exact (gather a rest).
Defined.

Inductive operator: Type :=
  | operator_empty: operator
  (* `nat` means the index of the relation it wants to access the n-th dataset inside `db`. *)
  | operator_relation: nat → operator
  | operator_union: operator → operator → operator
  | operator_join: operator → operator → operator
  | operator_project: project_list → operator → operator
  | operator_select: expression → operator → operator
  | operator_groupby_having: groupby_list → agg_list → expression → operator → operator
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

(* Apply *one* expression on the relation. *)
Inductive eval_expr_in_relation (s: schema) (r: relation s):
  Policy.context → budget → prov_ctx → expression →
    option (EResult * Policy.context * budget * prov_ctx) → Prop :=
.

(* Apply each project expression on the given relation `r`. *)
Inductive apply_proj_in_relation (s: schema) (r: relation s) (ℓ: list (expression * nat)):
  ∀ s', Policy.context → budget → prov_ctx →
    option (relation s' * Policy.context * budget * prov_ctx) → Prop :=
  (* Either the projection list is empty or the relation is empty. As such, we just do nothing here. *)
  | E_ApplyElemEmpty: ∀ s' Γ β p,
      ℓ = nil ∨ r = nil →
      apply_proj_in_relation s r ℓ s' Γ β p (Some (nil, Γ, β, p))
  | E_ApplyElemErrHead: ∀ s' Γ β p hd tl,
      ℓ = hd :: tl →
      eval_expr_in_relation s r Γ β p (fst hd) None →
      apply_proj_in_relation s r ℓ s' Γ β p None
  | E_ApplyElemHeadNonRelation: ∀ s' res r' Γ Γ' β β' p p' hd tl,
      ℓ = hd :: tl →
      eval_expr_in_relation s r Γ β p (fst hd) (Some (res, Γ', β', p')) →
      res ≠ EResultRelation r' →
      apply_proj_in_relation s r ℓ s' Γ β p None
  | E_ApplyElemErrTail: ∀ s' hd tl Γ β p,
      ℓ = hd :: tl →
      apply_proj_in_relation s r tl s' Γ β p None →
      apply_proj_in_relation s r ℓ s' Γ β p None
  | E_ApplyElemOk: ∀ s_hd s_tl Γ Γ' Γ'' β β' β'' p p' p'' hd hd' tl tl'
                (proj_case: ℓ = hd :: tl),
      r ≠ nil →
      eval_expr_in_relation s r Γ β p (fst hd) (Some (EResultRelation (RelationWrapped s_hd hd'), Γ', β', p')) →
      Some s_tl = determine_schema s tl →
      apply_proj_in_relation s r tl s_tl Γ' β' p' (Some (tl', Γ'', β'', p'')) →
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
      let col := (relation_product _ _ hd' tl') in
        (* let col_proxy := ((determine_schema_concat s hd tl) ♯ col_tmp) in
          col = ((eq_sym proj_case) ♯ col_proxy) → *)
          apply_proj_in_relation s r ℓ _ Γ β p (Some (col, Γ'', β'', p''))
.

(*
  @param s The schema of the relation.
  @param r The relation in which the predicate is to be evaluated.
  @param Policy.context The policy context.
  @param budget The budget for the evaluation.
  @param prov_ctx The provenance context.
  @param expression The predicate to be evaluated.
  @param option (relation s * Policy.context * budget * prov_ctx) The expected result of the evaluation.
  @returns Prop A proposition that is true if the evaluation is correctly applied, false otherwise.

  The `eval_predicate_in_relation` inductive type represents the evaluation of a predicate in a relation.
  The evaluation is performed in the context of a given policy context and provenance context, and it may
  consume a certain amount of budget. If the evaluation is successful, the function returns `Some` with a
  tuple containing the resulting relation, the updated policy context, the remaining budget, and the up-
  dated provenance context. The predicate is checked against each tuple in the relation.

  ** This must not involve `having` which is handled elsewhere.
*)
Inductive eval_predicate_in_relation (s: schema) (r: relation s):
  Policy.context → budget → prov_ctx → expression →
    option (relation s * Policy.context * budget * prov_ctx) → Prop :=
  | E_EvalExprRelationNil: ∀ Γ β p e,
      r = nil →
      eval_predicate_in_relation s r Γ β p e (Some (nil, Γ, β, p))
  | E_EvalExprConsTrue: ∀ db db' Γ Γ' Γ'' β β' β'' p p' p'' e env hd tl tl' id,
      r = hd :: tl →
      eval_expr (⟨ db Γ β p ⟩) (TupleWrapped s hd) None e (env, EResultValue BoolType (true, id)) →
      fst (fst (fst env)) = ⟨ db' Γ' β' p' ⟩ →
      eval_predicate_in_relation s tl Γ' β' p' e (Some (tl', Γ'', β'', p'')) →
      eval_predicate_in_relation s r Γ β p e (Some (hd :: tl', Γ'', β'', p''))
  | E_EvalExprConsFalse: ∀ db db' Γ Γ' Γ'' β β' β'' p p' p'' e env hd tl tl' id,
      r = hd :: tl →
      eval_expr (⟨ db Γ β p ⟩) (TupleWrapped s hd) None e (env, EResultValue BoolType (false, id)) →
      fst (fst (fst env)) = ⟨ db' Γ' β' p' ⟩ →
      eval_predicate_in_relation s tl Γ' β' p' e (Some (tl', Γ'', β'', p'')) →
      eval_predicate_in_relation s r Γ β p e (Some (tl', Γ'', β'', p''))
  | E_EvalError: ∀ db res v Γ β p e env hd tl,
      r = hd :: tl →
      eval_expr (⟨ db Γ β p ⟩) (TupleWrapped s hd) None e (env, res) →
      res ≠ EResultValue BoolType v →
      eval_predicate_in_relation s r Γ β p e None
  | E_EvalError2: ∀ Γ Γ' β β' p p' e hd tl,
      r = hd :: tl →
      eval_predicate_in_relation s tl Γ' β' p' e None →
      eval_predicate_in_relation s r Γ β p e None
.

(*
  The `apply_fold_on_groups` inductive type represents the application of a list of aggregation operations on a list of
  `groupby_proxy` elements.
*)
Inductive apply_fold_on_groups:
  ∀ s s_agg, Policy.context → budget → prov_ctx → list groupby → agg_list → relation s →
    option (relation s_agg * Policy.context * budget * prov_ctx) → Prop :=
  | E_ApplyFoldOnGroupsEmpty: ∀ s s_agg Γ β p gb agg r,
      gb = nil ∨ agg = nil →
      apply_fold_on_groups s s_agg Γ β p gb agg r (Some (nil, Γ, β, p))
.

(* TODO *)
(* Inductive eval_groupby_having *)

(* We should invoke `eval_expr` to get the result. *)
Inductive eval_aggregate:
  ∀ s s_agg gb, bounded_list s gb → agg_list → expression → Policy.context → budget → prov_ctx → relation s →
    option (relation s_agg * Policy.context * budget * prov_ctx) → Prop :=
  | E_EvalAggregate: ∀ s s_agg Γ β p gb (bounded: bounded_list s gb)
                       gb_proxy agg f r res,
      get_group_proxy s r gb bounded = gb_proxy →
      (* TODO: Filter `gb proxy` using the `group_by` filter. *)
      apply_fold_on_groups s s_agg Γ β p gb_proxy agg r res →
      eval_aggregate s s_agg gb bounded agg f Γ β p r res
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
      c' = config_output (RelationWrapped nil nil) c →
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
      c' = config_output (RelationWrapped s r) (⟨ db' Γ' β' p' ⟩) →
      r = nil ∨ s = nil →
      ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ c' ⟧
  (* If the operator returns a valid relation, we can then apply projection. *)
  | E_ProjOk: ∀ c c' c'' db db' pl pl' s' s''
                Γ Γ' Γ'' β β' β'' p p' p'' r' r'' o,
      c = ⟨ db Γ β p ⟩ →
      (* We first evaluate the inner operator and get the output. *)
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      (* We then destruct the output. *)
      c' = config_output (RelationWrapped s' r') (⟨ db' Γ' β' p' ⟩) →
      s' ≠ nil ∧ r' ≠ nil →
      (* We do a simple preprocess. *)
      project pl' = project_list_preprocess s' pl →
      Some s'' = determine_schema s' pl' →
        (* We then apply projection inside the environment. *)
        apply_proj_in_relation s' r' pl' s'' Γ' β' p' (Some (r'', Γ'', β'', p'')) →
        c'' = config_output (RelationWrapped _ r'') (⟨ db' Γ'' β'' p'' ⟩) →
        ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ c'' ⟧
  (*
     If the operator returns a valid environment, we can then apply projection. Then if the
     projection fails, we return `config_error`.
  *)
  | E_ProjError: ∀ c c' db db' pl pl' s' s''
                Γ Γ' β β' p p' r' o,
      c = ⟨ db Γ β p ⟩ →
      (* We first evaluate the inner operator and get the output. *)
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      (* We then destruct the output. *)
      c' = config_output (RelationWrapped s' r') (⟨ db' Γ' β' p' ⟩) →
      s' ≠ nil ∧ r' ≠ nil →
      (* We do a simple preprocess. *)
      project pl' = project_list_preprocess s' pl →
      Some s'' = determine_schema s' pl' →
        (* We then apply projection inside the environment. *)
        apply_proj_in_relation s' r' pl' s'' Γ β p None →
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
  (*
     If we the project list is itself wrongly typed, we return error.
  *)
  | E_ProjError3: ∀ c c' db db' pl pl' s'
                Γ Γ' β β' p p' r' o,
      c = ⟨ db Γ β p ⟩ →
      (* We first evaluate the inner operator and get the output. *)
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      (* We then destruct the output. *)
      c' = config_output (RelationWrapped s' r') (⟨ db' Γ' β' p' ⟩) →
      s' ≠ nil ∧ r' ≠ nil →
      (* We do a simple preprocess. *)
      project pl' = project_list_preprocess s' pl →
      None = determine_schema s' pl' →
      ⟦ c (operator_project pl o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectError: ∀ c c' db db' Γ Γ' β β' p p' s' r' o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s' r') (⟨ db' Γ' β' p' ⟩) →
      eval_predicate_in_relation s' r' Γ' β' p' expr  None →
      ⟦ c (operator_select expr o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectError2: ∀ c db Γ β p o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ config_error ⟧ →
      ⟦ c (operator_select expr o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectError3: ∀ c c' db db' Γ Γ' β β' p p' s1 s2 r' o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s2 r') (⟨ db' Γ' β' p' ⟩) →
      s1 ≠ s2 →
      ⟦ c (operator_select expr o) ⟧ ⇓ ⟦ config_error ⟧
  | E_SelectOk: ∀ c c' c'' db db' Γ Γ' Γ'' β β' β'' p p' p'' s' r' r'' o expr,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s' r') (⟨ db' Γ' β' p' ⟩) →
      eval_predicate_in_relation s' r' Γ' β' p' expr (Some (r'', Γ'', β'', p'')) →
      c'' = config_output (RelationWrapped s' r'') (⟨ db' Γ'' β'' p'' ⟩) →
      ⟦ c (operator_select expr o)⟧ ⇓ ⟦ c'' ⟧
  | E_UnionError: ∀ c c' c'' db Γ β p o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c' = config_error ∨ c'' = config_error →
      ⟦ c (operator_union o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_UnionSchemaError: ∀ c c' c'' db db' db'' Γ Γ' Γ'' β β' β'' p p' p'' s1 s2 r' r'' o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      s1 ≠ s2 →
      ⟦ c (operator_union o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_UnionOk: ∀ c c' c'' db db' db'' Γ Γ' Γ'' β β' β'' p p' p'' s r' r'' o1 o2,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      (*
        We ensure that cells are always assigned new ids;
        so it is safe for us to just append them together.
      *)
      let merged_p := merge_env p' p'' in
        let merged_Γ := merge_env Γ' Γ'' in
          let merged_β := calculate_budget β' β'' in
          (* TODO: How to deal with privacy budget? *)
          ⟦ c (operator_union o1 o2) ⟧ ⇓
          ⟦ config_output (RelationWrapped s (r' ++ r'')) (⟨ db'' merged_Γ merged_β merged_p ⟩) ⟧
  | E_JoinError: ∀ c c' c'' db Γ β p o1 o2,
      c = ⟨ db Γ β p ⟩ → 
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c' = config_error ∨ c'' = config_error →
      ⟦ c (operator_join o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_JoinError2: ∀ c c' c'' db db' db'' Γ Γ' Γ'' β β' β'' p p' p'' s1 s2 r' r'' o1 o2,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      let join_by := (natural_join_list s1 s2) in
        (relation_join_by_prv s1 s2 join_by r' r'' Γ' Γ'' β' β'' p' p'')
        None →
        ⟦ c (operator_join o1 o2) ⟧ ⇓ ⟦ config_error ⟧
  | E_JoinOk: ∀ c c' c'' db db' db'' Γ Γ' Γ'' Γout β β' β'' βout p p' p'' pout s1 s2 r' r'' r rout o1 o2,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o1 ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩) →
      ⟦ c o2 ⟧ ⇓ ⟦ c'' ⟧ →
      c'' = config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩) →
      let join_by := (natural_join_list s1 s2) in
        (relation_join_by_prv s1 s2 join_by r' r'' Γ' Γ'' β' β'' p' p'')
        (Some (rout, Γout, βout, pout))→
        r = RelationWrapped _ rout →
        ⟦ c (operator_join o1 o2) ⟧ ⇓
        (* TODO: Should join. *)
        ⟦ config_output r (⟨ db'' Γout βout pout ⟩) ⟧
  | E_AggEmpty: ∀ c c' db Γ β p o s r gb agg f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s r) c' →
      s = nil ∨ r = nil →
      ⟦ c (operator_groupby_having gb agg f o) ⟧ ⇓ ⟦ c' ⟧
  | E_AggError: ∀ c db Γ β p o gb agg f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ config_error ⟧ →
      ⟦ c (operator_groupby_having gb agg f o) ⟧ ⇓ ⟦ config_error ⟧
  | E_AggNotBounded: ∀ s c c' db db' Γ Γ' β β' p p' o r gb agg f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s r) (⟨ db' Γ' β' p' ⟩) →
      s ≠ nil ∧ r ≠ nil →
      ¬ bounded_list s gb →
      ⟦ c (operator_groupby_having gb agg f o) ⟧ ⇓ ⟦ config_error ⟧
  | E_AggSchemaError: ∀ c c' db db' Γ Γ' β β' p p' s r gb agg o f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s r) (⟨ db' Γ' β' p' ⟩) →
      s ≠ nil ∧ r ≠ nil →
      ∀ (bounded: bounded_list s gb),
        None = determine_schema_agg s agg gb bounded →
        ⟦ c (operator_groupby_having gb agg f o) ⟧ ⇓ ⟦ config_error ⟧
  | E_AggFail: ∀ c c' db db' Γ Γ' β β' p p' s s_agg r gb agg o f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s r) (⟨ db' Γ' β' p' ⟩) →
      s ≠ nil ∧ r ≠ nil →
      ∀ (bounded: bounded_list s gb),
        Some s_agg = determine_schema_agg s agg gb bounded →
        eval_aggregate s s_agg gb bounded agg f Γ' β' p' r None →
        ⟦ c (operator_groupby_having gb agg f o) ⟧ ⇓ ⟦ config_error ⟧
  | E_AggOk: ∀ c c' c'' db db' Γ Γ' Γ'' β β' β'' p p' p'' s s_agg r r' gb agg o f,
      c = ⟨ db Γ β p ⟩ →
      ⟦ c o ⟧ ⇓ ⟦ c' ⟧ →
      c' = config_output (RelationWrapped s r) (⟨ db' Γ' β' p' ⟩) →
      s ≠ nil ∧ r ≠ nil →
      ∀ (bounded: bounded_list s gb),
        Some s_agg = determine_schema_agg s agg gb bounded →
        eval_aggregate s s_agg gb bounded agg f Γ' β' p' r (Some (r', Γ'', β'', p'')) →
        c'' = config_output (RelationWrapped s_agg r') (⟨ db' Γ'' β'' p'' ⟩) →
        ⟦ c (operator_groupby_having gb agg f o) ⟧ ⇓ ⟦ c'' ⟧
where "'⟦' c op '⟧' '⇓' '⟦' c' '⟧'" := (step_config (c, op) c').
Hint Constructors step_config: core.

Section Facts.

Inductive has_type: schema → ty_env → expression_lexed → expr_type → Prop :=
  (* If variable is found in the typing environment, then we know its type. *)
  | T_Var: ∀ s env x t,
      nth_option env x = Some t →
      has_type s env (expression_lexed_var x) t
  | T_Const: ∀ s env bt c,
      has_type s env (expression_lexed_const bt c) (expr_type_basic bt)
  | T_Abs: ∀ s env t1 t2 body,
      has_type s (t1 :: env) body t2 →
      has_type s env (expression_lexed_abs t1 body) (expr_type_func t1 t2)
  | T_Column: ∀ s env n t,
      find' (fun x y => (snd x) =? y) s n = Some t →
      has_type s env (expression_lexed_column n) (expr_type_basic (fst t))
  | T_App: ∀ s env t1 t2 e1 e2,
      has_type s env e1 (expr_type_func t1 t2) →
      has_type s env e2 t1 →
      has_type s env (expression_lexed_app e1 e2) t2
  (* TODO. *)
.

Theorem determine_bt_from_expr_correct: ∀ s e env bt,
  determine_bt_from_expr_helper s e env = Some bt →
  has_type s env e bt.
Proof with eauto.
  intros s e.
  induction e; intros; try discriminate; inversion H.
  - destruct (nth_option env n).
    + inversion H1. subst. apply T_Var. assumption.
    + discriminate.
  - inversion H1. subst. constructor.
  - destruct ((find' (λ (x : basic_type * nat) (y : nat), snd x =? y) s n)) eqn: Heq; simpl in *.
    + inversion H1. subst. apply T_Column. auto.
    + discriminate.
  - destruct (determine_bt_from_expr_helper s e0 (e :: env)) eqn: Heq.
    + simpl in H1. inversion H1. subst. apply T_Abs. apply IHe...
    + discriminate.
  - destruct (determine_bt_from_expr_helper s e1 env) eqn: Heq1;
    destruct (determine_bt_from_expr_helper s e2 env) eqn: Heq2.
    + destruct e.
      * discriminate.
      * destruct (expr_type_eqb e3 e0) eqn: Heq3.
        -- inversion H1. subst. eapply T_App; eauto.
           eapply IHe2. apply expr_type_eqb_eq_iff in Heq3. subst. assumption.
        -- discriminate.
    + destruct e; discriminate. 
    + discriminate.
    + discriminate.
  
Admitted.

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
           specialize IHo1 with (c1 := (config_output (RelationWrapped s r') (⟨ db' Γ' β' p' ⟩))) (c2 := config_error).
           apply IHo1 in H9.
           ++ discriminate.
           ++ assumption.
        -- inversion H0; subst.
           specialize IHo2 with (c1 := config_error) (c2 := (config_output (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
           apply IHo2 in H11.
           ++ discriminate.
           ++ assumption.
      * inversion H0; subst; try discriminate.
        inversion H8. subst.
        (* The contradiction occurs when s1 ≠ s2 where s = s1 ∧ s = s2. *)
        specialize IHo1 with (c1 := (config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩)))
                             (c2 := (config_output (RelationWrapped s r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩))).
        specialize IHo2 with (c1 := (config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩)))
                             (c2 := (config_output (RelationWrapped s r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩))).
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
           specialize IHo1 with (c1 := (config_output (RelationWrapped s r') (⟨ db' Γ' β' p' ⟩))) (c2 := config_error).
           apply IHo1 in H9.
           ++ discriminate.
           ++ assumption.
        -- inversion H; subst.
           specialize IHo2 with (c1 := config_error) (c2 := (config_output (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
           apply IHo2 in H11.
           ++ discriminate.
           ++ assumption.
      * inversion H; subst; try discriminate.
        inversion H8. subst.
        (* The contradiction occurs when s1 ≠ s2 where s = s1 ∧ s = s2. *)
        specialize IHo1 with (c1 := (config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩)))
                             (c2 := (config_output (RelationWrapped s r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩))).
        specialize IHo2 with (c1 := (config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩)))
                             (c2 := (config_output (RelationWrapped s r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩))).
        apply IHo2 in H7. inversion H7. subst.
        apply IHo1 in H5. inversion H5. subst.
        -- exfalso. apply H9. reflexivity.
        -- assumption.
        -- assumption.
    + inversion H0; subst; try discriminate.
    + inversion H; inversion H0; subst; try discriminate.
      * inversion H8. subst. inversion H4. subst. assumption.
      * inversion H16. subst.
        specialize IHo2 with (c1 := (config_output (RelationWrapped s0 r''0) (⟨ db''0 Γ''0 β''0 p''0 ⟩)))
                             (c2 := (config_output (RelationWrapped s r'') (⟨ db'' Γ'' β'' p'' ⟩))).
        specialize IHo1 with (c1 := (config_output (RelationWrapped s0 r'0) (⟨ db'0 Γ'0 β'0 p'0 ⟩)))
                             (c2 := (config_output (RelationWrapped s r') (⟨ db' Γ' β' p' ⟩))).
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
      apply (IHo1 (config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩))) in H15.
      apply (IHo2 (config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H17.
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
      apply (IHo1 (config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩))) in H16.
      apply (IHo2 (config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H18.
      inversion H16. inversion H18. subst.
      apply inj_pair2_eq_dec in H3, H12; subst. 
      * eapply relation_join_by_prv_deterministic with (res2 := None) in H10.
        inversion H10. assumption.
      * apply list_eq_dec; apply attribute_eq_dec.
      * apply list_eq_dec; apply attribute_eq_dec.
      * assumption.
      * assumption.
    + apply (IHo1 (config_output (RelationWrapped s1 r') (⟨ db' Γ' β' p' ⟩))) in H16.
      apply (IHo2 (config_output (RelationWrapped s2 r'') (⟨ db'' Γ'' β'' p'' ⟩))) in H18.
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
    exists (config_output (RelationWrapped nil nil) (⟨ d c b p ⟩)).
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
          exists (config_output (RelationWrapped s (r ++ r0)) (⟨ d1 merged_Γ merged_β merged_p ⟩)).
          econstructor; try reflexivity; eauto.
        -- exists config_error. eapply E_UnionSchemaError with (s1 := s) (s2 := s0); try eauto.
      * (* There should be no rule for constructing nested output. *)
        inversion H1; subst; try discriminate.

Admitted.

End Facts.
