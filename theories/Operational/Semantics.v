Require Import Arith.
Require Import Arith.Compare.
Require Import Lia.
Require Import List.
Require Import ListSet.
Require Import Logic.Eqdep_dec Logic.EqdepFacts.
Require Import String.
Require Import Unicode.Utf8.

Require Import Base.Config.
Require Import Base.Lattice.
Require Import Base.Ordering.
Require Import Base.Trace.
Require Import Base.Types.
Require Import Base.Util.

Require Import Data.DataModel.
Require Import Data.Relation.

Require Import Operational.Expression.

(* A typing environment `Γ ⊢ ...` for evaluating the schema. *)
Definition ty_env := (list expr_type)%type.

Inductive project_list: Type :=
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
Fixpoint determine_bt_from_expr_helper (s: schema) (arg: expression) (env: ty_env):
  option expr_type :=
    match arg with
    (* For constants, we already know its type. *)
    | ExprConst bt _ => Some (ExprTypeBasic bt)
    (* For columns, we need to extract it from the schema. *)
    | ExprCol n =>
        let bt := find' (fun x y => (snd x) =? y) s n in
          option_map (fun x => ExprTypeBasic (fst x)) bt
    (*
      For binary operations, we need to evaluate the two arguments and check if their types match and
      the operation type is correct.
    *)
    | ExprBinary op x y =>
        match determine_bt_from_expr_helper s x env, determine_bt_from_expr_helper s y env with
          | Some τ1, Some τ2 =>
            match op with
              | BinFunc op _ _ _ _ =>
                match op with
                | Arithmetic _ =>
                  if expr_type_eqb τ1 (ExprTypeBasic IntegerType) then
                    if expr_type_eqb τ2 (ExprTypeBasic IntegerType) then
                      Some (ExprTypeBasic IntegerType)
                    else None
                  else None
                | Comparison _ =>
                  if expr_type_eqb τ1 τ2 then Some (ExprTypeBasic BoolType) else None
                | Logical _ =>
                  if expr_type_eqb τ1 (ExprTypeBasic BoolType) then
                    if expr_type_eqb τ2 (ExprTypeBasic BoolType) then
                      Some (ExprTypeBasic BoolType)
                    else None
                  else None
              end
            end
          | _, _ => None
        end
    | ExprUnary op x =>
        match determine_bt_from_expr_helper s x env with
          | Some τ =>
            match op with
              | UnaryFunc op _ ty _ =>
                if expr_type_eqb τ (ExprTypeBasic ty) then
                  match op with
                  | Not =>
                    if expr_type_eqb τ (ExprTypeBasic BoolType) then
                      Some (ExprTypeBasic BoolType)
                    else None
                  | _ =>
                    if expr_type_eqb τ (ExprTypeBasic ty) then
                      Some (ExprTypeBasic IntegerType)
                    else None
                  end
                else None
            end
          | _ => None
        end
    | ExprAgg op x =>
        match determine_bt_from_expr_helper s x env with
          | Some τ =>
            match op with
            | AggFunc _ _ τ _ _ _ => Some (ExprTypeBasic τ)
            end
          | _ => None
        end
    | ExprUDFSingleArg _ ret _ _ _ | ExprUDF _ ret _ _ _ => Some (ExprTypeBasic ret)
    end.

Definition determine_bt_from_expr (s: schema) (arg: expression): option basic_type :=
  match determine_bt_from_expr_helper s arg nil with
    | Some (ExprTypeBasic bt) => Some bt
    | _ => None
  end.

Fixpoint determine_schema (s: schema) (pl: list (expression * nat)): option schema :=
  match pl with
  | nil => Some nil
  | (expr, name) :: ℓ' =>
      match determine_bt_from_expr s expr with
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
        | (expr, name) :: ℓ' =>
          match determine_bt_from_expr s expr with
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
    | hd :: tl => (ExprCol n, snd hd) :: f tl (S n)
    end
  in project (f s 0).

Definition project_list_preprocess (s: schema) (pl: project_list): project_list :=
  match pl with
    | project_star => project_all s
    | _ => pl
  end.

Theorem project_list_preprocess_neq_star:
  ∀ s pl, ∃ pl', project_list_preprocess s pl = project pl'.
Proof.
  destruct pl.
  - simpl.
    exists (let f := fix f s n :=
      match s with
      | nil => nil
      | hd :: tl => (ExprCol n, snd hd) :: f tl (S n)
      end
    in (f s 0)).
    reflexivity.
  - exists l. reflexivity.
Qed.

(* This first creates for each tuple a `GroupbyProxy` which can later be `gathered` for our convenience. *)
Definition get_group_proxy_helper s (r: relation s) (gb_keys: groupby_list) (bounded: bounded_list s gb_keys):
  list groupby :=
  let gb_keys_extracted := (extract_columns s r gb_keys bounded) in
    (fix create_group_proxy keys n :=
      match keys with
      | nil => nil
      | hd :: tl => GroupbyProxy _ _ r hd (n :: nil) :: (create_group_proxy tl (S n))
      end
    ) gb_keys_extracted 0.

(*
  @param s The schema of the relation.
  @param r The relation from which the groupby elements are to be extracted.
  @param gb_keys The list of keys that define the grouping.
  @param bounded The bounded list that restricts the grouping.
  @returns list groupby The list of groupby elements extracted from the relation.

  The `get_group_proxy` function extracts a list of groupby elements from a given relation based
  on a list of groupby keys and group indices. The groupby keys define the grouping.
*)
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
          | GroupbyProxy _ s1 _ key indices, GroupbyProxy _ s2 _ key' indices' =>
            match list_eq_dec basic_type_eq_dec s1 s2 with
            | left eq => 
              if (Tuple.tuple_value_eqb _ key' (eq ♯ key)) then
                (GroupbyProxy s s1 r key (indices ++ indices'):: gather elem tl)
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
  (* ∅  *)
  | operator_empty: operator
  (* `nat` means the index of the relation it wants to access the n-th dataset inside `db`. *)
  (* R *)
  | OperatorRel: nat → operator
  (* e_1 ∪ e_2 *)
  | OperatorUnion: operator → operator → operator
  (* e_1 ⋈ e_2 *)
  | OperatorJoin: operator → operator → operator
  (* Πₐ(e) *)
  | OperatorProject: project_list → operator → operator
  (* σₗ(e) *)
  | OperatorSelect: expression → operator → operator
  (* γ(e) *)
  | OperatorGroupByHaving: groupby_list → agg_list → expression → operator → operator
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

(*
  Apply *one* expression on the relation.

  This works by iterating over the relation and applying the expression on *each tuple*, and
  the evaluation context for the expression contains that specific tuple.

  The result of the evaluation is only a relation that contain only *one* attribute.
*)
Inductive eval_expr_in_relation (s: schema) (r: relation s) ty:
  budget → trace → expression →
    option (relation (ty :: nil) * budget * trace) → Prop :=
  | E_EvalExprInRelationNil: ∀ β tr e,
      r = nil →
      eval_expr_in_relation s r ty β tr e (Some (nil, β, tr))
  | E_EvalExprInRelationHdError: ∀ β tr e hd tl,
      r = hd :: tl →
      eval_expr false (β, tr) (TupleWrapped s hd) None e None →
      eval_expr_in_relation s r ty β tr e None
  | E_EvalExprInRelationTlError: ∀ hd tl β tr e,
      r = hd :: tl →
      eval_expr_in_relation s tl ty β tr e None →
      eval_expr_in_relation s r ty β tr e None
  | E_EvalExprInRelationOk: ∀ bt' β β'  β'' tr tr' tr'' hd hd' id tl tl' e env' tp gb,
      r = hd :: tl →
      eval_expr false (β, tr) (TupleWrapped s hd) None e (Some (env', ValuePrimitive bt' (hd', id))) →
      env' = (β', tr', tp, gb) →
      ∀ (eq: bt' = (fst ty)),
      eval_expr_in_relation s tl ty β' tr' e (Some (tl', β'', tr'')) →
      let res := (eq ♯ hd', (unwrap_or_default id 0), tt) :: ((tuple_single_eq (ty :: nil) ty eq_refl) ♯ tl') in
        let res' := eq_sym (tuple_single_eq (ty :: nil) ty eq_refl) ♯ res in
          eval_expr_in_relation s r ty β tr e (Some (res', β'', tr''))
.

(*
  @param s The schema of the input relation.
  @param s' The **schema of the output** relation after projection.
  @param r The input relation on which the projection is to be applied.
  @param ℓ The list of expressions and their corresponding column indices that form the projection.
  @param budget The budget for the operation.
  @param trace The provenance context.
  @returns option (relation s' *  budget * trace) The expected result of the operation.

  Apply each project expression on the given relation `r`.

  This works as follows:

  - If the projection list is empty or the relation is empty, we just do nothing.
  - If the projection list is not empty, we evaluate each expression in the list.
    - Evaluation will further invoke `eval_expr_in_relation` (for readability).
*)
Inductive apply_proj_in_relation (s s': schema) (r: relation s) (ℓ: list (expression * nat)):
  budget → trace →
    option (relation s' * budget * trace) → Prop :=
  (* Either the projection list is empty or the relation is empty. As such, we just do nothing here. *)
  | E_ApplyElemEmpty: ∀ β tr,
      ℓ = nil ∨ r = nil ∨ s' = nil →
      apply_proj_in_relation s s' r ℓ β tr (Some (nil, β, tr))
  | E_ApplyElemErrHead: ∀ β tr hd tl s_hd s_tl,
      ℓ = hd :: tl →
      s' = s_hd :: s_tl →
      eval_expr_in_relation s r s_hd β tr (fst hd) None →
      apply_proj_in_relation s s' r ℓ β tr None
  | E_ApplyElemErrTail: ∀  hd tl β tr,
      ℓ = hd :: tl →
      apply_proj_in_relation s s' r tl β tr None →
      apply_proj_in_relation s s' r ℓ β tr None
  | E_ApplyElemOk: ∀ s_hd s_tl β β' β'' tr tr' tr'' hd hd' tl tl'
                (proj_case: ℓ = hd :: tl),
      r ≠ nil →
      ∀ (s_case: s' = s_hd :: s_tl),
        eval_expr_in_relation s r (fst s_hd, snd hd) β tr (fst hd) (Some (hd', β', tr')) →
        apply_proj_in_relation s s_tl r tl β' tr' (Some (tl',  β'', tr'')) →
        (*
          Goal:
          (((fst s_hd, snd hd) :: nil) ++ s_tl) = s'
        *)
        let col := (relation_product _ _ hd' tl') in
        let res := ((Tuple.schema_flat_2nd_arg_irrelevant_tuple s' _ _ _ s_case) ♯ col) in
          apply_proj_in_relation s s' r ℓ β tr (Some (res, β'', tr''))
.

(*
  @param s The schema of the relation.
  @param r The relation in which the predicate is to be evaluated.
  @param budget The budget for the evaluation.
  @param trace The provenance context.
  @param expression The predicate to be evaluated.
  @param option (relation s *  budget * trace) The expected result of the evaluation.
  @returns Prop A proposition that is true if the evaluation is correctly applied, false otherwise.

  The `eval_predicate_in_relation` inductive type represents the evaluation of a predicate in a relation.
  The evaluation is performed in the context of a given policy context and provenance context, and it may
  consume a certain amount of budget. If the evaluation is successful, the function returns `Some` with a
  tuple containing the resulting relation, the updated policy context, the remaining budget, and the up-
  dated provenance context. The predicate is checked against each tuple in the relation.

  ** This must not involve `having` which is handled elsewhere.
*)
Inductive eval_predicate_in_relation (s: schema) (r: relation s):
 budget → trace → expression →
    option (relation s * budget * trace) → Prop :=
  | E_EvalExprRelationNil: ∀ β tr e,
      r = nil →
      eval_predicate_in_relation s r β tr e (Some (nil, β, tr))
  | E_EvalExprConsTrue: ∀ β β' β'' tr tr' tr'' e env hd tl tl' id,
      r = hd :: tl →
      eval_expr false (β, tr) (TupleWrapped s hd) None e (Some (env, ValuePrimitive BoolType (true, id))) →
      fst (fst env) = (β', tr') →
      eval_predicate_in_relation s tl β' tr' e (Some (tl', β'', tr'')) →
      eval_predicate_in_relation s r β tr e (Some (hd :: tl', β'', tr))
  | E_EvalExprConsFalse: ∀  β β' β'' tr tr' tr'' e env hd tl tl' id,
      r = hd :: tl →
      eval_expr false (β, tr) (TupleWrapped s hd) None e (Some (env, ValuePrimitive BoolType (false, id))) →
      fst (fst env) = (β', tr') →
      eval_predicate_in_relation s tl β' tr' e (Some (tl', β'', tr'')) →
      eval_predicate_in_relation s r β tr e (Some (tl', β'', tr))
  | E_EvalError: ∀ res v β tr e env hd tl,
      r = hd :: tl →
      eval_expr false (β, tr) (TupleWrapped s hd) None e (Some (env, res)) →
      res ≠ ValuePrimitive BoolType v →
      eval_predicate_in_relation s r β tr e None
  | E_EvalError2: ∀ β β' tr tr' e hd tl env v,
      r = hd :: tl →
      eval_expr false (β, tr) (TupleWrapped s hd) None e (Some (env, ValuePrimitive BoolType v)) →
      fst (fst env) = (β', tr') →
      eval_predicate_in_relation s tl β' tr' e None →
      eval_predicate_in_relation s r β tr e None
.

(*
  @param bt The basic type of the elements in the resulting list of tuples.
  @param budget The budget available for the operation.
  @param trace The provenance context for the operation.
  @param list groupby The list of groupby elements on which the aggregation operation is applied.
  @param expression The aggregation operation to be applied.
  @param option (list (Tuple.tuple (bt :: nil)) *  budget * trace) The expected result of the operation.

  This evaluates the aggregate expression on a given group.
*)
Inductive apply_fold_on_groups_once: ∀ bt, budget → trace → list groupby → expression →
  option (list (Tuple.tuple (bt :: nil)) * budget * trace) → Prop :=
  | E_ApplyFoldOnGroupsOnceNil: ∀ bt β tr gb e,
      gb = nil →
      apply_fold_on_groups_once bt β tr gb e (Some (nil, β, tr))
  | E_ApplyFoldOnGroupsHdError: ∀ bt β tr tp gb hd tl e,
      gb = hd :: tl →
      (*
        We have to set `in_agg` to false here to avoid confusion; this bit is set only when we are
        evaluating the argument of a fold operation.
       *)
      eval_expr false (β, tr) tp (Some hd) e None →
      apply_fold_on_groups_once bt β tr gb e None
  | E_AplpyFoldOnGroupConsError: ∀ bt β β' tr tr' tp gb hd tl e env res,
      gb = hd :: tl →
      eval_expr false (β, tr) tp (Some hd) e (Some (env, res)) →
      fst (fst env) = (β', tr') →
      apply_fold_on_groups_once bt β' tr' tl e None →
      apply_fold_on_groups_once bt β tr gb e None
  | E_ApplyFoldOnGroupsOk: ∀ bt β β' β'' tr tr' tr'' tp gb hd tl e env v res id res',
      gb = hd :: tl →
      (* Evalautes the expression. *)
      eval_expr false (β, tr) tp (Some hd) e (Some (env, v)) →
      fst (fst env) = (β', tr') →
      v = ValuePrimitive bt (res, id) →
      apply_fold_on_groups_once bt β' tr' tl e (Some (res', β'', tr'')) →
      apply_fold_on_groups_once bt β tr gb e (Some ((res, (unwrap_or_default id 0), tt) :: res', β'', tr''))
.

(*
  @param s, s_gb The schemas of the input and output relations.
  @param budget The budget available for the operation.
  @param trace The provenance context for the operation.
  @param list (GroupbyProxy s_gb) The list of groupby elements on which the aggregation operations are applied.
  @param agg_list The list of aggregation operations to be applied.
  @param relation s The initial relation on which the operations are performed.
  @param option (relation s *  budget * trace) The expected result of the operation.

  The `apply_fold_on_groups` represents the application of a list of aggregation operations on a list of
  groupby elements. This operation is performed within a given policy context and provenance context, and
  it may consume a certain amount of budget. 
*)
Inductive apply_fold_on_groups: schema → budget → trace → list groupby → agg_list →
  option (relation_wrapped * budget * trace) → Prop :=
  | E_ApplyFoldOnGroupNilAggList: ∀ s β tr gb agg,
      agg = nil ∨ s = nil →
      apply_fold_on_groups s β tr gb agg (Some (RelationWrapped s nil, β, tr))
  | E_ApplyFoldOnGroupHeadError: ∀ s s_hd s_tl β tr gb agg agg_hd agg_tl,
      agg = agg_hd :: agg_tl →
      s = s_hd :: s_tl →
      apply_fold_on_groups_once (fst s_hd) β tr gb (fst agg_hd) None →
      apply_fold_on_groups s β tr gb agg None
  | E_ApplyFoldOnGroupTailError: ∀ s s_hd s_tl β β' tr tr' gb agg agg_hd agg_tl,
      agg = agg_hd :: agg_tl →
      s = s_hd :: s_tl →
      apply_fold_on_groups_once (fst s_hd) β tr gb (fst agg_hd) (Some (nil, β', tr')) →
      apply_fold_on_groups s_tl β' tr' gb agg_tl None →
      apply_fold_on_groups s β tr gb agg None
  | E_ApplyFoldOnGroupOk: ∀ s s_hd s_tl β β' β'' tr tr' tr'' gb agg agg_hd agg_tl res res',
      agg = agg_hd :: agg_tl →
      s = s_hd :: s_tl →
      apply_fold_on_groups_once (fst s_hd) β tr gb (fst agg_hd) (Some (res, β', tr')) →
      apply_fold_on_groups s_tl β' tr' gb agg_tl (Some (RelationWrapped s_tl res', β'', tr'')) →
      let output := relation_product ((fst s_hd, snd agg_hd) :: nil) s_tl res res' in
        apply_fold_on_groups s β tr gb agg (Some (RelationWrapped _ output, β', tr'))
.

(*
  @param list groupby The list of groupby elements to be evaluated.
  @param expression The having clause to be evaluated.
  @param budget The budget for the evaluation.
  @param trace The provenance context.
  @param option (list groupby *  budget * trace) The expected result of the evaluation.
  @returns Prop A proposition that is true if the evaluation is correctly applied, false otherwise.

  The `eval_groupby_having` inductive type represents the evaluation of a having clause on a list of groupby
  elements. A having clause is a predicate that is evaluated on the result of a groupby operation.

  # Examples

  ```
  let gb = [0, 1];
  let having = (λ x: x, > "count"(x) 6) (col 2);
  ```
*)
Inductive eval_groupby_having:
  list groupby → expression → budget → trace →
    option (list groupby * budget * trace) → Prop :=
  | E_EvalGroupByHavingNil: ∀ gb β tr e,
      gb = nil →
      eval_groupby_having gb e β tr (Some (nil, β, tr))
  | E_EvalGroupByHavingHeadFalse: ∀ t gb hd tl β β' tr tr' e env id res,
      gb = hd :: tl →
      eval_expr true (β, tr) t (Some hd) e (Some (env, ValuePrimitive BoolType (false, id))) →
      fst (fst env) = (β', tr') →
      eval_groupby_having tl e β' tr' res →
      eval_groupby_having gb e β tr res
  | E_EvalGroupByHavingHeadTrue: ∀ t gb hd tl β β' β'' tr tr' tr'' e env id res,
      gb = hd :: tl →
      eval_expr true (β, tr) t (Some hd) e (Some (env, ValuePrimitive BoolType (true, id))) →
      fst (fst env) = (β', tr') →
      eval_groupby_having tl e β' tr' (Some (res, β'', tr'')) →
      eval_groupby_having gb e β tr (Some (hd :: res, β'', tr''))
  | E_EvalGroupByHavingHeadError1: ∀ t gb hd tl β tr e,
      gb = hd :: tl →
      eval_expr true (β, tr) t (Some hd) e None →
      eval_groupby_having gb e β tr None
  | E_EvalGroupByHavingHeadError2: ∀ t gb hd tl β β' tr tr' e env id,
      gb = hd :: tl →
      eval_expr true (β, tr) t (Some hd) e (Some (env, ValuePrimitive BoolType id)) →
      fst (fst env) = (β', tr') →
      eval_groupby_having tl e β tr' None →
      eval_groupby_having gb e β tr None
.

(* We should invoke `eval_expr` to get the result. *)
Inductive eval_aggregate:
  ∀ s s_agg gb, bounded_list s gb → agg_list → expression → budget → trace → relation s →
    option (relation s_agg * budget * trace) → Prop :=
  | E_EvalAggregate: ∀ s s_agg β β' β'' tr tr' tr'' gb (bounded: bounded_list s gb)
                      gb_proxy agg f r r' res,
      let gb_proxy_raw := get_group_proxy s r gb bounded in
        (* We do a filtering here. *)
        eval_groupby_having gb_proxy_raw f β tr (Some (gb_proxy, β', tr')) →
        apply_fold_on_groups s β' tr' gb_proxy agg res →
        res = Some (RelationWrapped s_agg r', β'', tr'') →
        eval_aggregate s s_agg gb bounded agg f β tr r (Some (r', β'', tr''))
  | E_EvalAggregateError: ∀ s s_agg β β' tr tr' gb (bounded: bounded_list s gb)
                      gb_proxy agg r f,
      let gb_proxy_raw := get_group_proxy s r gb bounded in
        (* We do a filtering here. *)
        eval_groupby_having gb_proxy_raw f β tr (Some (gb_proxy, β', tr')) →
        apply_fold_on_groups s β' tr' gb_proxy agg None →
        eval_aggregate s s_agg gb bounded agg f β tr r None
  | E_EvalAggregateGroupByError: ∀ s s_agg β tr gb agg f r (bounded: bounded_list s gb),
      let gb_proxy_raw := get_group_proxy s r gb bounded in
        eval_groupby_having gb_proxy_raw f β tr None →
        eval_aggregate s s_agg gb bounded agg f β tr r None
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

  db, o -> r, tr
*)
Reserved Notation "'⟦' db op '⟧' '⇓' '⟦' c '⟧'"
  (at level 10, db at next level, op at next level, c at next level).
Inductive step_config: (database * operator) → config → Prop :=
  (* Empty operator returns nothing and does not affect the configuration. *)
  | E_Empty: ∀ c db,
      c = ConfigOut (RelationWrapped nil nil) 0 nil →
      ⟦ db operator_empty ⟧ ⇓ ⟦ c ⟧
  (* Getting the relation is an identity operation w.r.t. configurations. *)
  | E_GetRelation: ∀ c db o n r β tr,
      o = OperatorRel n →
      database_get_contexts db n = Some (r, tr, β) →
      let Γ := List.map (λ x, (fst x, extract_policy (snd x))) tr in 
        Policy.policy_context_valid Γ →
        c = ConfigOut r β tr →
        ⟦ db (OperatorRel n) ⟧ ⇓ ⟦ c ⟧
  | E_GetRelationNotValid: ∀ c db o n r β tr,
      o = OperatorRel n →
      database_get_contexts db n = Some (r, tr, β) →
      let Γ := List.map (λ x, (fst x, extract_policy (snd x))) tr in 
      ¬ Policy.policy_context_valid Γ →
      c = ConfigOut r β tr →
      ⟦ db (OperatorRel n) ⟧ ⇓ ⟦ ConfigError ⟧
  (* The given relation index is not found in the database. *)
  | E_GetRelationError: ∀ c db o n,
      o = OperatorRel n →
      database_get_contexts db n = None →
      c = ConfigError →
      ⟦ db (OperatorRel n) ⟧ ⇓ ⟦ c ⟧
  (* If the operator returns an empty relation, we do nothing. *)
  | E_ProjEmpty: ∀ c db σ t s r o pl,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ → 
      c = ConfigOut (RelationWrapped s r) σ t →
      r = nil ∨ s = nil →
      ⟦ db (OperatorProject pl o) ⟧ ⇓ ⟦ c ⟧
  (* If the operator returns a valid relation, we can then apply projection. *)
  | E_ProjOk: ∀ c c' db pl pl' s s'
               β β' tr tr' r r' o,
      (* We first evaluate the inner operator and get the output. *)
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      (* We then destruct the output. *)
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      (* We do a simple preprocess. *)
      project pl' = project_list_preprocess s pl →
      Some s' = determine_schema s pl' →
        (* We then apply projection inside the environment. *)
          apply_proj_in_relation s s' r pl' β tr (Some (r', β', tr')) →
          c' = ConfigOut (RelationWrapped _ r') β' tr' →
          ⟦ db (OperatorProject pl o) ⟧ ⇓ ⟦ c' ⟧
  (*
     If the operator returns a valid environment, we can then apply projection. Then if the
     projection fails, we return `ConfigError`.
  *)
  | E_ProjError: ∀ c db pl pl' s s' β r tr o,
      (* We first evaluate the inner operator and get the output. *)
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      (* We then destruct the output. *)
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      (* We do a simple preprocess. *)
      project pl' = project_list_preprocess s pl →
      Some s' = determine_schema s pl' →
        (* We then apply projection inside the environment. *)
        apply_proj_in_relation s s' r pl' β tr None →
        ⟦ db (OperatorProject pl o) ⟧ ⇓ ⟦ ConfigError ⟧
  (*
     If the operator returns a valid environment, we can then apply projection. Then if the
     projection fails, we return `ConfigError`.
  *)
  | E_ProjError2: ∀ db pl o,
      (* We first evaluate the inner operator and get the output. *)
      ⟦ db o ⟧ ⇓ ⟦ ConfigError ⟧ →
      ⟦ db (OperatorProject pl o) ⟧ ⇓ ⟦ ConfigError ⟧
  (*
     If we the project list is itself wrongly typed, we return error.
  *)
  | E_ProjError3: ∀ c db pl pl' s β tr r o,
      (* We first evaluate the inner operator and get the output. *)
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      (* We then destruct the output. *)
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      (* We do a simple preprocess. *)
      project pl' = project_list_preprocess s pl →
      None = determine_schema s pl' →
      ⟦ db (OperatorProject pl o) ⟧ ⇓ ⟦ ConfigError ⟧ 
  | E_SelectError: ∀ c db β s r tr o expr,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      eval_predicate_in_relation s r β tr expr None →
      ⟦ db (OperatorSelect expr o) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_SelectError2: ∀ db o expr,
      ⟦ db o ⟧ ⇓ ⟦ ConfigError ⟧ →
      ⟦ db (OperatorSelect expr o) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_SelectError3: ∀ c db β s1 s2 r tr o expr,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s2 r) β tr →
      s1 ≠ s2 →
      ⟦ db (OperatorSelect expr o) ⟧ ⇓ ⟦ ConfigError ⟧
   | E_SelectOk: ∀ c c' db β β' s r r' tr tr' o expr,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
        eval_predicate_in_relation s r β tr expr (Some (r', β', tr')) →
        c' = ConfigOut (RelationWrapped s r') β' tr' →
        ⟦ db (OperatorSelect expr o)⟧ ⇓ ⟦ c' ⟧
  | E_UnionError: ∀ c c' db o1 o2,
      ⟦ db o1 ⟧ ⇓ ⟦ c ⟧ →
      ⟦ db o2 ⟧ ⇓ ⟦ c' ⟧ →
      c = ConfigError ∨ c' = ConfigError →
      ⟦ db (OperatorUnion o1 o2) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_UnionSchemaError: ∀ c c' db β β' s1 s2 r r' tr tr' o1 o2,
      ⟦ db o1 ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s1 r) β tr →
      ⟦ db o2 ⟧ ⇓ ⟦ c' ⟧ →
      c' = ConfigOut (RelationWrapped s2 r') β' tr' →
      s1 ≠ s2 →
      ⟦ db (OperatorUnion o1 o2) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_UnionOk: ∀ c c'  db β β' s r r' tr tr' merged_tr o1 o2,
      ⟦ db o1 ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      ⟦ db o2 ⟧ ⇓ ⟦ c' ⟧ →
      c' = ConfigOut (RelationWrapped s r') β' tr' →
      tr ⊍ tr' = merged_tr →
      (*
        We ensure that cells are always assigned new ids;
        so it is safe for us to just append them together.
      *)
      let merged_β := calculate_budget β β' in
      ⟦ db (OperatorUnion o1 o2) ⟧ ⇓
      ⟦ ConfigOut (RelationWrapped s (r ++ r')) merged_β merged_tr ⟧
  | E_JoinError: ∀ c c' db o1 o2,
      ⟦ db o1 ⟧ ⇓ ⟦ c ⟧ →
      ⟦ db o2 ⟧ ⇓ ⟦ c' ⟧ →
      c = ConfigError ∨ c' = ConfigError →
      ⟦ db (OperatorJoin o1 o2) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_JoinError2: ∀ c c' db β β' s1 s2 r r' tr tr' o1 o2,
      ⟦ db o1 ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s1 r) β tr →
      ⟦ db o2 ⟧ ⇓ ⟦ c' ⟧ →
      c' = ConfigOut (RelationWrapped s2 r') β' tr' →
      let join_by := (natural_join_list s1 s2) in
        (relation_join_by_prv s1 s2 join_by r r' β β' tr tr') None →
        ⟦ db (OperatorJoin o1 o2) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_JoinOk: ∀ c c' db β β' βout s1 s2 r r' r'' tr tr' trout rout o1 o2,
      ⟦ db o1 ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s1 r) β tr →
      ⟦ db o2 ⟧ ⇓ ⟦ c' ⟧ →
      c' = ConfigOut (RelationWrapped s2 r') β' tr' →
      let join_by := (natural_join_list s1 s2) in
        (relation_join_by_prv s1 s2 join_by r r' β β' tr tr')
        (Some (rout, βout, trout)) →
        r'' = RelationWrapped _ rout →
        ⟦ db (OperatorJoin o1 o2) ⟧ ⇓ ⟦ ConfigOut r'' βout trout ⟧
  | E_AggEmpty: ∀ c db β o s r tr gb agg f,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      s = nil ∨ r = nil →
      ⟦ db (OperatorGroupByHaving gb agg f o) ⟧ ⇓ ⟦ c ⟧
  | E_AggError: ∀ db o gb agg f,
      ⟦ db o ⟧ ⇓ ⟦ ConfigError ⟧ →
      ⟦ db (OperatorGroupByHaving gb agg f o) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_AggNotBounded: ∀ s c db β o r tr gb agg f,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      ¬ bounded_list s gb →
      ⟦ db (OperatorGroupByHaving gb agg f o) ⟧ ⇓ ⟦ ConfigError ⟧
   | E_AggSchemaError: ∀ c db β s r tr gb agg o f,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      ∀ (bounded: bounded_list s gb),
        None = determine_schema_agg s agg gb bounded →
        ⟦ db (OperatorGroupByHaving gb agg f o) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_AggFail: ∀ c db β s s_agg r tr gb agg o f,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      ∀ (bounded: bounded_list s gb),
        Some s_agg = determine_schema_agg s agg gb bounded →
        eval_aggregate s s_agg gb bounded agg f β tr r None →
        ⟦ db (OperatorGroupByHaving gb agg f o) ⟧ ⇓ ⟦ ConfigError ⟧
  | E_AggOk: ∀ c c' db β β' s s_agg r r' tr tr' gb agg o f,
      ⟦ db o ⟧ ⇓ ⟦ c ⟧ →
      c = ConfigOut (RelationWrapped s r) β tr →
      s ≠ nil ∧ r ≠ nil →
      ∀ (bounded: bounded_list s gb),
        Some s_agg = determine_schema_agg s agg gb bounded →
          eval_aggregate s s_agg gb bounded agg f β tr r (Some (r', β', tr')) →
          c' = ConfigOut (RelationWrapped s_agg r') β' tr' →
          ⟦ db (OperatorGroupByHaving gb agg f o) ⟧ ⇓ ⟦ c' ⟧
where "'⟦' c op '⟧' '⇓' '⟦' c' '⟧'" := (step_config (c, op) c').
Hint Constructors step_config: core.

Definition finalize (c: config): config :=
  match c with
  | ConfigError => c
  | ConfigOut r β tr =>
    let Γ := List.map (λ x, extract_policy (snd x)) tr in 
    (fix finalize' Γ :=
      match Γ with
        | nil => c
        | hd :: tl =>
            match hd with
              | ∎ | Policy.policy_bot ⇝ ∎ => finalize' tl
              | _ => ConfigError
            end
      end
    ) Γ
  end.