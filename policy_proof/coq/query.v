Require Import List.
Require Import String.
Require Import Unicode.Utf8.
Require Import Lia.

Require Import types.
Require Import relation.
Require Import formula.
Require Import data_model.
Require Import ordering.
Require Import lattice.
Require Import finite_bags.
Require Import util.
Require Import prov.

Set Printing Coercions.
Set Printing Implicit.
Set Printing Projections.

Inductive trans_func (ℓ1 ℓ2: Policy.policy): Set :=
  | trans_func_with_label: ∀ bt, transform_func bt → trans_func ℓ1 ℓ2
.

Definition trans_func_denote ℓ1 ℓ2 (f: trans_func ℓ1 ℓ2) : basic_type -> basic_type. Admitted.

Inductive project_list: Set :=
  (* Denotes a "*" projection list. *)
  | project_star: project_list
  (* Dentoes a project list consisting function applications, column names, and constants. *)
  | project: list (simple_atomic_expression) → project_list
.

Definition normalized (pl: project_list): Prop :=
  match pl with
  | project_star => False
  | project ℓ =>
      (fix check ℓ := match ℓ with
                      | nil => True
                      | x :: ℓ' => match x with
                                  | simple_atomic_expression_column _ => check ℓ'
                                  | simple_atomic_expression_const _ => check ℓ'
                                  | simple_atomic_expression_func _ ℓ'' => 
                                             (fix check' ℓ := match ℓ with
                                                        | nil => True
                                                        | cur :: ℓ' =>
                                                          match cur with
                                                          | simple_atomic_expression_column _ => check' ℓ'
                                                          | simple_atomic_expression_const _ => check' ℓ'
                                                          | _ => False
                                                          end
                                                        end) ℓ''
                                  end
                        end) ℓ
  end.

(*
  `determine_bt_from_args` is a function that takes a schema and a list of simple atomic expressions
  and returns a basic type. This function calculates the output basic type for a function application
  given the input schema and the list of simple atomic expressions.

  HACK: This function uses `option` which is inconsistent with the `nth` function in `Tuple.v`.
        `nth` requires a proof that the index is within the bounds of the list. However, this
        function does not require such a proof.

        The major difficulty is that we cannot easily obtain the proof that the bound is satisfied,
        although is might appear quite intuitive for us after the project list is normalized.

        We thus use `option` to avoid the proof obligation. This is a hack, though.
*)
Fixpoint determine_bt_from_args (s: schema) (ℓ: list simple_atomic_expression): option basic_type :=
  match ℓ with
  | nil => None
  | x :: ℓ' => match x with
                | simple_atomic_expression_column c => Tuple.nth_nocheck s c
                | simple_atomic_expression_const bt => Some bt
                | simple_atomic_expression_func _ _ => determine_bt_from_args s ℓ'
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
          | x :: ℓ' => match x with
                        | simple_atomic_expression_column c => 
                            match Tuple.nth_nocheck s c with
                              | Some bt => bt :: determine ℓ'
                              | None => determine ℓ'
                            end
                        | simple_atomic_expression_const bt => bt :: determine ℓ'
                        | simple_atomic_expression_func _ ℓ'' =>
                            match determine_bt_from_args s ℓ'' with
                              | Some bt => bt :: determine ℓ'
                              | None => determine ℓ'
                            end
                      end
          end) ℓ
  end.

(*
  `normalize_project_star` is a function that takes a schema and a natural number `n` and
  returns a list of simple atomic expressions. The list of simple atomic expressions is
  the same length as the schema. Each simple atomic expression is a function application
  of the identity function to a column name.

  For example, if we have a schema `(IntegerType :: StringType :: BoolType :: nil)%type`,
  then the result of `normalize_project_star` is:
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
  ::
  nil
  ```
*)
Fixpoint normalize_project_star (s: schema) (n: nat): list (simple_atomic_expression) :=
  match s with
    | nil => nil
    | _ :: s' =>
      (simple_atomic_expression_func stf_id
        (cons (simple_atomic_expression_column n) nil)
      )
          :: normalize_project_star s' (S n)
  end.

(* 
  `normalize_project_list_list` is a function that takes a schema and a list of simple atomic
  expressions and returns a list of simple atomic expressions. The list of simple atomic
  expressions is the same length as the schema.

  This function converts from
  - column names to function applications of the identity function to the column name,
  - constants to constants, and
  - functions to functions (by filtering) with only column names as arguments.
*)
Fixpoint normalize_project_list_list
  (s: schema) (pl: list (simple_atomic_expression)): list (simple_atomic_expression) :=
  match pl with
    | nil => nil
    | e :: pl' => match e with
                    | simple_atomic_expression_column c => 
                          (simple_atomic_expression_func stf_id
                            (cons (simple_atomic_expression_column c) nil)
                          ) :: normalize_project_list_list s pl'
                    | simple_atomic_expression_const _ => e:: normalize_project_list_list s pl'
                    (* Functions are special: because Coq requires that all recursive functions are
                       well-typed, we cannot normalize a function application since we do not know
                       the number of nested functions.

                       Consider:
                        ```
                        f1 (f2 (f3 (f4 (...))))
                        ```
                        This is ill-typed.

                        So we just assume that the functions are only 1-order; i.e., there is no
                        functions over functions: the hierarchy cannot be infinite.

                        This can be fixed, though. We can refine the constructor `simple_atomic_expression_func`
                        to be simple_atomic_expression_func:
                          ∀ bt, transform_func bt → 
                                list (∀ n, (n * simple_atomic_expression)) →
                                simple_atomic_expression
                        
                        Then we can let Coq know that `n` will reduce. This is a bit tricky.
                    *)
                    | simple_atomic_expression_func f ℓ =>
                        simple_atomic_expression_func f (List.filter (fun x => match x with
                                                                                | simple_atomic_expression_column _ => true
                                                                                | simple_atomic_expression_const _ => true
                                                                                | _ => false
                                                                              end) ℓ)
                          :: normalize_project_list_list s pl'
                  end
  end.

Lemma normalize_project_star_length: ∀ s n,
  List.length (normalize_project_star s n) = List.length s.
Proof.
  induction s.
  - auto.
  - intros. simpl.
    specialize IHs with (n := S n). rewrite <- IHs. auto.
Qed.

Example sample_schema: schema := (IntegerType :: StringType :: BoolType :: nil)%type.
Compute normalize_project_star sample_schema 0.

Definition normalize_project_list (s: schema) (pl: project_list): project_list :=
  match pl with
    | project_star => project (normalize_project_star s 0)
    | project ℓ => project (normalize_project_list_list s ℓ)
  end.

Lemma normalize_normalized: ∀ s pl, normalized (normalize_project_list s pl).
Proof.
  destruct pl.
  - induction s; simpl; auto.
  - induction l.
    + simpl. auto.
    + destruct a; simpl; auto.
      induction l0; simpl; auto with *.
      destruct a; simpl; auto.
Qed.

Definition groupby_list := (list nat)%type.
Definition agg_list s := (list (∀ bt, agg_expression s bt))%type.

Definition schema_env:= list (nat * schema)%type.
Fixpoint relation_env (se: schema_env): Set :=
  match se with
    | nil => unit
    | (_, s) :: se' => (relation s * relation_env se')%type
  end.

Fixpoint lookup_schema (n: nat) (se: schema_env): schema :=
  match se with
    | nil => nil
    | (n', s) :: se' => if Nat.eqb n n' then s else lookup_schema n se'
  end.

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
*)
Definition env_slice (s: schema) := ((relation s) * list nat * groupby_list * list (Tuple.tuple s))%type.

(* An environment is just a list of environment slices. *)
Definition ℰ (s: schema): Set := list (env_slice s)%type.

(* =============================== Some utility functions =================================== *)
Definition env_slice_get_relation {s} (e: env_slice s) : relation s :=
  match e with
    | (r, _, _, _) => r
  end.

Definition env_slice_get_selected {s} (e: env_slice s) : list nat :=
  match e with
    | (_, s, _, _) => s
  end.

Definition env_slice_get_groupby {s} (e: env_slice s) : groupby_list :=
  match e with
    | (_, _, g, _) => g
  end.

Definition env_slice_get_tuples {s} (e: env_slice s) : list (Tuple.tuple s) :=
  match e with
    | (_, _, _, t) => t
  end.

Definition get_env_slice s (e: ℰ s) (non_empty: List.length e > 0) : env_slice s.
  destruct e.
  - simpl in non_empty. lia.
  - exact e.
Defined.
(* ========================================================================================= *)

Inductive Operator: Set :=
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
Inductive config: Set :=
  | config_terminal: config
  | config_error: config
  | config_ok: ∀ s, Policy.context → Configuration.privacy → ℰ s → prov_ctx -> config
.

Notation "'⟨' s Γ β ℰ p '⟩'":= (config_ok s Γ β ℰ p)
  (at level 10, s at next level, Γ at next level, β at next level, ℰ at next level,
  p at next level,
  no associativity).

(*
  `step_cell` is an inductive type that defines a relation between two configurations except that
  it works on the level of cells. This transition is defined by a notation `c1 >[ f ]> c2` where `f`
  is a function that transforms the cell.
*)
Reserved Notation "c1 '>[' f ']>' c2" (at level 50, no associativity).
Inductive step_cell: ∀ ℓ1 ℓ2, trans_func ℓ1 ℓ2 → config → config → Prop :=
  (* If the environment is empty, then we cannot do anything.  *)
  | E_CTransSkip1:
      ∀ ℓ1 ℓ2 s Γ β e p (f: trans_func ℓ1 ℓ2), 
          List.length e = 0 →
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e p ⟩
  (* If the environment is not empty but there is no active tuples, we cannot do anything. *)
  | E_CTransSkip2:
      ∀ ℓ1 ℓ2 s Γ β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0) tl,
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          List.length tl = 0 → 
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e p ⟩
  (* The label does not flow to the current one. *)
  | E_CTransSkip3:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (ℓcur, Some ℓdisc) = Policy.label_lookup c_idx Γ →
          ~ (ℓcur ⊑ ℓ1) →
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e p ⟩
  (* No active labels are found; this should be an error. *)
  | E_CTransError1:
      ∀ ℓ1 ℓ2 s Γ β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          None = Policy.label_lookup c_idx Γ →
          ⟨ s Γ β e p ⟩ >[ f ]> config_error
  | E_CTransError2:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl (tl_non_empty: List.length tl > 0) t c c' c_idx (idx_bound: c_idx < List.length s),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (ℓcur, Some ℓdisc) = Policy.label_lookup c_idx Γ →
          (* udpate the policy environment. *)
          ℓcur ⊑ ℓ1 → Γ' = Policy.update_label c_idx Γ (ℓ2, Some ℓdisc) →
          (* update the cell *)
          c = Tuple.nth _ c_idx idx_bound → c' = (trans_func_denote _ _ f) c →
          (* update the tuple by updating this cell. *)
          None = Tuple.set_nth_type_match _ c_idx c' idx_bound t →
          (* update the environment. *)
          ⟨ s Γ β e p ⟩ >[ f ]> config_error
  (* This transition is ok. *)
  | E_CTransOk:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e e' p p' (f: trans_func ℓ1 ℓ2) (non_empty: List.length e > 0)
        tl tl' (tl_non_empty: List.length tl > 0) t t' c c' c_idx (idx_bound: c_idx < List.length s),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (ℓcur, Some ℓdisc) = Policy.label_lookup c_idx Γ →
          (* udpate the policy environment. *)
          ℓcur ⊑ ℓ1 → Γ' = Policy.update_label c_idx Γ (ℓ2, Some ℓdisc) →
          (* update the cell. *)
          c = Tuple.nth _ c_idx idx_bound → c' = (trans_func_denote _ _ f) c →
          (* update the tuple by updating this cell. *)
          Some t' = Tuple.set_nth_type_match _ c_idx c' idx_bound t →
          (* update the tuple environment. *)
          tl' = set_nth tl 0 t' →
          (* update the environment. *)
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ' β e' p' ⟩
where "c1 '>[' f ']>' c2" := (step_cell _ _ f c1 c2).

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
  | E_Empty: ∀ s1 Γ β p (e: ℰ s1),
      ⟨ s1 Γ β e p ⟩ =[ operator_empty ]=> ⟨ nil nil β nil nil ⟩
  (* If the operator returns an empty environment, we do nothing. *)
  | E_ProjEmpty: ∀ s1 s2 Γ Γ' β β' p p' (e: ℰ s1) (e': ℰ s2) project_list o,
      ⟨ s1 Γ β e p ⟩ =[ o ]=> ⟨ s2 Γ' β' e' p' ⟩ →
      List.length e' = 0 →
      ⟨ s1 Γ β e p ⟩ =[ operator_project project_list o ]=> ⟨ s2 Γ' β' nil nil ⟩
  | E_Proj: ∀ s1 s2 s3 Γ Γ' β β' p p' (e: ℰ s1) (e'': ℰ s2) (e': ℰ s3) project_list ℓ o,
      ⟨ s1 Γ β e p ⟩ =[ o ]=> ⟨ s2 Γ' β' e'' p'⟩ →
      List.length e' > 0 →
      ℓ = normalize_project_list s2 project_list →
      s3 = determine_schema s2 ℓ →
      ⟨ s1 Γ β e p ⟩ =[ operator_project project_list o]=> ⟨ s3 Γ' β' e' p' ⟩
where "c1 '=[' o ']=>' c2" := (step_config o c1 c2).
