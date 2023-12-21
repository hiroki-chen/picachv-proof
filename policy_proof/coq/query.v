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

(* (*
  We say that the project list is "normalized" if the list contains no column names and no constants.
*)
Definition normalized (pl: project_list): Prop :=
  match pl with
  | project_star => False
  | project ℓ =>
      (fix check ℓ := match ℓ with
                      | nil => True
                      | x :: ℓ' => match x with
                                  | simple_atomic_expression_column _ => False
                                  | simple_atomic_expression_const _ => False
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
  end. *)

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

Lemma determine_schema_concat: ∀ s a ℓ,
  determine_schema s (project (a :: @nil simple_atomic_expression)) ++
    determine_schema s (project ℓ) =
  determine_schema s (project (a :: ℓ)).
Proof.
  induction ℓ; destruct a; auto.
  - simpl. destruct (Tuple.nth_nocheck s n); auto.
  - simpl. destruct (determine_bt_from_args s l); auto.
  - 
Admitted.

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
  - functions to functions (by normalizing all its arguments).

  We will later prove that this function preserves the semantics of the project operation.
*)
Fixpoint normalize_project_list_list
  (s: schema) (pl: list (simple_atomic_expression)): list (simple_atomic_expression) :=
  match pl with
    | nil => nil
    | e :: pl' => (fix normalize e := match e with
                    | simple_atomic_expression_column c => 
                          (simple_atomic_expression_func stf_id
                            (cons (simple_atomic_expression_column c) nil)
                          )
                    | simple_atomic_expression_const _ => e
                    (* This branch of the `normalize` function handles the case where the
                       simple atomic expression is a function. It recursively normalizes
                       the list of arguments `ℓ` to the function using the helper function
                       `normalize'`. 

                      The normalized list of arguments `ℓ'` is then used to construct a
                      new simple atomic expression with the same function `f` and the
                      normalized arguments `ℓ'`.

                      We do not explicitly define any recursive helpers outside this function
                      body since that would be too cumbersome. We also define two anonymous
                      functions so that we can let Coq know that the two functions terminate.
                    *)
                    | simple_atomic_expression_func f ℓ =>
                        let ℓ' := (fix normalize' ℓ :=
                          match ℓ with
                          | nil => nil
                          | h :: t => normalize h :: normalize' t
                          end
                        ) ℓ
                        in
                        simple_atomic_expression_func f ℓ'
                  end) e 
                    :: normalize_project_list_list s pl'
  end.

Lemma normalize_project_star_length: ∀ s n,
  List.length (normalize_project_star s n) = List.length s.
Proof.
  induction s.
  - auto.
  - intros. simpl.
    specialize IHs with (n := S n). rewrite <- IHs. auto.
Qed.

Definition normalize_project_list (s: schema) (pl: project_list): list (simple_atomic_expression) :=
  match pl with
    | project_star => normalize_project_star s 0
    | project ℓ => normalize_project_list_list s ℓ
  end.

Lemma normalize_preserve_length: ∀ s pl,
  List.length pl = List.length (normalize_project_list_list s pl).
Proof.
  induction s; induction pl; simpl; auto with *.
Qed.

Example sample_schema: schema := (IntegerType :: StringType :: BoolType :: nil)%type.
Compute normalize_project_list sample_schema project_star.
Compute normalize_project_list
  sample_schema
  (project (
    (simple_atomic_expression_func
      stf_other
      ((simple_atomic_expression_column 0) :: nil)
    ) :: nil)
  ).

(* 
Lemma normalize_normalized: ∀ s pl, normalized (normalize_project_list s pl).
Proof.
  destruct pl.
  - induction s; simpl; auto.
  - induction l.
    + simpl. auto.
    + destruct a; simpl; auto.
      induction l0; simpl; auto with *.
      destruct a; simpl; auto.
Qed. *)

Definition groupby_list := (list nat)%type.
Definition agg_list s := (list (∀ bt, agg_expression s bt))%type.

(* Do we really need `list nat` to represent the lists? *)
Definition env_slice s := (relation s * list nat * groupby_list * list (Tuple.tuple s))%type.

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

Definition env_slice_get_tuples s (es: env_slice s) : list (Tuple.tuple s) :=
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
Inductive config: Type :=
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
          List.length s = 0 →
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e p ⟩
  (* If the environment is not empty but there is no active tuples, we cannot do anything. *)
  | E_CTransSkip2:
      ∀ ℓ1 ℓ2 s Γ β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length s > 0) tl,
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          List.length tl = 0 → 
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e p ⟩
  (* The label does not flow to the current one. *)
  | E_CTransSkip3:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length s > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          Some (ℓcur, Some ℓdisc) = Policy.label_lookup c_idx Γ →
          ~ (ℓcur ⊑ ℓ1) →
          ⟨ s Γ β e p ⟩ >[ f ]> ⟨ s Γ β e p ⟩
  (* No active labels are found; this should be an error. *)
  | E_CTransError1:
      ∀ ℓ1 ℓ2 s Γ β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length s > 0)
        tl (tl_non_empty: List.length tl > 0) t c_idx,
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
          (* t => The first tuple. *)
          t = hd_ok tl tl_non_empty →
          (* we now get the label encodings. *)
          None = Policy.label_lookup c_idx Γ →
          ⟨ s Γ β e p ⟩ >[ f ]> config_error
  | E_CTransError2:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e p (f: trans_func ℓ1 ℓ2) (non_empty: List.length s > 0)
        tl (tl_non_empty: List.length tl > 0) t c c' c_idx
        (idx_bound: c_idx < List.length (hd_ok s non_empty)),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
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
  (* TODO: Perhaps we need to add some sort of provenance update? *)
  | E_CTransOk:
      ∀ ℓ1 ℓ2 ℓcur ℓdisc s Γ Γ' β e e' p p' (f: trans_func ℓ1 ℓ2) (non_empty: List.length s > 0)
        tl tl' (tl_non_empty: List.length tl > 0) t t' c c' c_idx
        (idx_bound: c_idx < List.length (hd_ok s non_empty)),
          (* tl => A list of tuples. *)
          tl = (env_slice_get_tuples (hd_ok s non_empty) (get_env_slice s e non_empty)) →
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
   `apply_proj_elem` is a function that applies a projection operation to a
   single column of a relation.
*)
Definition apply_proj_elem s (r: relation s) (expr: simple_atomic_expression)
                           (Γ: Policy.context) (p: prov_ctx)
  : relation (determine_schema s (project (expr :: nil))) * Policy.context * prov_ctx.
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
Definition apply_proj_in_relation s (r: relation s) (ℓ: list (simple_atomic_expression))
                                    (Γ: Policy.context) (p: prov_ctx)
  : relation (determine_schema s (project ℓ)) * Policy.context * prov_ctx.
Proof.
  induction ℓ.
  - exact (nil, Γ, p).
  - (* We apply `a` to the relation s and obtain the output. *)
    pose (apply_proj_elem s r a Γ p) as col.
    pose (fst (fst IHℓ)) as r'.
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
    apply (relation_join _ _ r'') in r'.
    rewrite (determine_schema_concat s a ℓ) in r'.
    exact (r', Γ', p').
Defined.

Definition apply_proj_in_env_slice s (es: env_slice s) (ℓ: list (simple_atomic_expression))
                                     (Γ: Policy.context) (p: prov_ctx)
  : env_slice (determine_schema s (project ℓ)) * Policy.context * prov_ctx :=
  match es with
  | (r, a, b, _) =>
      let r := (apply_proj_in_relation s r ℓ Γ p) in
        match r with 
        | (r', Γ', p') => ((r', a, b, nil), Γ', p')
        end
  end.

(* 
  A helper function that applies the projection list in the environment.
  It returns a new environment, a new policy environment, and a new provenance context.

  Note that `ℓ` is the normalized projection list.
*)
Definition apply_proj_in_env s (evidence: List.length s > 0): ∀ (e: ℰ s)
                             (ℓ: list simple_atomic_expression) (Γ: Policy.context) (p: prov_ctx),
                             ℰ ((determine_schema (hd_ok s evidence) (project ℓ)) :: (tail s)) *
                             Policy.context * prov_ctx.
  destruct s.
  - simpl in evidence. lia.
  - intros. 
    simpl. intros.
    (* We now apply the projection list in the environment slice. *)
    pose (apply_proj_in_env_slice s (fst e) ℓ Γ p) as config'.
    exact (fst (fst config'), snd e, (snd (fst config')), snd config').
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
  | E_Proj: ∀ s1 s2 Γ Γ' β β' p p' (e: ℰ s1) (e'': ℰ s2) project_list ℓ o,
      ⟨ s1 Γ β e p ⟩ =[ o ]=> ⟨ s2 Γ' β' e'' p'⟩ →
      (* Introduce terms into the scope to avoid identifier problems. *)
        ∀ (evidence: List.length s2 > 0) e',
          let input_schema := (hd_ok s2 evidence) in
            let output_schema := determine_schema input_schema (project ℓ) in
              ℓ = normalize_project_list input_schema project_list →
              (e', Γ', p') = apply_proj_in_env s2 evidence e'' ℓ Γ p →
              ⟨ s1 Γ β e p ⟩ =[ operator_project project_list o]=>
                ⟨ (output_schema :: (tail s2)) Γ' β' e' p' ⟩
where "c1 '=[' o ']=>' c2" := (step_config o c1 c2).
