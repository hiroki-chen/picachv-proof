Require Import expression.
Require Import Utf8.

Section Tests.

Import data_model.
Import String.
Import types.
Import config.
Import relation.
Import List.

Section Expr.

(* expr = (λ x.x)1 *)
Example expr :=
  expression_app
    (expression_abs ("x"%string) (expression_var "x"%string))
    (expression_const IntegerType 1).

Example default_config := ⟨ database_empty nil nil nil ⟩.
Example default_relation := (RelationWrapped nil nil).

End Expr.

Section Relation.

Example relation_a :=
  [[ << 4 >>, << 5 >>, << 6 >>, << ("abcd"%string) >> ]] ::
    [[ << 7 >>, << 8 >>, << 9 >>, << ("abcd"%string) >> ]] :: nil.
Example relation_b :=
  [[ << 1 >>, << 2 >>, << 3 >>, << ("abcd"%string) >> ]] ::
    [[ << 114 >>, << 514 >>, << 114 >>, << ("abcd"%string) >> ]] :: nil.
Example simple_schema :=
  (IntegerType, 1) ::
    (IntegerType, 2) ::
      (IntegerType, 3) ::
        (StringType, 4) :: nil.
Example cartesian_product_test := relation_product simple_schema simple_schema relation_a relation_b.

Example cartesian_product_test': cartesian_product_test = 
Proof.
  reflexivity.
Qed.

Example ok: 0 < List.length (simple_schema ++ simple_schema).
Proof.
  simpl. lia.
Qed.
Example extract_column_test := extract_column _ cartesian_product_test 0 ok.
Example extract_column_correct: extract_column_test = [[ << 4 >> ]] :: [[ << 4 >> ]] :: [[ << 7 >> ]] :: [[ << 7 >> ]] :: nil.
Proof.
  reflexivity.
Qed.

Example relation_stitch_test := relation_stitch simple_schema simple_schema relation_a relation_b.
Example relation_stitch_test': relation_stitch_test = (4, 0, (5, 0, (6, 0, ("abcd"%string, 0, (1, 0, (2, 0, (3, 0, ("abcd"%string, 0, tt)))))))) :: (7, 0, (8, 0, (9, 0, ("abcd"%string, 0, (114, 0, (514, 0, (114, 0, ("abcd"%string, 0, tt)))))))) :: nil.
Proof.
  reflexivity.
Qed.

Example simple_schema_lhs :=
  (IntegerType, "foo"%string) ::
    (IntegerType, "bar"%string) ::
      (IntegerType, "baz"%string) :: nil.

Example simple_schema_rhs :=
  (IntegerType, "baz"%string) ::
    (StringType, "qux"%string) :: nil.

Example join_by_test := output_schema_join_by simple_schema_lhs simple_schema_rhs ("baz"%string :: nil).
Example join_by_test': join_by_test = (IntegerType, "foo"%string) :: (IntegerType, "bar"%string) :: (IntegerType, "baz"%string)  :: (StringType, "qux"%string) :: nil.
Proof.
  reflexivity.
Qed.

Example tuple_a := [[ << 1 >>, << 2 >>, << 3 >>, << ("abcd"%string) >> ]].
Example tuple_b := [[ << 4 >>, << 2 >>, << 3 >>, << ("dcba"%string) >> ]].
Example tuple_schema_lhs := (IntegerType, "foo"%string) :: (IntegerType, "bar"%string) :: (IntegerType, "baz"%string) :: (StringType, "qux"%string) :: nil.
Example tuple_schema_rhs := (IntegerType, "a"%string) :: (IntegerType, "bar"%string) :: (IntegerType, "baz"%string) :: (StringType, "b"%string) :: nil.

Example common_join_list := find_common (join_list_to_index tuple_schema_lhs ("bar"%string :: "baz"%string :: nil) 0)
                                        (join_list_to_index tuple_schema_rhs ("bar"%string :: "baz"%string :: nil) 0).
Example common_join_list_correct: common_join_list = ((1, 1), (IntegerType, "bar"%string)) :: ((2, 2), (IntegerType, "baz"%string)) :: nil.
Proof.
  reflexivity.
Qed.

Example removed_schema_lhs := remove_common tuple_schema_lhs (List.map (fun x => fst (fst x)) common_join_list) 0.
Example removed_schema_rhs := remove_common tuple_schema_rhs (List.map (fun x => snd (fst x)) common_join_list) 0.
Example removed_schema_lhs_correct: removed_schema_lhs = (IntegerType, "foo"%string) :: (StringType, "qux"%string) :: nil.
Proof.
  reflexivity.
Qed.
Example removed_schema_rhs_correct: removed_schema_rhs = (IntegerType, "a"%string) :: (StringType, "b"%string) :: nil.
Proof.
  reflexivity.
Qed.

Example removed_common_lhs := remove_common_part tuple_schema_lhs tuple_a 0 (List.map (fun x => fst (fst x)) common_join_list).
Example removed_common_rhs := remove_common_part tuple_schema_rhs tuple_b 0 (List.map (fun x => snd (fst x)) common_join_list).
Example removed_common_lhs_correct: removed_common_lhs = [[ << 1 >>, << ("abcd"%string) >> ]].
Proof.
  reflexivity.
Qed.
Example removed_common_rhs_correct: removed_common_rhs = [[ << 4 >>, << ("dcba"%string) >> ]].
Proof.
  reflexivity.
Qed.

Example tuple_concat_by_test := tuple_concat_by tuple_schema_lhs tuple_schema_rhs ("bar"%string :: "baz"%string :: nil) tuple_a tuple_b.
(* 
Example tuple_concat_by_test_correct:
  tuple_concat_by_test =
  Some [[ << 1 >>, << ("abcd"%string) >>, << 2 >>, << 3 >>, << 4 >>, << ("dcba"%string) >> ]].
Proof.
  (*
    This is tricky because although Coq uses `eq_refl` to inhabit the refl type, the concrete form
    of the term appears rather complex. This is due to the heavy use of dependent types.

    Nevertheless, we can still use `reflexivity` to check the equivalance between terms as Coq can
    reduce the term recursively since the term is determined; thus the computation must terminate.
    To check if we are obtaining the correct result, we can just use `reflexivity`.
   *)
  reflexivity.
Qed. *)

End Relation.

End Tests.