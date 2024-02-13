Require Import formula.
Require Import Utf8.

Section Tests.

Import data_model.
Import String.
Import types.
Import config.
Import relation.
Import List.

(* expr = (λ x.x)1 *)
Example expr :=
  expression_app
    (expression_abs ("x"%string) (expression_var "x"%string))
    (expression_const IntegerType 1).

Example default_config := ⟨ database_empty nil nil nil ⟩.
Example default_relation := (relation_output nil nil).

Example result_is_1: ∀ env,
  eval_expr default_config default_relation expr env → snd env = EResultValue IntegerType 1.
Proof.
  intros.
  inversion H. subst. unfold expr in *. simpl in *.
  inversion H0; subst; intuition; try discriminate.


Example relation := (relation_output ((IntegerType, "foo"%string) :: (IntegerType, "bar"%string) :: nil) 
(((1, 2), (3, 4, tt)) :: nil)).
(* expr' =  (λ x. _0) 1 *)
Example expr' := expression_app
    (expression_abs ("x"%string) (expression_column 0))
    (expression_const IntegerType 1).

Example result' := snd (eval_expr default_config relation expr').
Example result'_is_rel : result' = EResultRelation (relation_output ((IntegerType, "foo"%string) :: nil) ((1, 2, tt) :: nil)).
Proof. reflexivity. Qed.

End Tests.
