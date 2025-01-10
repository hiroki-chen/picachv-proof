Require Import Eqdep_dec.
Require Import List.
Require Import Unicode.Utf8.

Require Import Base.Trace.

Require Import Operational.Expression.

Lemma do_eval_udf_ok: ∀ trace args_types ret op f β tr tp gb args policy res,
  trace_ok tr →
  do_eval_udf args_types ret op f (β, tr, tp, gb) args (Some (policy, trace, res)) →
  Forall (λ x, label_transition_valid x) trace ∧ branch_ok policy trace.
Proof.
  induction trace.
  - intuition. constructor.
  - intros. inversion H0. subst. inversion H5. subst. clear H5. (* Preparation *)
    apply inj_pair2_eq_dec in H1, H1, H4.
    + inversion H15. subst.
      inversion H7. subst. apply inj_pair2_eq_dec in H6. subst. split.
      * apply Forall_cons_iff. split.
        -- inversion H21. subst.

Admitted.
