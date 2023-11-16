(* The policy library. *)

(* For now, the policy is just a placeholder. *)
Inductive policy : Set :=
  | policy_empty : policy
  | policy_select: policy
  | policy_top : policy
  .
