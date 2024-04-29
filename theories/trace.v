Require Import List.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import types.
Require Import util.

Inductive prov_type: Set :=
  | prov_trans_unary: un_op → prov_type
  | prov_trans_binary: ∀ bt, bin_op → type_to_coq_type bt → prov_type
  | prov_agg: agg_op → prov_type
  (* Just re-use it; should be fine. *)
  | prov_udf: trans_op → prov_type
  | prov_noise: noise_op → prov_type
  | prov_join: prov_type
.

Definition prov_type_eqb (τ1 τ2: prov_type): bool.
  refine (match τ1, τ2 with
  | prov_trans_unary op1, prov_trans_unary op2 => un_op_eqb op1 op2
  | prov_trans_binary bt1 op1 v1, prov_trans_binary bt2 op2 v2 => andb (bin_op_eqb op1 op2) _
  | prov_agg op1, prov_agg op2 => agg_op_eqb op1 op2
  | prov_noise op1, prov_noise op2 => noise_op_eqb op1 op2
  | prov_join, prov_join => true
  | prov_udf op1, prov_udf op2 => trans_op_eqb op1 op2
  | _, _ => false
  end).
  destruct (type_matches bt1 bt2) eqn: Heq.
  - apply type_matches_eq in Heq. subst.
    destruct bt2; simpl in *.
    + destruct (Nat.eqb v1 v2).
      * apply true.
      * apply false.
    + destruct (Bool.eqb v1 v2).
      * apply true.
      * apply false.
    + destruct (String.eqb v1 v2).
      * apply true.
      * apply false.
  - apply false.
Defined.

Inductive trace_ty: Type :=
  (* ⊥ *)
  | TrEmpty: Policy.policy → trace_ty
  (* Linear trace: op → current policy → predecessors *)
  | TrLinear: prov_type → Policy.policy → trace_ty → trace_ty
  (* Branching trace. *)
  | TrBranch: prov_type → Policy.policy → list trace_ty → trace_ty
  (* Binary expressions *)
  | TrBinary: prov_type → Policy.policy → trace_ty → trace_ty → trace_ty  
.

Definition extract_policy tr :=
  match tr with
  | TrEmpty p => p
  | TrLinear _ p _ => p
  | TrBranch _ p _ => p
  | TrBinary _ p _ _ => p
  end.

(*
 * A trace is a list of tuples recording how a given data cell is transitioned
 * from one policy to another; it also bookkeeps the provenance information.
 *)
Definition trace := ctx trace_ty.

(* σ ::= ⟨ Γ, β ⟩; the program state. *)
Definition σ := (Policy.context * budget)%type.
