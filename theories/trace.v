Require Import List.
Require Import Unicode.Utf8.

Require Import data_model.
Require Import types.
Require Import util.

Inductive prov_type: Set :=
  | prov_trans_unary: un_op → prov_type
  | prov_trans_binary: bin_op → prov_type
  | prov_agg: agg_op → prov_type
  | prov_noise: noise_op → prov_type
  | prov_join: prov_type
.

Definition prov_type_eqb τ1 τ2: bool :=
  match τ1, τ2 with
  | prov_trans_unary op1, prov_trans_unary op2 => un_op_eqb op1 op2
  | prov_trans_binary op1, prov_trans_binary op2 => bin_op_eqb op1 op2
  | prov_agg op1, prov_agg op2 => agg_op_eqb op1 op2
  | prov_noise op1, prov_noise op2 => noise_op_eqb op1 op2
  | prov_join, prov_join => true
  | _, _ => false
  end.

Inductive trace_ty: Type :=
  (* ⊥ *)
  | TrEmpty: trace_ty
  (* Linear trace: op → current policy → predecessors *)
  | TrLinear: prov_type → Policy.policy → list trace_ty → trace_ty
  (* Branching trace. *)
  | TrBranch: prov_type → Policy.policy → trace_ty → trace_ty → trace_ty
.

Definition extract_policy tr :=
  match tr with
  | TrEmpty => ∎
  | TrLinear _ p _ => p
  | TrBranch _ p _ _ => p
  end.

(*
 * A trace is a list of tuples recording how a given data cell is transitioned
 * from one policy to another; it also bookkeeps the provenance information.
 *)
Definition trace := ctx trace_ty.

Fixpoint empty_trace_from_pctx (Γ: Policy.context): trace :=
  match Γ with
  | nil => nil
  | (n, _) :: Γ' => (n, TrEmpty) :: empty_trace_from_pctx Γ'
  end.

(* σ ::= ⟨ Γ, β ⟩; the program state. *)
Definition σ := (Policy.context * budget)%type.

Notation "∅" := TrEmpty.
