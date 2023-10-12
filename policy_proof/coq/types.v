Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Inductive Conjuction: Type := And | Or.

(* Basic value types. *)
Inductive Value: Set :=
  | Integer: Z -> Value
  | Bool: bool -> Value
  | String: string -> Value
  | NULL: Value.

(* Attributes are themselves string representation of the name. *)
Definition Attribute := string.
Definition Symbol := string.
Definition Aggregate := string.

(* Function types that can be applied on attributes *)
Inductive Func: Type :=
  (* Simply returns the value *)
  | func_val: Value -> Func
  (* Identity *)
  | func_ident: Attribute -> Func
  (* Function application *)
  | func_expr: Symbol -> list Func -> Func.

(* Aggregate types. *)
Inductive Agg: Type :=
  | agg_expr: Func -> Agg
  | agg_agg: Aggregate -> Func -> Agg
  | agg_func: Symbol -> list Agg -> Agg.

(* Something that will appear in `where` or filter. *)
Inductive Predicate (domain: Type): Type :=
  (* Constant true *)
  | predicate_true: Predicate domain
  (* Negation *)
  | predicate_not: Predicate domain -> Predicate domain
  (* A conjuction *)
  | predicate_conj: Conjuction -> Predicate domain -> Predicate domain -> Predicate domain
.

Definition true_to_coq_true (domain: Type) (p: Predicate domain): bool :=
  match p with
  | predicate_true _ => true
  | _ => false
  end.

Definition coq_true_to_true (domain: Type) (b: bool): Predicate domain :=
  match b with
  | true => predicate_true domain
  | false => predicate_not domain (predicate_true domain)
  end.

