
Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Wellfounded.Lexicographic_Product.

Generalizable All Variables.
Reserved Infix "⊓" (at level 40, left associativity).
Reserved Infix "⊔" (at level 36, left associativity).

Class Lattice (A : Type) := {
  meet : A -> A -> A where "x ⊓ y" := (meet x y);
  join : A -> A -> A where "x ⊔ y" := (join x y);

  meet_commutative : forall a b, a ⊓ b = b ⊓ a;
  meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c);
  meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a;
  meet_idempotent  : forall a, a ⊓ a = a;

  join_commutative : forall a b, a ⊔ b = b ⊔ a;
  join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c);
  join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a;
  join_idempotent  : forall a, a ⊔ a = a
}.

Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 36, left associativity).

Class Order (A : Set) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.
(* 
Infix "≤" := ord (atlevel 50). *)

Inductive Labels : Type :=
  | Top
  | Mid.
