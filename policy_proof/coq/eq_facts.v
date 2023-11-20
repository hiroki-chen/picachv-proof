Require Import SetoidDec.
Require Import SetoidClass.
Require Import Equivalence.
Require Import Lia.
Require Import Ascii.
Require Import String.

Require Import ordering.

Global Instance char_eq_setoid : Setoid ascii.
refine (@Build_Setoid _ char_eq _).
  econstructor.
  - unfold Reflexive. intros. unfold char_eq. auto.
  - unfold Symmetric. intros. unfold char_eq in *. auto.
  - unfold Transitive. intros. unfold char_eq in *. lia.
Defined.