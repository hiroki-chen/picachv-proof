Require Import ordering.

(* We require that the element must have ordering. *)
(* A bag is a multiset. *)
Class FiniteBag (elt: Set) (E: Ordered elt) := {
    (* The bag type. *)
    bag: Type;

    (* Creates an empty bag. *)
    empty: bag;
    (* Converts an element into a bag. *)
    lift: elt -> bag;
    (* Check if an element is in the bag. *)
    member: elt -> bag -> Prop;
    (* Append an element into the bag. *)
    add: elt -> bag -> bag;
    (* Do a union. *)
    union: bag -> bag -> bag;
    (* Check if the bag is empty. *)
    is_empty: bag -> Prop;
    (* Check if the bag is a subset of another bag. *)
    subbag: bag -> bag -> Prop;
    (* Check if two bags are equal. *)
    equal: bag -> bag -> Prop;
    (* Apply a map on all elements. *)
    map: bag -> (elt -> elt) -> bag;
    (* Apply a filter on all elements. *)
    filter: bag -> (elt -> bool) -> bag;
    (* Apply a fold on all elements. *)
    fold: bag -> (elt -> elt -> elt) -> elt -> elt;

    (* TODO: IN CONSTRUCTION. *)
    (* partition: creates an element-to-list set. *)

    (* The following are theorems. *)
    (* The empty bag is empty. *)
    empty_is_empty: is_empty empty;
    (* If an element is in the bag, then the bag is not empty. *)
    member_is_not_empty: forall (e: elt) (b: bag), member e b -> ~ is_empty b;
    (* If an element is in the bag, then the bag is a subset of the bag with the element. *)
    member_subbag: forall (e: elt) (b: bag), member e b -> subbag b (add e b);
    (* If an element is in the bag, then the bag is equal to the bag with the element. *)
}.