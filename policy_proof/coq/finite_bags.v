(*
  Author: Hiroki Chen
  Date: 11/20/2023
  Email: haobchen@iu.edu

  This Coq file defines a class `FiniteBag` that represents a multiset (or bag) of elements.
  The elements in the bag must have an ordering, as indicated by the `Ordered` class constraint
  on the type of elements (elt). This file is essential for building the relation in a dataframe.

  The reason why we refrain from using the `Multiset` library in Coq is that the library is
  not well-developed for the purpose of building a relation in a dataframe. Also, the type
  of elements in the `Multiset` library is dependent on a concrete type, which means that we
  cannot use the library to build a relation on a dataframe with a generic type determined
  at runtime.

  == References ==
  1. Coq Standard Library, Multiset: https://coq.inria.fr/library/Coq.Sets.Multiset.html
  2. Harvard' YNOT Project. https://web.archive.org/web/20100204055904/http://ynot.cs.harvard.edu/
  3. Benzaken and Contejeam.
     A Coq mechanised formal semantics for realistic SQL queries: formally reconciling SQL and bag
     relational algebra.
     In CPP'19.
*)

Require Import RelationClasses.
Require Import SetoidClass.
Require Import List.
Require Import Unicode.Utf8.

Require Import ordering.

(* We require that the element must have ordering. *)
(* A bag is a multiset. *)
Class FiniteBag (elt: Set) (E: Ordered elt) := {
    (* The bag type. *)
    bag: Set;
    ord :: Ordered bag;

    (* Creates an empty bag. *)
    empty: bag;
    (* Converts an element into a bag. *)
    lift: elt → bag;
    (* Check if an element is in the bag. *)
    in_bag: elt → bag → Prop;
    (* Checks if an element is in the bag, returns bool. *)
    in_bag_bool: elt → bag → bool;
    (* Append an element into the bag. *)
    add: elt → bag → bag;
    (* Do a union. *)
    union: bag → bag → bag;
    (* Check if the bag is empty. *)
    is_empty: bag → Prop;
    (* Check if the bag is a subset of another bag. *)
    subbag: bag → bag → Prop;
    (* Check if two bags are equal. *)
    equal: bag → bag → Prop;
    (* Apply a map on all elements. *)
    map: (elt → elt) → bag → bag;
    (* Apply a filter on all elements. *)
    filter: (elt → bool) → bag → bag;
    (* Removes an element. *)
    remove: elt → bag → bag;
    (* Apply a fold on all elements. *)
    fold : ∀ A : Set, (elt → A → A) → bag → A → A;
    (* Returns the length of the bag. *)
    len: bag → nat;
    (* Returns all the elements in the bag. *)
    elements: bag → list elt;
    (* Returns the number of a given element in the bag. *)
    count: elt → bag → nat;
    (* Returns an element in the bag. *)
    choose : bag → option elt;
    (* Checks if all elements satisfy a given predicate. *)
    for_all : (elt → bool) → bag → bool;
    (* Checks if there ∃ an element that satisfies a given predicate. *)
    exists_element: (elt → bool) → bag → bool;

    compare : bag → bag → comparison;
    (* TODO: IN CONSTRUCTION. *)
    (* partition: creates an element-to-list set. *)

    (* The following are theorems. *)
    (* The empty bag is empty. *)
    empty_is_empty: is_empty empty;
    (* Prop <→ bool. *)
    in_bag_is_in_bag_bool: ∀ (e: elt) (b: bag), in_bag e b ↔ in_bag_bool e b = true;
    (* If an element is in the bag, then the bag is not empty. *)
    member_is_not_empty: ∀ (e: elt) (b: bag), in_bag e b → ~ is_empty b;
    (* If an element is in the bag, then the bag is a subset of the bag with the element. *)
    member_subbag: ∀ (e: elt) (b: bag), in_bag e b → subbag b (add e b);
    subbag_count_less: ∀ (a b: bag), subbag a b ↔ ∀ (e: elt), count e a <= count e b;
    (* Length should match. *)
    length_elements: ∀ (b: bag), len b = length (elements b);
    (* If two bags are equal, then the number of a given element in the bags are equal. *)
    eq_bag_count_eq: ∀ (b1 b2: bag),
      equal b1 b2 ↔ ∀ (e: elt), count e b1 = count e b2;
    (* If a bag is empty, then there is no member in it *)
    empty_bag_no_member: ∀ (b: bag),
      is_empty b ↔ ∀ (e: elt), in_bag_bool e b = false;
    (* If a bag is empty, then there is no member in it *)
    empty_bag_no_member': ∀ (e: elt), in_bag_bool e empty = false;
    choose_spec: ∀ (b: bag) (e: elt), choose b = Some e → count e b > 0;
    choose_spec': ∀ (b: bag), choose b = None → is_empty b;
    compare_spec : ∀ s1 s2, compare s1 s2 = Eq ↔ equal s1 s2;
    compare_eq_trans : 
      ∀ a1 a2 a3, compare a1 a2 = Eq → compare a2 a3 = Eq → compare a1 a3 = Eq;
    compare_eq_lt_trans : 
      ∀ a1 a2 a3, compare a1 a2 = Eq → compare a2 a3 = Lt → compare a1 a3 = Lt;
    compare_lt_eq_trans : 
      ∀ a1 a2 a3, compare a1 a2 = Lt → compare a2 a3 = Eq → compare a1 a3 = Lt;
    compare_lt_trans : 
      ∀ a1 a2 a3, compare a1 a2 = Lt → compare a2 a3 = Lt → compare a1 a3 = Lt;
    compare_lt_gt : ∀ a1 a2, compare a1 a2 = CompOpp (compare a2 a1);
    exists_bool : ∀ (s : bag) (f : elt → bool), exists_element f s = existsb f (elements s);
}.

Hint Immediate @empty_is_empty.
Hint Resolve
  @in_bag_is_in_bag_bool @member_is_not_empty @member_subbag
  @length_elements @eq_bag_count_eq @empty_bag_no_member @subbag_count_less
  @empty_bag_no_member @compare_spec @compare_eq_lt_trans @compare_eq_trans
  @compare_lt_gt @compare_lt_trans @exists_bool.

Section FB.
  Hypothesis elt: Set.
  Hypothesis E: Ordered elt.

  (* The bag type. *)
  Definition fbag := @list elt.

  (* Creates an empty bag. *)
  Definition empty_bag: fbag := nil.

  Definition lift' (e: elt): fbag := cons e empty_bag.

  Definition in_bag' (e: elt) (b: fbag): Prop := In e b.

  Fixpoint in_bag_bool' (e: elt) (b: fbag): bool :=
    match b with
    | nil => false
    | cons e' b' => match cmp e e' with
                    | OrderedType.EQ _ => true
                    | OrderedType.GT _ => false
                    | OrderedType.LT _ => in_bag_bool' e b'
                    end
    end.

  Fixpoint add' (e: elt) (b: fbag): fbag := 
    match b with
      | nil => e :: nil
      | e' :: b' => match cmp e e' with
                    | OrderedType.EQ _ => e :: b'
                    | OrderedType.GT _ => e' :: add' e b'
                    | OrderedType.LT _ => e :: e' :: b'
                    end
  end.

  Fixpoint remove' (e: elt) (b: fbag): fbag :=
    match b with
    | nil => nil
    | e' :: b' => match cmp e e' with
                  | OrderedType.EQ _ => b'
                  | OrderedType.GT _ => e' :: remove' e b'
                  | OrderedType.LT _ => e' :: b'
                  end
    end.


  Fixpoint union' (b: fbag): fbag → fbag :=
    match b with
    | nil => fun b' => b'
    | e :: b' =>  
      (fix union'' (b'': fbag): fbag :=
        match b'' with
        | nil => e :: b'
        | e' :: b''' => match cmp e e' with
                        | OrderedType.EQ _ => e :: union' b' b'''
                        | OrderedType.GT _ => e' :: union'' b'''
                        | OrderedType.LT _ => e :: union' b' b''
                        end
        end)
    end.

    Fixpoint subset' (b1 b2: fbag): Prop :=
      match b1 with
      | nil => True
      | e :: b1' => match b2 with
                    | nil => False
                    | e' :: b2' => match cmp e e' with
                                  | OrderedType.EQ _ => subset' b1' b2'
                                  | OrderedType.GT _ => subset' b1 b2'
                                  | OrderedType.LT _ => False
                                  end
                    end
      end.

      Fixpoint for_all' (f: elt → bool) (b: fbag): bool :=
        match b with
        | nil => true
        | e :: b' => if f e then for_all' f b' else false
        end.

    Fixpoint exists' (f: elt → bool) (b: fbag): bool :=
      match b with
      | nil => false
      | e :: b' => if f e then true else exists' f b'
      end.

    Fixpoint fold' (A: Set) (f: elt → A → A) (b: fbag) (a: A): A :=
      match b with
      | nil => a
      | e :: b' => fold' A f b' (f e a)
      end.

    Fixpoint count' (e: elt) (b: fbag): nat :=
      match b with
      | nil => 0
      | e' :: b' => match cmp e e' with
                    | OrderedType.EQ _ => S (count' e b')
                    | OrderedType.GT _ => count' e b'
                    | OrderedType.LT _ => count' e b'
                    end
      end.

    Definition choose' (b: fbag): option elt :=
      match b with
      | nil => None
      | e :: b' => Some e
      end.
    
    Fixpoint map' (f: elt → elt) (b: fbag): fbag :=
      match b with
      | nil => nil
      | e :: b' => f e :: map' f b'
      end.

    Fixpoint filter' (f: elt → bool) (b: fbag): fbag :=
      match b with
      | nil => nil
      | e :: b' => if f e then e :: filter' f b' else filter' f b'
      end.

    Fixpoint equal' (b1 b2: fbag): Prop :=
      match b1 with
      | nil => match b2 with
              | nil => True
              | _ => False
              end
      | e :: b1' => match b2 with
                    | nil => False
                    | e' :: b2' => match cmp e e' with
                                  | OrderedType.EQ _ => equal' b1' b2'
                                  | OrderedType.GT _ => False
                                  | OrderedType.LT _ => False
                                  end
                    end
      end.

  Definition len' (b: fbag): nat := length b.

  Definition elements' (b: fbag): list elt := b.

  Global Instance fbag_eq_setoid: Setoid fbag.
  refine (
    @Build_Setoid _ equal' _
  ).
    constructor.
    - unfold Reflexive. intros. induction x; try intuition auto with *.
      simpl in *. destruct (cmp a a); intuition; apply neq in l; intuition auto with *.
    - unfold Symmetric. induction x; destruct y; auto. intros.
      simpl in *. destruct (cmp e a); destruct (cmp a e);
      try assumption; try red in e0; try apply neq in l; auto with *.
    - unfold Transitive. induction x; destruct y; destruct z; auto with *.
      intuition. simpl in *.
      destruct (cmp a e); destruct (cmp e e0); destruct (cmp a e0);
      try intuition auto with *.
      + apply neq in l. red in e1. red in e2. eapply transitivity in e2. eauto. assumption.
      + specialize (IHx _ _ H H0). assumption.
      + destruct (SetoidDec.equiv_dec e0 a).
        * apply neq in l. intuition.
        * apply neq in l. intuition.
          red in e1. red in e2. assert (a == e0). eapply transitivity. eauto. assumption.
          symmetry in H1. intuition.
Defined.

End FB.