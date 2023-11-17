import Lean

-- The recursive defined BST where
--  * leaf contains nothing.
--  * node contains a left tree and a right tree with an internal kv store.
inductive Tree (beta: Type v) where
  | leaf
  | node (left: Tree beta) (key: Nat) (val: beta) (right: Tree beta)
  deriving Repr

def Tree.search? (tree: Tree beta) (key: Nat) : Option beta :=
  match tree with
    | leaf => none
    | node lhs k v rhs =>
      if key < k then lhs.search? key
      else if key > k then rhs.search? key
      else some v

def Tree.make (tree: Tree beta) (key: Nat) (val: beta) : Tree beta :=
  match tree with
    | leaf => node leaf key val leaf
    | node lhs k _ rhs =>
      if key < k then lhs.make key val
      else if key > k then rhs.make key val
      else node lhs key val rhs

def Tree.as_list (tree: Tree beta) : List Nat :=
  match tree with
    | leaf => List.nil
    | node lhs k _ rhs => lhs.as_list ++ [k] ++ rhs.as_list

inductive pred_holds_for_tree (pred: Nat -> beta -> Prop) : Tree beta -> Prop 
  | leaf: pred_holds_for_tree pred Tree.leaf
  | node:
    -- lhs => mid => rhs => all
    pred_holds_for_tree pred lhs ->
    pred k v ->
    pred_holds_for_tree pred rhs ->
    pred_holds_for_tree pred (Tree.node lhs k v rhs)

inductive is_bst : Tree beta -> Prop
  | leaf : is_bst Tree.leaf
  | node:
    pred_holds_for_tree (fun k _ => k < key) lhs ->
    pred_holds_for_tree (fun k _ => k > key) rhs ->
    is_bst lhs -> is_bst rhs -> is_bst (Tree.node lhs k v rhs)
