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
