
> {-# OPTIONS_GHC -Wall #-}

> {-# LANGUAGE GADTs, FlexibleInstances #-}

Having defined OBDDs, we can now move on to ROBDDs.

> module ROBDD where

> import Data.Map
> import Prelude hiding (lookup)

> import Formula

The type of ROBDDs is bdd,
which is either a Boolean constant (denoting a terminal vertex) or a pointer
to an entry in the global data structure BDDPoo

> data ROBDD lbl = Root (BDDPool lbl) (BDD lbl)

Without pointers in haskell, bdd is either a constant or an internal node. We
get the functions label, left, and right for free.

> data BDD lbl = Const Bool
>              | Node { f     :: Formula lbl,
>                       label :: lbl, 
>                       left  :: BDD lbl, 
>                       right :: BDD lbl }

> type NodeKey lbl = (lbl, BDD lbl, BDD lbl)
> type BDDPool lbl = Map (NodeKey lbl) (BDD lbl)

Insert
insert :: Ord lbl => NodeKey lbl -> BDD lbl -> BDDPool lbl -> BDDPool lbl

Contains
member :: Ord lbl => NodeKey lbl -> BDDPool lbl -> Bool

Index is now unused without pointers.

Deref
lookup :: Ord lbl => NodeKey lbl -> BDDPool lbl -> Maybe (BDD lbl)

> 