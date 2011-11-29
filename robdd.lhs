
> {-# OPTIONS_GHC -Wall #-}

> {-# LANGUAGE GADTs, 
>     FlexibleInstances, 
>     FlexibleContexts,
>     ScopedTypeVariables #-}

Having defined OBDDs, we can now move on to ROBDDs.

> module ROBDD where

> import Control.Monad.State
> import Data.Map (Map)
> import qualified Data.Map as M
> import Data.Set (Set)
> import qualified Data.Set as S
> import Prelude hiding (lookup)

> import Formula (Formula (TM_T, TM_F, TM_Var, TM_Not, 
>                          TM_Conj, TM_Disj, TM_Exst),
>                 Variable (V), simplify)

The type of ROBDDs is bdd,
which is either a Boolean constant (denoting a terminal vertex) or a pointer
to an entry in the global data structure BDDPoo

> data ROBDD lbl = Root (BDDPool lbl) (BDD lbl)

Without pointers in haskell, bdd is either a constant or an internal node. We
get the functions label, left, and right for free.

> data BDD lbl = Const Bool
>              | Node { form  :: Formula lbl,
>                       label :: lbl, 
>                       left  :: BDD lbl, 
>                       right :: BDD lbl }
>   deriving (Eq, Ord)

The goal here is to compute a robdd from a formula. We define 
formulaToROBDD here

> formulaToROBDD :: Ord lbl => Formula lbl -> ROBDD lbl
> formulaToROBDD f = Root finalPool bdd where

>   (bdd, finalPool) = runState (convert.simplify$f) S.empty

>   convert :: Ord lbl => Formula lbl -> State (BDDPool lbl) (BDD lbl)

>   convert (TM_T) = error "simplify"
>   convert (TM_F) = error "simplify"

>   convert (TM_Var (V l)) = 
>     addVertex l (Const False) (Const True)

>   convert (TM_Not (TM_Var (V l))) =
>     addVertex l (Const True) (Const False)

>   convert (TM_Conj f1 f2) = do bdd1 <- convert f1
>                                bdd2 <- convert f2
>                                evalStateT (conj bdd1 bdd2) M.empty

>   convert (TM_Disj f1 f2) = do bdd1 <- convert f1
>                                bdd2 <- convert f2
>                                disj bdd1 bdd2

>   convert (TM_Not f') = do bdd' <- convert f'
>                            diff (Const True) bdd'

>   convert (TM_Exst (V l) f') = do bdd' <- convert f'
>                                   exists bdd' l

We need two more data structures for our computation. First, we need a global
set of BDDNodes

> type BDDPool lbl = Set (BDD lbl)

Insert exists in the definition for Data.Map
insert :: Ord lbl => NodeKey lbl -> BDD lbl -> BDDPool lbl -> BDDPool lbl

Contains is simple member
member :: Ord lbl => NodeKey lbl -> BDDPool lbl -> Bool

Index is now unused without pointers.
Deref is also unused, since we rely on structural equality rather than 
an equivalence relation to check (robdd1 :: BDD) == (robdd2 :: BDD)

BDDPool is used to implement addVertex

> addVertex :: Ord lbl => 
>              lbl -> BDD lbl -> BDD lbl -> 
>              State (BDDPool lbl) (BDD lbl)
> addVertex = undefined

The next step in the implementation is to define operations on robdds. To
avoid recomputation, we keep a table of parameters and results.

> type ComputeKey lbl   = (BDD lbl, BDD lbl)
> type Table lbl = Map (ComputeKey lbl) (BDD lbl)

conj :: Ord lbl => 
        (MonadState (BDDPool lbl) m, 
         MonadState (Table lbl) m) =>
        BDD lbl -> BDD lbl -> m (BDD lbl)

> conj :: Ord lbl => BDD lbl -> BDD lbl ->
>         StateT (Table lbl) (State (BDDPool lbl)) (BDD lbl)

First, we have four trivial cases, which we won't save for recomputation

> conj (Const False) _  = return $ Const False
> conj _ (Const False)  = return $ Const False
> conj (Const True) bdd = return $ bdd
> conj bdd (Const True) = return $ bdd

After this, we need to examine the case where both are pointers
to internal nodes.

> conj bdd1 bdd2 = 
>   if bdd1 == bdd2 
>   then return bdd1
>   else do (_table::Table lbl) <- get
>           undefined

> disj :: Ord lbl => BDD lbl -> BDD lbl ->
>                    State (BDDPool lbl) (BDD lbl)
> disj = undefined

> diff :: Ord lbl => BDD lbl -> BDD lbl ->
>                    State (BDDPool lbl) (BDD lbl)
> diff = undefined

> exists :: Ord lbl => BDD lbl -> lbl ->
>                      State (BDDPool lbl) (BDD lbl)
> exists = undefined
