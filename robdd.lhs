
> {-# OPTIONS_GHC -Wall #-}

> {-# LANGUAGE GADTs, 
>     FlexibleInstances, 
>     FlexibleContexts,
>     ScopedTypeVariables #-}

Having defined OBDDs, we can now move on to ROBDDs.

> module ROBDD where

> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Map (Map)
> import qualified Data.Map as M
> import Prelude hiding (lookup)

> import Formula (Formula (TM_T, TM_F, TM_Var, TM_Not, 
>                          TM_Conj, TM_Disj, TM_Exst),
>                 Variable (V), simplify)
> import qualified Formula as F

The type of ROBDDs is bdd,
which is either a Boolean constant (denoting a terminal vertex) or a pointer
to an entry in the global data structure BDDPoo

> data ROBDD lbl = Root (BDD lbl)

> instance (Ord lbl, Show lbl) => Show (ROBDD lbl) where
>   show (Root bdd) = snd.fst $ 
>     runState (runWriterT $ printBDDPool bdd) 
>     (0, M.empty)

> printBDDPool :: (Ord lbl, Show lbl) => 
>                 BDD lbl -> WriterT String (State (Int, Map (BDD lbl) Int)) ()
> printBDDPool c@(Const b) = 
>   do (nextVertex, pool) <- get
>      if M.member c pool
>      then return ()
>      else do put (nextVertex + 1, M.insert c nextVertex pool)
>              tell.(++"\n") $ show nextVertex ++ "\t" ++ show b
> printBDDPool b@(Node l b0 b1) = 
>   do printBDDPool b0
>      printBDDPool b1
>      (nextVertex, pool) <- get
>      if M.member b pool
>      then return ()
>      else case (M.lookup b0 pool, M.lookup b1 pool) of
>          (Just i1, Just i2) -> do let newPool = M.insert b nextVertex pool
>                                   let newNextVertex = nextVertex + 1
>                                   put (newNextVertex, newPool)
>                                   tell.(++"\n") $ 
>                                     show nextVertex ++ "\t" ++
>                                     show l ++ "\t" ++ 
>                                     show i1 ++ "\t" ++ show i2
>          (_,_)              -> error $ show pool

Without pointers in haskell, bdd is either a constant or an internal node. We
get the functions label, left, and right for free.

> data BDD lbl = Const Bool
>              | Node { label :: lbl, 
>                       left  :: BDD lbl, 
>                       right :: BDD lbl }
>   deriving (Eq, Ord, Show)

The goal here is to compute a robdd from a formula. We define 
formulaToROBDD here

> formulaToROBDD :: Ord lbl => Formula lbl -> ROBDD lbl
> formulaToROBDD f = Root $ convert.simplify$f where

>   convert :: Ord lbl => Formula lbl -> BDD lbl

>   convert (TM_T) = error "simplify"
>   convert (TM_F) = error "simplify"

>   convert (TM_Var (V l)) = 
>     addVertex l (Const False) (Const True)

>   convert (TM_Not (TM_Var (V l))) =
>     addVertex l (Const True) (Const False)

>   convert (TM_Conj f1 f2) = evalState (conj (convert f1) (convert f2)) M.empty

>   convert (TM_Disj f1 f2) = evalState (disj (convert f1) (convert f2)) M.empty

>   convert (TM_Not f') = diff (Const True) $ convert f'

>   convert (TM_Exst (V l) f') = exists (convert f') l

BDDPool is unused, since we rely on structural equality rather than 
an equivalence relation to check (robdd1 :: BDD) == (robdd2 :: BDD)

Addvertex only takes care of eliminating nodes with same left and right sub-nodes

> addVertex :: Ord lbl => 
>              lbl -> BDD lbl -> BDD lbl -> 
>              BDD lbl
> addVertex l bdd1 bdd2 = 
>   if bdd1 == bdd2
>   then bdd1
>   else Node l bdd1 bdd2

The next step in the implementation is to define operations on robdds. To
avoid recomputation, we keep a table of parameters and results.

> type ComputeKey lbl   = (BDD lbl, BDD lbl)
> type Table lbl = Map (ComputeKey lbl) (BDD lbl)

conj :: Ord lbl => 
        (MonadState (BDDPool lbl) m, 
         MonadState (Table lbl) m) =>
        BDD lbl -> BDD lbl -> m (BDD lbl)

> conj :: Ord lbl => BDD lbl -> BDD lbl ->
>         State (Table lbl) (BDD lbl)

First, we have four trivial cases, which we won't save for recomputation

> conj (Const False) _  = return $ Const False
> conj _ (Const False)  = return $ Const False
> conj (Const True) bdd = return $ bdd
> conj bdd (Const True) = return $ bdd

After this, we need to examine the case where both are pointers
to internal nodes.

> conj b@(Node j b0 b1) b'@(Node j' b0' b1') = 
>   if b == b'
>   then return b
>   else do table <- get
>           case M.lookup (b, b') table of
>             Just bdd -> return bdd
>             Nothing ->
>               case M.lookup (b', b) table of 
>                 Just bdd -> return bdd
>                 Nothing -> case j `compare` j' of
>                   EQ -> do b0'' <- conj b0 b0'
>                            b1'' <- conj b1 b1'
>                            let bdd = addVertex j b0'' b1''
>                            put $ M.insert (b, b') bdd table
>                            return bdd
>                   LT -> do b0'' <- conj b0 b'
>                            b1'' <- conj b1 b'
>                            let bdd = addVertex j b0'' b1''
>                            put $ M.insert (b, b') bdd table
>                            return bdd
>                   GT -> do b0'' <- conj b b0'
>                            b1'' <- conj b b1'
>                            let bdd = addVertex j b0'' b1''
>                            put $ M.insert (b, b') bdd table
>                            return bdd

> disj :: Ord lbl => BDD lbl -> BDD lbl ->
>                    State (Table lbl) (BDD lbl)
> disj = error "disj"

> diff :: Ord lbl => BDD lbl -> BDD lbl -> (BDD lbl)
> diff = error "diff"

> exists :: Ord lbl => BDD lbl -> lbl -> BDD lbl
> exists = error "exists"

> t1,t2,t3,t4 :: ROBDD F.Label
> t1 = formulaToROBDD F.f1
> t2 = formulaToROBDD F.f2
> t3 = formulaToROBDD F.f3
> t4 = formulaToROBDD F.f4