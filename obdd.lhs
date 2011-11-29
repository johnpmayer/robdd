
> {-# OPTIONS_GHC -Wall #-}

This section defines the implementation for ordered binary decision diagrams.

> module OBDD where

> import Data.Maybe

> import Formula
> -- import Shannon

We have defined boolean variables in the module Formula; their definition
is copied here. Their implementation explicitly requires a total ordering 
< over the labels of variables.

---
type Label = Int

newtype Ord a => Variable a = V { label :: a }
  deriving (Eq, Ord)
---

OBDDs are made up of vertices, terminal and internal. All vertices are tagged
with the boolean formula that produces them. Terminal vertices are labeled
with a Boolean value. Internal vertices are labeled and have two subtrees

> data Ord lbl => OBDDVertex lbl
>   = Terminal { formula :: Formula lbl,
>                value   :: Bool }
>   | Internal { formula :: Formula lbl,
>                label   :: lbl,
>                left    :: OBDDVertex lbl, 
>                right   :: OBDDVertex lbl }
>   deriving Show

> newtype OBDD lbl = Root (OBDDVertex lbl)

> instance (Ord lbl, Show lbl) => Show (OBDD lbl) where
>   show = printOBDD

And finally we implement the function that computes an OBDD from any function

> buildOBDD :: Ord lbl => Formula lbl -> OBDD lbl
> buildOBDD f = Root $ builder f where

>   builder :: Ord lbl => Formula lbl -> OBDDVertex lbl
>   builder TM_T = Terminal TM_T True
>   builder TM_F = Terminal TM_F False
>   builder f'   = Internal f' (fromJust.minLabel $ f')
>                           (builder $ substLeft f' (fromJust.minLabel $ f'))
>                           (builder $ substRight f' (fromJust.minLabel $ f'))

> printOBDD :: (Ord lbl, Show lbl) => OBDD lbl -> String
> printOBDD (Root v) = printOBDDVertex 0 v where

>   printOBDDVertex :: (Ord lbl, Show lbl) => Int -> OBDDVertex lbl -> String
>   printOBDDVertex i v' = case v' of

>                           (Terminal _ b) -> 
>                             (replicate i '\t') ++ show b

>                           (Internal f' lbl l r) -> 
>                             (printOBDDVertex (i+1) l) ++ "\n" ++
>                             (replicate i '\t') ++
>                             (show (lbl, f')) ++ "\n" ++
>                             (printOBDDVertex (i+1) r)

Finally, we define a function for determining isomorphism of OBDDs

> isoOBDD :: Ord lbl => OBDD lbl -> OBDD lbl -> Bool
> isoOBDD (Root v1) (Root v2) = isoOBDDVertex v1 v2

> isoOBDDVertex :: Ord lbl => OBDDVertex lbl -> OBDDVertex lbl -> Bool
> isoOBDDVertex (Terminal _ b1) (Terminal _ b2) = b1 == b2
> isoOBDDVertex (Terminal _ _) (Internal _ _ _ _) = False
> isoOBDDVertex (Internal _ _ _ _) (Terminal _ _) = False
> isoOBDDVertex (Internal _ lbl1 l1 r1) (Internal _ lbl2 l2 r2) =
>   lbl1 == lbl2 &&
>   isoOBDDVertex l1 l2 &&
>   isoOBDDVertex r1 r2
