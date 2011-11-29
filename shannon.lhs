
> {-# OPTIONS_GHC -Wall #-}

> module Shannon where

> import NeList
> import Formula

In this section, we implement the shannon expansion. To do so, we also
implement single-variable substitution for a labeled variable over a
formula, which will be used in our implementation of ROBDDs. Notice the
intentional omission of a outer call to simplify.

> shannon :: (Ord label) => Formula label -> label -> Formula label
> shannon f l = TM_Disj (Cons (TM_Conj 
>                               (Cons (TM_Not $ TM_Var (V l)) 
>                                 (Cons (substLeft f l) Nil)))
>                             (Cons (TM_Conj 
>                                     (Cons (TM_Var (V l))
>                                       (Cons (substRight f l) Nil)))
>                                   Nil))

The following functions compute the False and True substitutions, respectively.
While here only used as helper functions for shannon, they are defined at the
top level to be used later in ROBDD.

> substLeft :: (Ord label) => Formula label -> label -> Formula label
> substLeft = \f l -> (simplify $ subst l False f)

> substRight :: (Ord label) => Formula label -> label -> Formula label
> substRight = \f l -> (simplify $ subst l True f)

Subst recursively replaces all occurences of the variable in f with
either True or False, depending on the argument.

> subst :: Ord label => label -> Bool -> Formula label -> Formula label
> subst _ _ TM_T = TM_T
> subst _ _ TM_F = TM_F
> subst l b v@(TM_Var (V l')) = if l == l' 
>                               then if b 
>                                  then TM_T 
>                                  else TM_F
>                               else v
> subst l b (TM_Not f)        = TM_Not $ subst l b f
> subst l b (TM_Conj fs)      = TM_Conj $ fmap (subst l b) fs
> subst l b (TM_Disj fs)      = TM_Disj $ fmap (subst l b) fs

Next, simplify removes all boolean value terms and reduces conjunctions
and disjunctions where appropriate.

> simplify :: Ord label => Formula label -> Formula label
> simplify TM_T         = TM_T
> simplify TM_F         = TM_F
> simplify v@(TM_Var _) = v
> simplify (TM_Not f)   = case simplify f of
>                         TM_T -> TM_F
>                         TM_F -> TM_T
>                         f'   -> TM_Not f'

> simplify (TM_Conj fs) = if neany (==TM_F) rfs
>                       then TM_F
>                       else case nedrop (==TM_T) rfs of
>                              []  -> TM_T
>                              [f] -> f
>                              fs' -> TM_Conj $ nebuild fs'
>                       where rfs = fmap simplify fs

> simplify (TM_Disj fs) = if neany (==TM_T) rfs
>                       then TM_T
>                       else case nedrop (==TM_F) rfs of
>                              []  -> TM_F
>                              [f] -> f
>                              fs' -> TM_Disj $ nebuild fs'
>                       where rfs = fmap simplify fs
