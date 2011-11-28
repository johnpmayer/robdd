
> {-# OPTIONS_GHC -Wall #-}

> module Shannon where

> import NeList
> import Formula

In this section, we implement the shannon expansion. To do so, we also
implement single-variable substitution for a labeled variable over a
formula, which will be used in our implementation of ROBDDs.

> shannon :: Formula -> Label -> Formula
> shannon f l = TM_Disj (Cons (TM_Conj 
>                               (Cons (TM_Not $ TM_Var (V l)) 
>                                 (Cons (left f l) Nil)))
>                             (Cons (TM_Conj 
>                                     (Cons (TM_Var (V l))
>                                       (Cons (right f l) Nil)))
>                                   Nil)) where

> left :: Formula -> Label -> Formula
> left = \f l -> (reduce $ subst l False f)

> right :: Formula -> Label -> Formula
> right = \f l -> (reduce $ subst l True f)

Subst recursively replaces all occurences of the variable in f with
either True or False, depending on the argument

> subst :: Label -> Bool -> Formula -> Formula
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

> reduce :: Formula -> Formula
> reduce TM_T         = TM_T
> reduce TM_F         = TM_F
> reduce v@(TM_Var _) = v
> reduce (TM_Not f)   = case reduce f of
>                         TM_T -> TM_F
>                         TM_F -> TM_T
>                         f'   -> TM_Not f'

> reduce (TM_Conj fs) = if neany (==TM_F) rfs
>                       then TM_F
>                       else case nedrop (==TM_T) rfs of
>                              []  -> TM_T
>                              [f] -> f
>                              fs' -> TM_Conj $ nebuild fs'
>                       where rfs = fmap reduce fs

> reduce (TM_Disj fs) = if neany (==TM_T) rfs
>                       then TM_T
>                       else case nedrop (==TM_F) rfs of
>                              []  -> TM_F
>                              [f] -> f
>                              fs' -> TM_Disj $ nebuild fs'
>                       where rfs = fmap reduce fs