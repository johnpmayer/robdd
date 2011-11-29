
> {-# OPTIONS_GHC -Wall #-}

> module Formula
> where

> import Data.Map (Map)
> import qualified Data.Map as M

We'll support labeled boolean variables, where (V 1) would correspond to 
the variable x1. We also support negation, conjunction, and disjunction.

> type Label = String

> newtype Ord a => Variable a = V { label :: a }
>   deriving (Eq, Ord)

> instance (Ord a, Show a) => Show (Variable a) where
>   show (V n) = show n

> x1, x2, x3, x4 :: Variable Label
> x1 = V "x1"
> x2 = V "x2"
> x3 = V "x3"
> x4 = V "x4"

In an earlier implementation disjunction and conjunction operated over
lists of formulae, but this became incompatible with robdd operations.
Additionally, existential quantification over labeled variables has been
added.

data Ord label => Formula label 
             = TM_T
             | TM_F
             | TM_Var (Variable label)
             | TM_Not (Formula label)
             | TM_Conj (List NonEmpty (Formula label))
             | TM_Disj (List NonEmpty (Formula label))
  deriving (Eq, Ord)

> data Ord label => Formula label 
>              = TM_T
>              | TM_F
>              | TM_Var (Variable label)
>              | TM_Not (Formula label)
>              | TM_Conj (Formula label) (Formula label)
>              | TM_Disj (Formula label) (Formula label)
>              | TM_Exst (Variable label) (Formula label)
>   deriving (Eq, Ord)

A custom show implementation is used for pretty printiing formulae

> instance (Ord label, Show label) => Show (Formula label) where
>   show TM_T           = "T"
>   show TM_F           = "F"
>   show (TM_Var v)     = show v
>   show (TM_Not f)     = '¬' : show f
>   --show (TM_Conj fs) = '(' : showHelper " ∧ " ")" fs
>   --show (TM_Disj fs) = '(' : showHelper " ∨ " ")" fs
>   show (TM_Conj f f') = "(" ++ show f ++ " ∧ " ++ show f' ++ ")"
>   show (TM_Disj f f') = "(" ++ show f ++ " ∧ " ++ show f' ++ ")"
>   show (TM_Exst l f)  = "∃" ++ show l ++ "." ++ show f ++ ""

> f1, f2, f3, f4, f5, f6 :: Formula Label
> f1 = TM_Var x1
> f2 = TM_Not (TM_Var x2)
> f3 = TM_Conj (TM_Var x3) (TM_Var x4)
> f4 = TM_Disj f2 f3
> f5 = TM_Exst x1 f1
> f6 = TM_Exst x2 f4

Next, given a formula an assignment over variables to boolan values, 
we determine if a formula is valid. An assignment is a mapping from
Labels to Booleans

> type Assignment label = Map (Variable label) Bool

> valid :: Ord label => Formula label -> Assignment label -> Bool
> valid f assign = case validWalker f assign of
>                    Just b -> b
>                    Nothing -> False
>                  where

Here, we use a helper function that produces a maybe bool. A nothing result
signifies that the assignment is incomplete, and subsequently insufficient
to determine the validity of the formula.

>   validWalker :: Ord label =>
>                  Formula label ->
>                  Assignment label ->
>                  Maybe Bool

Boolean values are trivial (and independent of the assignment!)

>   validWalker TM_T _ = return True
>   validWalker TM_F _ = return False

For variables, if a valuation is possible we produce the boolean, otherwise 
we indicate with a Nothing value that the validity cannot be determined.

>   validWalker (TM_Var v) a = M.lookup v a

For negation, iff the valuation of the contained formuala can be determined, 
so can its negation.

>   validWalker (TM_Not f') a = fmap not $ validWalker f' a

>   validWalker (TM_Conj f' f'') a = 
>     case (validWalker f' a, validWalker f'' a) of
>       (Nothing, _)       -> Nothing
>       (_, Nothing)       -> Nothing
>       (Just b1, Just b2) -> Just $ b1 && b2

>   validWalker (TM_Disj f' f'') a =
>     case (validWalker f' a, validWalker f'' a) of
>       (Just True, _)           -> Just True
>       (_, Just True)           -> Just True
>       (Just False, Just False) -> Just False
>       (_,_)                    -> Nothing

Validity of existentially qualified formulas is equal to the validity of
the disjunction of substituting the qualified variable with both True and 
False, respectivly.

>   validWalker (TM_Exst (V l) f') a = 
>     validWalker (TM_Disj (substLeft f' l) (substRight f' l)) a

Here are some assignments that satisfy the formulas defined at the top
of the file

> a1, a1', a2, a2', a3 :: Assignment Label
> a1  = M.insert x1 True  M.empty
> a1' = M.insert x2 False M.empty
> a2  = M.insert x2 False M.empty
> a2' = M.insert x2 True  M.empty
> a3  = M.insert x3 True (M.insert x4 True M.empty)

Now we define a function that, given a formula, computes the minimal label
among variables in the function, according to the total ordering defined
on the type of labels. It is possible that some formulas do not have a
minimum (TM_T, TM_F)

> minLabel :: Ord lbl => Formula lbl -> Maybe lbl
> minLabel TM_T           = Nothing
> minLabel TM_F           = Nothing
> minLabel (TM_Var (V l)) = Just l
> minLabel (TM_Not f)     = minLabel f
> minLabel (TM_Conj f f') = 
>   case (minLabel f, minLabel f') of
>     (Nothing, Nothing) -> Nothing
>     (Just l1, Just l2) -> Just $ min l1 l2
>     (Just l1, Nothing) -> Just l1
>     (Nothing, Just l2) -> Just l2
> minLabel (TM_Disj f f') = 
>   case (minLabel f, minLabel f') of
>     (Nothing, Nothing) -> Nothing
>     (Just l1, Just l2) -> Just $ min l1 l2
>     (Just l1, Nothing) -> Just l1
>     (Nothing, Just l2) -> Just l2
> minLabel (TM_Exst (V l) f) =
>   case minLabel f of
>     Nothing -> Just l
>     Just f'  -> Just $ min l f'

In this section, we implement the shannon expansion. To do so, we also
implement single-variable substitution for a labeled variable over a
formula, which will be used in our implementation of ROBDDs. Notice the
intentional omission of a outer call to simplify.

> shannon :: (Ord label) => Formula label -> label -> Formula label
> shannon f l = TM_Disj (TM_Conj (TM_Not $ TM_Var (V l)) (substLeft  f l))
>                       (TM_Conj          (TM_Var (V l)) (substRight f l))

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
> subst l b (TM_Conj f f')    = TM_Conj (subst l b f) (subst l b f')
> subst l b (TM_Disj f f')    = TM_Disj (subst l b f) (subst l b f')

> subst l b (TM_Exst v@(V l') f) = if l == l'
>                            then undefined
>                            else TM_Exst v (subst l b f)

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

> simplify c@(TM_Conj f f') = 
>   case (f, f') of
>     (TM_F, _)   -> TM_F
>     (_, TM_F)   -> TM_F
>     (TM_T, f'') -> f''
>     (f'', TM_T) -> f''
>     (_,_)       -> c

> simplify d@(TM_Disj f f') = 
>   case (f, f') of
>     (TM_T, _)   -> TM_T
>     (_, TM_T)   -> TM_T
>     (TM_F, f'') -> f''
>     (f'', TM_F) -> f''
>     (_,_)       -> d

> simplify (TM_Exst v f) = TM_Exst v $ simplify f