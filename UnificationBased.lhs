> {-# LANGUAGE GADTs, EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances #-}
> {-# LANGUAGE TypeFamilies, FlexibleContexts, ConstraintKinds #-}
> {-# LANGUAGE TypeOperators #-}

> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE FunctionalDependencies #-}

> {-# LANGUAGE DataKinds #-}

> module Data.Array.Specs2 where

> import Data.Array

> data HNil
> data HCons x xs

> data HList t where
>     HNil :: HList HNil
>     HCons :: x -> HList xs -> HList (HCons x xs)

Type-level natural numbers and integers for relative indices

> data Z
> data S n 

> data Nat n where
>    Z :: Nat Z
>    S :: Nat n -> Nat (S n)

> natToInt :: Nat n -> Int
> natToInt Z = 0
> natToInt (S n) = 1 + natToInt n

> data Neg n

> data IntT n where
>    Neg :: Nat (S n) -> IntT (Neg (S n))
>    Pos :: Nat n -> IntT n

> intTtoInt :: IntT n -> Int
> intTtoInt (Pos n) = natToInt n
> intTtoInt (Neg n) = - natToInt n

> class ToValue t t' where
>     toValue :: t -> t'

> instance ToValue (Nat n) Int where
>     toValue n = natToInt n

> instance ToValue (IntT n) Int where
>     toValue n = intTtoInt n

> instance (ToValue m Int, ToValue n Int) => ToValue (m, n) (Int, Int) where
>     toValue (m, n) = (toValue m, toValue n)

Arrays with specifications 

> data SpecArray x a = MkSA (Array Int a)

Array indexing with specification

> (!!!) :: SpecArray (HCons x xs) a -> IntT x -> (a, SpecArray xs a)
> (MkSA x) !!! n = (x ! (toValue n), MkSA x)

> done :: SpecArray HNil a -> SpecArray xs a 
> done (MkSA x) = MkSA x

Forward-oriented stencils

> type Forward sten = Sort (HCons Z (ForwardP sten))

> type family ForwardP depth 
> type instance ForwardP Z     = HNil -- HCons Z HNil
> type instance ForwardP (S n) = HCons (S n) (ForwardP n)

Backward-oriented stencils

> type Backward sten = Sort (HCons Z (BackwardP sten))

> type family BackwardP depth
> type instance BackwardP Z     = HNil -- HCons Z HNil
> type instance BackwardP (S n) = HCons (Neg (S n)) (BackwardP n)  

> type family Append s t
> type instance Append HNil t = t
> type instance Append (HCons s ss) t = HCons s (Append ss t)

Symmetrical stencils (derived from Forward and Backward stencils of the same depth)

> type Symmetrical depth = Sort (HCons Z (Append (ForwardP depth) (BackwardP depth)))

Type-level sorting

> type family Fst t
> type instance Fst (a, b) = a

> type family Snd t 
> type instance Snd (a, b) = b

> type SortLeft n m = SortLeft' n m n m  

> type family SortLeft' n m p q 

> type instance SortLeft' Z Z p q = (p, q)
> type instance SortLeft' Z (S m) p q = (p, q)
> type instance SortLeft' (S m) Z p q = (q, p)
> type instance SortLeft' (S m) (S n) p q = SortLeft' m n p q

> type instance SortLeft' Z (Neg m) p q = (q, p)
> type instance SortLeft' (S m) (Neg n) p q = (q, p)
> type instance SortLeft' (Neg m) Z p q = (p, q)
> type instance SortLeft' (Neg m) (S n) p q = (p, q)
> type instance SortLeft' (Neg (S m)) (Neg (S n)) p q = SortLeft' (Neg m) (Neg n) p q

Single pass of bubble sort

> type family Bubble l
> type instance Bubble (HCons a HNil) = HCons a HNil
> type instance Bubble (HCons a (HCons b c)) = HCons (Fst (SortLeft a b))
>                                             (Bubble (HCons (Snd (SortLeft a b)) c))

N-passes of bubble for a list of length N 

> type family BSort l l'
> type instance BSort l HNil = l
> type instance BSort l (HCons x y) = BSort (Bubble l) y

> type Sort l = BSort l l

Stencil constructor

> data Stencil s a b where
>     Stencil :: (SpecArray spec a -> b) -> Stencil (Sort spec) a b

> fooFwd :: (Num a) => Stencil (Forward (S (S Z))) a a
> fooFwd = Stencil $ \x -> let (a, x')  = x !!! (Pos Z)
>                              (b, x2) = x3 !!! (Pos (S Z))
>                              (c, x3) = x' !!! (Pos (S (S Z)))
>                              xa' = done x2
>                          in b + c + a

> fooSym :: (Num a) => Stencil (Symmetrical (S Z)) a a
> fooSym = Stencil $ \x -> let (a, x2) = x !!! (Pos Z)
>                              (b, x3) = x2 !!! (Pos (S Z))
>                              (c, x4) = x3 !!! (Neg (S Z))
>                              x5 = done x4
>                          in a + b + c

