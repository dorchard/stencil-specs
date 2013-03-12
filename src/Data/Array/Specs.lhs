> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE EmptyDataDecls #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE OverlappingInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE UndecidableInstances #-}

> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE ConstraintKinds #-}

> module Data.Array.Specs((!!!), HCons, HNil, 
>                         Z(), S(), Neg(), Pos(), 
>                         Nat(..), IntT(..), Member,
>                         toValue,
>                         Symmetry, Backward, Forward, SpecArray) where

> import Data.Array
> import Data.HList
> import GHC.Prim

> data Z
> data S n 

> data Nat n where
>     Z :: Nat Z
>     S :: Nat n -> Nat (S n)

> natToInt :: Nat n -> Int
> natToInt Z = 0
> natToInt (S n) = 1 + natToInt n

> data Neg n
> data Pos n

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

> data SpecArray i as a = SpecArray (Array i a)

> class Member x xs 
> instance Member x (HCons x xs)
> instance (Member x xs) => Member x (HCons y xs)

> (!!!) :: (Member n ns, HList ns, ToValue n i, Ix i) => SpecArray i ns a -> n -> a
> (!!!) (SpecArray x) n = x ! (toValue n)

> type SpecBase as = HList as 

> type family Symmetry depth as :: Constraint
> type instance Symmetry Z as = (SpecBase as, Member (IntT Z) as, ToValue (IntT Z) Int) 
> type instance Symmetry (S n) as = (Member (IntT (S n)) as, Member (IntT (Neg (S n))) as, Symmetry n as, ToValue (IntT (S n)) Int, ToValue (IntT (Neg (S n))) Int) 

> type family Forward depth as :: Constraint
> type instance Forward Z as = (SpecBase as, Member (IntT Z) as)
> type instance Forward (S n) as = (Member (IntT (S n)) as, Forward n as)

> type family Backward depth as :: Constraint
> type instance Backward Z as = (SpecBase as, Member (IntT Z) as)
> type instance Backward (S n) as = (Member (IntT (Neg (S n))) as, Backward n as)

> type instance Symmetry (Z, Z) as = (SpecBase as, Member (IntT Z, IntT Z) as)
> type instance Symmetry (S m, Z) as = (SpecBase as,
>                                       Member (IntT (S m), IntT Z) as, 
>                                       Member (IntT (Neg (S m)), IntT Z) as,
>                                       Symmetry (m, Z) as)
> type instance Symmetry (Z, S n) as = (SpecBase as,
>                                       Member (IntT Z, IntT (S n)) as,
>                                       Member (IntT Z, IntT (Neg (S n))) as,
>                                       Symmetry (Z, n) as)
> type instance Symmetry (S m, S n) as = (Member (IntT (S m), IntT (S n)) as,
>                                         Member (IntT (S m), IntT (S n)) as,
>                                         Member (IntT (Neg (S m)), IntT (S n)) as,
>                                         Member (IntT (Neg (S m)), IntT (Neg (S n))) as,
>                                         Symmetry (m, S n) as,
>                                         Symmetry (S m, n) as,
>                                         Symmetry (m, n) as)

