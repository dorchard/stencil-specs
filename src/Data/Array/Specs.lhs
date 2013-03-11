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

> {-# LANGUAGE ImplicitParams #-}

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE PolyKinds #-}

> {-# LANGUAGE RankNTypes #-}


> import Data.HList
> import GHC.Prim

> data Z
> data S n 

> data Nat n where
>     Z :: Nat Z
>     S :: Nat n -> Nat (S n)

> data Neg n
> data Pos n

> data IntT n where
>    Neg :: Nat (S n) -> IntT (Neg (S n))
>    Pos :: Nat n -> IntT (Pos n)

> class ToValue t t' | t -> t' where
>     toValue :: t -> Int

> instance ToValue Z Int where
>     toValue Z = 0

> instance ToValue n => ToValue (S n) Int where
>     toValue (S n) = 1 + (toValue n)

> instance (ToValue n) => ToValue (Pos n) Int where
>     toValue n = toValue n

> instance (ToValue n) => ToValue (Neg n) Int where
>     toValue n = - toValue n

> instance (ToValue m, ToValue n) => ToValue (m, n) where
>     toValue (m, n) = (toValue m, toValue n)

> type SpecArray i as a = Array i a

> class Member x xs 
> instance Member x (HCons x xs)
> instance (Member x xs) => Member x (HCons y xs)

> (!!!) :: (Member n ns, HList ns) => SpecArray i ns a -> IntT n -> a
> (!!!) x n = 

> data Nil
> data Cons (a :: Nat) (b :: *) 

> data List t where
>     Nil :: List Nil
>     Cons :: forall (t :: Nat) ts . t -> List ts -> List (Cons t ts)

> test :: SpecArray i (Cons 0 HNil) a
> test = undefined

> foo_a :: SpecArray i (HCons (Pos Z) (HCons (Pos (S Z)) (HCons (Neg (S Z)) HNil))) Int
> foo_a = undefined

 class Symmetry xs as
 instance (Member (Pos Z) as) => Symmetry HNil as
 instance (Symmetry xs as,
           Member (Neg n) as) => Symmetry (HCons (Pos n) xs) as
 instance (Symmetry xs as,
           Member (Pos n) as) => Symmetry (HCons (Neg n) xs) as

 f :: (Symmetry xs xs) => SpecArray i xs a -> a

> f :: (Num a, Symmetry (S Z) as) => SpecArray i as a -> a
> f x = x !!! (Pos Z) + x !!! (Pos (S Z)) + x !!! (Neg (S Z))

> type SpecBase as = HList as 

> type family Symmetry depth as :: Constraint
> type instance Symmetry Z as = (SpecBase as, Member (Pos Z) as) 
> type instance Symmetry (S n) as = (Member (Pos (S n)) as, Member (Neg (S n)) as, Symmetry n as) 

> type family Forward depth as :: Constraint
> type instance Forward Z as = (SpecBase as, Member (Pos Z) as)
> type instance Forward (S n) as = (Member (Pos (S n)) as, Forward n as)

> type family Backward depth as :: Constraint
> type instance Backward Z as = (SpecBase as, Member (Pos Z) as)
> type instance Backward (S n) as = (Member (Neg (S n)) as, Backward n as)

> g :: (Num a, Forward (S Z) as) => SpecArray i as a -> a
> g u = u !!! (Pos Z) + (u !!! (Pos (S Z)))

> h :: (Num a, Backward (S Z) as) => SpecArray i as a -> a
> h u = u !!! (Pos Z) + (u !!! (Neg (S Z)))

> f' :: (Num a, Forward (S Z) as, Backward (S Z) as) => SpecArray i as a -> a
> f' = f

> (!!!!) :: (Member (m, n) ns, HList ns) => SpecArray i ns a -> (IntT m, IntT n) -> a
> (!!!!) = undefined

> type instance Symmetry (Z, Z) as = (SpecBase as, Member (Pos Z, Pos Z) as)
> type instance Symmetry (S m, Z) as = (SpecBase as,
>                                       Member (Pos (S m), Pos Z) as, 
>                                       Member (Neg (S m), Pos Z) as,
>                                       Symmetry (m, Z) as)
> type instance Symmetry (Z, S n) as = (SpecBase as,
>                                       Member (Pos Z, Pos (S n)) as,
>                                       Member (Pos Z, Neg (S n)) as,
>                                       Symmetry (Z, n) as)
> type instance Symmetry (S m, S n) as = (Member (Pos (S m), Pos (S n)) as,
>                                         Member (Pos (S m), Neg (S n)) as,
>                                         Member (Neg (S m), Pos (S n)) as,
>                                         Member (Neg (S m), Neg (S n)) as,
>                                         Symmetry (m, S n) as,
>                                         Symmetry (S m, n) as,
>                                         Symmetry (m, n) as)

> f2 :: (Num a, Symmetry (S Z, S Z) as) => SpecArray i as a -> a
> f2 x =   x!!!!(Pos Z, Pos Z)  
>        + x!!!!(Pos (S Z), Pos Z)
>        + x!!!!(Pos Z, Pos (S Z))
>        + x!!!!(Neg (S Z), Pos Z)
>        + x!!!!(Pos Z, Neg (S Z))

The following makes the type system diverge/run of stack space

 type Symm as = SymmP Z as
 type family SymmP n as :: Constraint
 type instance SymmP Z as = (Member (Pos Z) as, SymmP (S Z) as)
 type instance SymmP (S n) as = (Member (Neg n) as, Member (Pos n) as, SymmP (S (S n)) as)

 ef :: (Num a, Symm as) => SpecArray i as a -> a
 ef x = x !!! (Pos Z) + x !!! (Pos (S Z)) + x !!! (Neg (S Z))

Rewrite to make specification shorter?

 type family Prev n
 type instance Prev Z = Z
 type instance Prev (S n) = n

 type family Symma depth as :: Constraint
 type instance Symma Z as = (SpecBase as, Member (Pos Z) as) 
 type instance Symma n as = (Member (Pos n) as, Member (Neg n) as, Symma (Prev n) as)

 type instance Symma (Z, Z) as = (SpecBase as, Member (Pos Z, Pos Z) as)
 type instance Symma (m, n) as = (Member (Pos m, Pos n) as,
                                  Member (Pos m, Neg n) as,
                                  Member (Neg m, Pos n) as,
                                  Member (Neg m, Neg n) as,
                                  Symma (Prev m, n) as,
                                  Symma (m, Prev n) as,
                                  Symma (Prev m, Prev n) as)

> data F
> data T

 -- symmetry in our dimension
 type family SymmA dim d as
 type instance SymmA F d as = (SpecBase as)
 type instance SymmA T d as = Symmetry d as
 type instance SymmA (F, T) d as =  
 type instance SymmA (T, F) d as =
 type instance SymmA (T, T) d as =


> f3 x =   x!!!!(Pos Z, Pos Z)
>        + x!!!!(Pos Z, Pos (S Z))
>        + x!!!!(Pos Z, Neg (S Z))
>        + x!!!!(Pos (S Z), Pos Z)