> {-# LANGUAGE GADTs, EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances #-}
> {-# LANGUAGE TypeFamilies, FlexibleContexts, ConstraintKinds, OverlappingInstances #-}
> {-# LANGUAGE TypeOperators #-}

> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE FunctionalDependencies #-}

> {-# LANGUAGE DataKinds #-}

> module Data.Array.Specs where
>                         -- ((!!!), (:=)(..), HCons, HNil,
>                         -- Z(), S(), Neg(),  
>                         -- Nat(..), IntT(..), Member,
>                         -- Symmetrical, Backward, Forward,
>                         -- Symm2
>                         -- ) where

> import Data.Array

> import Data.HList

> import GHC.Prim

 data HNil
 data HCons x xs

 data HList t where
     HNil :: HList HNil
     HCons :: x -> HList xs -> HList (Cons x xs)

 type HList t = () :: Constraint

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

 data SpecArray x i a = SpecArray (Array i a)

> data x := a = Spec a

Array indexing with specification

> (!!!) :: (Member n ns, HList ns, ToValue n i, Ix i) => (ns := (Array i a)) -> n -> a
> (Spec x) !!! n = x ! (toValue n)

> class Member x xs 
> instance Member x (HCons x xs)
> instance (Member x xs) => Member x (HCons y xs)

> type SpecBase as = HList as

Forward-oriented stencils 

> type Forward depth a = (SpecBase a, ForwardP depth a)

> type family ForwardP depth a :: Constraint
> type instance ForwardP Z a = (Member (IntT Z) a)

> type instance ForwardP (S n) a = (Member (IntT (S n)) a,
>                                    ForwardP n a)

> type instance ForwardP (Z, Z) a = (Member (IntT Z, IntT Z) a)

> type instance ForwardP (S m, Z) a = (Member (IntT (S m), IntT Z) a,
>                                      ForwardP (m, Z) a)

> type instance ForwardP (Z, S n) a = (Member (IntT Z, IntT (S n)) a,
>                                      ForwardP (Z, n) a)

> type instance ForwardP (S m, S n) a = (Member (IntT (S m), IntT (S n)) a,
>                                        ForwardP (S m, n) a,
>                                        ForwardP (m, S n) a,
>                                        ForwardP (m, n) a)

Backward-oriented stencils

> type Backward depth a = (SpecBase a, BackwardP depth a)

> type family BackwardP depth a :: Constraint

> type instance BackwardP Z as = Member (IntT Z) as

> type instance BackwardP (S n) as = (Member (IntT (Neg (S n))) as,
>                                     BackwardP n as)

> type instance BackwardP (Z, Z) a = (Member (IntT Z, IntT Z) a)

> type instance BackwardP (S m, Z) a = (Member (IntT (Neg (S m)), IntT Z) a,
>                                       BackwardP (m, Z) a)

> type instance BackwardP (Z, S n) a = (Member (IntT Z, IntT (Neg (S n))) a,
>                                       BackwardP (Z, n) a)

> type instance BackwardP (S m, S n) a = (Member (IntT (Neg (S m)), IntT (Neg (S n))) a,
>                                         BackwardP (S m, n) a,
>                                         BackwardP (m, S n) a,
>                                         BackwardP (m, n) a)

Symmetrical stencils (derived from Forward and Backward stencils of the same depth)

> type Symmetrical depth a = (SpecBase a, ForwardP depth a, BackwardP depth a)


 class Symm2 n x
 instance (HList x, Member (IntT Z) x) => Symm2 Z x
 instance (HList x, Member (IntT (S n)) x, Symm2 n x) => Symm2 (S n) x
 instance (HList x, Member (IntT (Neg (S n))) x, Symm2 (Neg n) x) => Symm2 (Neg (S n)) x

Playing around with some other options

> type Symm2 x = SymmAB x x

> type family SymmAB x a :: Constraint
> type instance SymmAB HNil a = ()
> type instance SymmAB (HCons (IntT (Neg x)) xs) a = (Member (IntT (Neg x)) a,
>                                                     Member (IntT x) a, SymmAB xs a)

> type instance SymmAB (HCons (IntT Z) xs) a = (Member (IntT Z) a, SymmAB xs a)
> type instance SymmAB (HCons (IntT (S n)) xs) a = (Member (IntT (S n)) a,
>                                                   Member (IntT (Neg (S n))) a, SymmAB xs a)


 type family Foo (t :: Constraint) :: Constraint
 type instance Foo () = ()
 type instance Foo ((Member (IntT (Neg n)) xs), rs) = (Member (IntT (Neg n)) xs,
                                                       Member (IntT n) xs,
                                                       Foo rs)
 type instance Foo ((Member (IntT (S n)) xs), rs) = (Member (IntT (Neg (S n))) xs,
                                                     Member (IntT (S n)) xs,
                                                     Foo rs)
 data Sym t where
     Sym :: (Foo c => Spec x (Array Int a) -> a) -> Sym a


Inverse

 (!!!<) :: (NotMember n negs, HList negs, ToValue n i, Ix i) => (negs := (Array i a)) -> n -> a
 (Spec x) !!!< n = x ! (toValue n)

 class NotMemberP x xs 
 instance NotMemberP x HNil
 instance (NotMemberP x xs) => NotMemberP x (HCons y xs)

> data False
> data True

> class MemberPf x xs r | x xs -> r
> instance MemberPf x HNil False
> instance MemberPf x (HCons x xs) True
> instance (MemberPf x xs t) => MemberPf x (HCons y xs) t

 type family NotMember x (xs :: HList)  :: Constraint
 type instance NotMember x HNil = (MemberPf x HNil False)
 type instance NotMember x (HCons y xs) = (MemberPf x (HCons y xs) False, NotMember x xs)

 foop :: (Num a, NSymm (S Z) x, HList x) => (x := (Array Int a)) -> a
 foop x = x !!!< (Pos (S Z)) --  x !!!< (Neg (S Z))


> ntest :: MemberPf n xs False => n -> xs -> ()
> ntest _ _ = ()


> type family NSymm depth x :: Constraint
> type instance NSymm Z x = (MemberPf (IntT Z) x False)
> type instance NSymm (S n) x = (MemberPf (IntT (S n)) x False,
>                                MemberPf (IntT (Neg (S n))) x False,
>                                NSymm (IntT n) x)
> type instance NSymm (Neg (S n)) x = (MemberPf (IntT (S n)) x False,
>                                      MemberPf (IntT (Neg (S n))) x False,
>                                      NSymm (IntT (Neg n)) x)
>     

> type family TSymm depth
> type instance TSymm Z = HNil
> type instance TSymm (S n) = HCons (IntT (S n)) (HCons (IntT (Neg (S n))) (TSymm n))

> foopa :: (Num a, Symmetrical (S Z) xs, xs ~ TSymm (S Z)) => (xs := (Array Int a)) -> a
> foopa x = x !!! (Pos (S Z))  -- + x !!! (Neg (S Z))