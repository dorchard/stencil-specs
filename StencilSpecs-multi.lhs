> {-# LANGUAGE GADTs, EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
> {-# LANGUAGE TypeFamilies, FlexibleContexts, RebindableSyntax #-}

> {-# LANGUAGE NoMonomorphismRestriction #-}

> import Control.IxMonad
> import Data.Array
> import Unsafe.Coerce

Preface
------------------------------------------------

The following shows how to use Haskell's type system for defining data access pattern specifications
on stencil computations (common in finite element approaches). This is defined here only for
one-dimensional arrays. It uses some type-level machinery
(type families and GADTs) and indexed monads [1], [2] (the dual of indexed comonads [3]) to abstract
the composition of computations with specifications. 

[1] http://www.cl.cam.ac.uk/~dao29/drafts/ixmonad-eabstract.pdf
[2] https://github.com/dorchard/ixmonad
[3] http://www.cl.cam.ac.uk/~dao29/publ/coeffects-icalp13.pdf

Note, this also uses Haskell's "rebindable syntax option" so that do notation can be redefined
over indexed monads. We therefore need to import a whole load of stuff from Prelude manually:

> import Prelude hiding (Monad(..)) 

Example stencils with data access specifications
------------------------------------------------

Stencils are defined in terms of "relative" indexing operations relative to a cursor
that is paired with an array. The following (fooSym) defines
a three-point symmetrical stencil to depth of 1, indexing the current
position (at offset 0, written Pos Z), at offset 1 (written (Pos (S Z))), and
offset -1 (written (Neg (S Z))). 

> fooSym :: (Num a) => Stencil (Symmetrical (S Z)) a a
> fooSym = Stencil $ do a <- ix (Pos Z)
>                       b <- ix (Pos (S Z))
>                       c <- ix (Neg (S Z))
>                       return $ a + b + c 

The following is a binary stencil taking two arrays


> fooSym2 :: (Num a) => StencilN (S (S Z)) (HCons (Forward (S Z)) (HCons (Forward (S (S Z))) HNil)) a a
> fooSym2 = StencilN $ 
>            do uc <- ixN Z (Pos Z)
>               ur <- ixN Z (Pos (S Z))
>                    
>               vc <- ixN (S Z) (Pos Z)
>               vr <- ixN (S Z) (Pos (S Z))
>               vrr <- ixN (S Z) (Pos (S (S Z)))
 
>               return $ uc + ur + vc + vr + vrr



---------------------------------
The following causes a type error as it violates the specification
of symmetry

> --  fooSymBroken :: (Num a) => Stencil (Symmetrical (S Z)) a a
> -- fooSymBroken = Stencil $ do a <- ix (Pos Z)
> --                              b <- ix (Pos (S Z))
> --                              return $ a + b 


fooFwd has a 'forward' pattern to depth of 2

> fooFwd :: Num a => Stencil (Forward (S (S Z))) a a
> fooFwd = Stencil $ do a <- ix (Pos Z)
>                       b <- ix (Pos (S Z))
>                       c <- ix (Pos (S (S Z)))
>                       return $ a + b + c


Specification-indexed array reader monad
--------------------------------------------------

The following defines a kind of indexed reader monad 
(http://www.cl.cam.ac.uk/~dao29/drafts/ixmonad-eabstract.pdf)
for array stencil computations, with elemet type e to e'

> data SAVector n t e where
>     SAVNil :: SAVector Z HNil e
>     SAVCons :: (SpecArray r e) -> SAVector n rs e -> SAVector (S n) (HCons r rs) e

> data NArrayReader n e r e' = NArrayReader (SAVector n r e -> e')


> data ArrayReader e r e' = ArrayReader (SpecArray r e -> e')

1D array paired with the current "cursor" position

> data SpecArray x a = MkSA (Array Int a, Int) 

> instance IxMonad (ArrayReader e) where
>     type Plus (ArrayReader e) s t = Append s t -- append specs
>     type Unit (ArrayReader e) = HNil           -- empty spec

>     (ArrayReader f) >>= k = ArrayReader (\(MkSA a) -> let (ArrayReader f') = k (f (MkSA a))
>                                                       in f' (MkSA a))
>     return a = ArrayReader (\_ -> a)


n-tuple of 1D arrays 

> type family Promote n x
> type instance Promote Z x = HNil
> type instance Promote (S n) x = HCons x (Promote n x)

> instance IxMonad (NArrayReader n e) where
>     type Plus (NArrayReader n e) s t = VAppend n s t -- append specs
>     type Unit (NArrayReader n e)     = Promote n HNil -- empty spec

>     (NArrayReader f) >>= k = NArrayReader (\x -> let (NArrayReader f') = k (f $ unsafeCoerce x)
>                                                  in f' (unsafeCoerce x))

>     return a = NArrayReader (\_ -> a)


Stencil constructor/wrapper, which sorts the spec pattern (using the Sort type family) 
since we do not know the order in which indexing will occur. 

> data Stencil r x y where
>     Stencil :: (ArrayReader x spec y) -> Stencil (Sort spec) x y

N-tuple version

> data StencilN n r x y where
>     StencilN :: (NArrayReader n x spec y) -> StencilN n (VSort spec) x y


Array indexing
--------------------

Unary stencil indexing is straightword

> ix :: IntT x -> ArrayReader a (HCons x HNil) a
> ix n = ArrayReader (\(MkSA (a, cursor)) -> a ! (cursor + toValue n))

Indexing for n-ary stencils is a little more complex

> ixN :: (IndexV m n, LT m n) =>  Nat m -> IntT i -> NArrayReader n a (InjectAt m n i) a
> ixN m i = NArrayReader (\x -> let (MkSA (a, cursor)) = projV m x
>                               in a ! (cursor + toValue i))


i.e. index the mth array of n with index i

`InjectAt m n i` creates a vector of size n where the m'th position is a singleton 
list with index i and everywhere else is an empty list

> type family   InjectAt m n r
> type instance InjectAt Z Z r = HNil
> type instance InjectAt Z (S n) r = HCons (HCons r HNil) (Rest n)
> type instance InjectAt (S m) (S n) r = HCons HNil (InjectAt m n r)

> type family Rest n 
> type instance Rest Z = HNil
> type instance Rest (S n) = HCons HNil (Rest n)

`projV m` projects the mth SpecArray out of an n-tuple of SpecArrays (and ProjV computes the type-level version)

> class LT m n => IndexV m n where
>     projV :: Nat m -> SAVector n specs e -> SpecArray (ProjV m specs) e

> instance IndexV Z (S n) where
>     projV Z (SAVCons x _) = x

> instance (LT m n, IndexV m n) => IndexV (S m) (S n) where
>     projV (S n) (SAVCons x xs) = projV n xs

> type family ProjV n ts
> type instance ProjV Z (HCons x xs) = x
> type instance ProjV (S n) (HCons x xs) = ProjV n xs

Specification definitions
------------------------------------------------

Forward-oriented stencil specification

> type Forward sten = Sort (HCons Z (ForwardP sten))

> -- ForwardP excludes the zero point
> type family ForwardP depth 
> type instance ForwardP Z     = HNil
> type instance ForwardP (S n) = HCons (S n) (ForwardP n)

Symmetrical stencils (derived from Forward and Backward stencils of the same depth)

> type Symmetrical depth = Sort (HCons Z (Append (ForwardP depth) (BackwardP depth)))

Backward-oriented stencils

> type Backward sten = Sort (HCons Z (BackwardP sten))

> type family BackwardP depth
> type instance BackwardP Z     = HNil
> type instance BackwardP (S n) = HCons (Neg (S n)) (BackwardP n)  

Type-level lists
------------------------------------

> type family Append s t
> type instance Append HNil t = t
> type instance Append (HCons s ss) t = HCons s (Append ss t)

> data HNil
> data HCons x xs

> data HList t where
>     HNil :: HList HNil
>     HCons :: x -> HList xs -> HList (HCons x xs)

List sorting uses bubble sort (since this is easy to define inductively and for
the type system to handle!)

> type Sort l = BSort l l

N-passes of bubble for a list of length N 

> type family BSort l l'
> type instance BSort l HNil = l
> type instance BSort l (HCons x y) = BSort (Bubble l) y

Type-level sorting

> type family Fst t
> type instance Fst (a, b) = a

> type family Snd t 
> type instance Snd (a, b) = b

Single pass of bubble sort

> type family Bubble l
> type instance Bubble (HCons a HNil) = HCons a HNil
> type instance Bubble (HCons a (HCons b c)) = HCons (Fst (SortLeft a b))
>                                             (Bubble (HCons (Snd (SortLeft a b)) c))

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

Type-level sized vectors
---------------------------

> data Vector n t where
>     VNil :: Vector Z HNil
>     VCons :: x -> Vector n xs -> Vector (S n) (HCons x xs)

Poinwise sort a vector of lists

> type family VSort l  
> type instance VSort HNil = HNil
> type instance VSort (HCons x xs) = HCons (Sort x) (VSort xs)

Pointwise append if vectors of size n

> type family VAppend n s t
> type instance VAppend Z HNil HNil = HNil
> type instance VAppend (S n) (HCons s ss) (HCons t ts) = HCons (Append s t) (VAppend n ss ts)



Type-level integers
---------------------------

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

Note that zero is "positive"

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

> class LT a b where
> instance LT Z (S n) where
> instance LT n m => LT (S n) (S m) where

