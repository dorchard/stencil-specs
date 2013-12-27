> {-# LANGUAGE GADTs, EmptyDataDecls, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
> {-# LANGUAGE TypeFamilies, FlexibleContexts, RebindableSyntax #-}

> import Data.Array

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

> fooSym :: (Num a) => StencilM a (Symmetrical (S Z)) a a
> fooSym = StencilM $ do a <- ix (Pos Z)
>                        b <- ix (Pos (S Z))
>                        c <- ix (Neg (S Z))
>                        return $ a + b + c 

---------------------------------
The following causes a type error as it violates the specification
of symmetry

> --  fooSymBroken :: (Num a) => StencilM a (Symmetrical (S Z)) a a
> -- fooSymBroken = StencilM $ do a <- ix (Pos Z)
> --                              b <- ix (Pos (S Z))
> --                              return $ a + b 


fooFwd has a 'forward' pattern to depth of 2

> fooFwd :: Num a => StencilM a (Forward (S (S Z))) a a
> fooFwd = StencilM $ do a <- ix (Pos Z)
>                        b <- ix (Pos (S Z))
>                        c <- ix (Pos (S (S Z)))
>                        return $ a + b + c

Indexed monad
------------------------------------------------

See [1],[2],[3] above.

> class IxMonad (m :: * -> * -> *) where
>     type MPlus m s t 
>     type MUnit m 

>     (>>=) ::  m r a -> (a -> m s b) -> m (MPlus m s r) b
>     return :: a -> m (MUnit m) a

>     fail :: String -> m () () 
>     fail = error "Fail not implemented"


Specification-indexed array reader monad
--------------------------------------------------

The following defines a kind of indexed reader monad 
(http://www.cl.cam.ac.uk/~dao29/drafts/ixmonad-eabstract.pdf)
for array stencil computations, with elemet type e to e'

> data ArrayReader e r e' = ArrayReader (SpecArray r e -> e')

1D array paired with the current "cursor" position

> data SpecArray x a = MkSA (Array Int a, Int) 

> instance IxMonad (ArrayReader e) where
>     type MPlus (ArrayReader e) s t = Append s t -- append specs
>     type MUnit (ArrayReader e) = HNil           -- empty spec

>     (ArrayReader f) >>= k = ArrayReader (\(MkSA a) -> let (ArrayReader f') = k (f (MkSA a))
>                                                       in f' (MkSA a))
>     return a = ArrayReader (\_ -> a)

Stencil constructor/wrapper, which sorts the spec pattern (using the Sort type family) 
since we do not know the order in which indexing will occur. 

> data StencilM a r x y where
>     StencilM :: (ArrayReader a spec y) -> StencilM a (Sort spec) x y


Array indexing
--------------------

> ix :: IntT x -> ArrayReader a (HCons x HNil) a
> ix n = ArrayReader (\(MkSA (a, cursor)) -> a ! (cursor + toValue n))


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
