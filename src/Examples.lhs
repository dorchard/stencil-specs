> {-# LANGUAGE ConstraintKinds #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE RankNTypes #-}

> import Data.Array.Specs
> import Data.Array

> f :: (Num a, Symmetrical (S Z) x) => Spec x (Array Int a) -> a
> f x = x !!! (Pos Z) + x !!! (Pos (S Z)) + x !!! (Neg (S Z))

> g :: (Num a, Forward (S Z) x) => Spec x (Array Int a) -> a
> g u = u !!! (Pos Z) + (u !!! (Pos (S Z)))

> h :: (Num a, Backward (S Z) x) => Spec x (Array Int a) -> a
> h u = u !!! (Pos Z) + (u !!! (Neg (S Z)))

> f' :: (Num a, Forward (S Z) x, Backward (S Z) x) => Spec x (Array Int a) -> a
> f' = f

> f2 :: (Num a, Symmetrical (S Z, S Z) x) => Spec x (Array (Int, Int) a) -> a
> f2 x =   x!!!(Pos Z, Pos Z)  
>        + x!!!(Pos (S Z), Pos Z)
>        + x!!!(Pos Z, Pos (S Z))
>        + x!!!(Neg (S Z), Pos Z)
>        + x!!!(Pos Z, Neg (S Z))

> f3 :: (Num a, Symmetrical (Z, S Z) x, Forward (S Z, Z) x) => Spec x (Array (Int, Int) a) -> a
> f3 x =   x!!!(Pos Z, Pos Z)
>        + x!!!(Pos Z, Pos (S Z))
>        + x!!!(Pos Z, Neg (S Z))
>        + x!!!(Pos (S Z), Pos Z)

> f4 :: (Num a, Symmetrical (S Z, S Z) x) => Spec x (Array (Int, Int) a) -> a
> f4 x =   x!!!(Pos Z, Pos Z)
>        + x!!!(Pos Z, Pos (S Z))
>        + x!!!(Pos (S Z), Pos Z)
>        + x!!!(Pos Z, Neg (S Z))
>        + x!!!(Neg (S Z), Pos Z)

> x :: Spec (HCons (IntT (S Z)) (HCons (IntT Z) (HCons (IntT (Neg (S Z))) HNil))) (Array Int Int)
> x = Spec (listArray (0 :: Int, 5 :: Int) [0..5])

Example of something that should probably be disallowed but is currently allowed
because 

> f5 :: (Num a, Symmetrical (S Z, S Z) x) => Spec x (Array (Int, Int) a) -> a
> f5 x =   x!!!(Pos Z, Pos Z)
>        + x!!!(Pos Z, Pos (S Z))
>        + x!!!(Pos (S Z), Pos Z)
>        + x!!!(Pos Z, Neg (S Z))
>        + x!!!(Neg (S Z), Pos Z)
>        + x!!!(Pos (S Z), Pos (S Z))

 ef :: (Num a, SymmAB x x) => Spec x (Array Int a) -> a
 ef x = x !!! (Pos Z) + x !!! (Pos (S Z)) + x !!! (Neg (S Z))

 f6 :: (Num a, SymmA x) => Spec x (Array (Int, Int) a) -> a
 f6 x =   x!!!(Pos Z, Pos Z)
        + x!!!(Pos Z, Pos (S Z))
        + x!!!(Pos (S Z), Pos Z)
        + x!!!(Pos Z, Neg (S Z))
        + x!!!(Neg (S Z), Pos Z)
        + x!!!(Pos (S Z), Pos (S Z))

 

> ef :: Num a => Sym a
> ef = Sym $ \x -> (x !!! (Pos Z)) + (x !!! (Pos (S Z))) + (x !!! (Neg (S Z)))