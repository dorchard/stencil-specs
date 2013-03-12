> {-# LANGUAGE ConstraintKinds #-}
> {-# LANGUAGE FlexibleContexts #-}

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