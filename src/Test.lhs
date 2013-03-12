> {-# LANGUAGE ConstraintKinds #-}

> import Data.Array.Specs
> import Data.Array

> foo_a :: SpecArray i (HCons (Pos Z) (HCons (Pos (S Z)) (HCons (Neg (S Z)) HNil))) Int
> foo_a = undefined

> f :: (Num a, Symmetry (S Z) as) => SpecArray Int as a -> a
> f x = x !!! (Pos Z) + x !!! (Pos (S Z)) + x !!! (Neg (S Z))

 g :: (Num a, Forward (S Z) as) => SpecArray i as a -> a
 g u = u !!! (Pos Z) + (u !!! (Pos (S Z)))

 h :: (Num a, Backward (S Z) as) => SpecArray i as a -> a
 h u = u !!! (Pos Z) + (u !!! (Neg (S Z)))

 f' :: (Num a, Forward (S Z) as, Backward (S Z) as) => SpecArray i as a -> a
 f' = f

 (!!!) :: (Member (m, n) ns, HList ns) => SpecArray i ns a -> (IntT m, IntT n) -> a
 (!!!) = undefined

 f2 :: (Num a, Symmetry (S Z, S Z) as) => SpecArray i as a -> a
 f2 x =   x!!!(Pos Z, Pos Z)  
        + x!!!(Pos (S Z), Pos Z)
        + x!!!(Pos Z, Pos (S Z))
        + x!!!(Neg (S Z), Pos Z)
        + x!!!(Pos Z, Neg (S Z))

 f3 x =   x!!!(Pos Z, Pos Z)
        + x!!!(Pos Z, Pos (S Z))
        + x!!!(Pos Z, Neg (S Z))
        + x!!!(Pos (S Z), Pos Z)