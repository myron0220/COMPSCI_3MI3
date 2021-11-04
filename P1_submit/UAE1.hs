module Lib
    ( someFunc,
      ssos,
      eval
    ) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- 1.1
data T = IfThenElse T T T
       | Succ T
       | Pred T
       | IsZero T
       | BV BVSub
       | NV NVSub
    deriving (Eq, Show)

data BVSub = Tru
           | Fal
        deriving (Eq, Show)
         
data NVSub = Zero 
           | SuccVal NVSub  -- Should take care here.
        deriving (Eq, Show)
       

-- 1.2
-- small-steps operational semantics
ssos :: T -> T
ssos (IfThenElse (BV Tru) t2 t3) = t2
ssos (IfThenElse (BV Fal) t2 t3) = t3
ssos (IfThenElse t1 t2 t3) = IfThenElse t1 t2 t3
ssos (Succ (NV nv)) = NV (SuccVal nv) -- transform a successor to a value-successor
ssos (Succ t1) = Succ t1
ssos (Pred (NV Zero)) = NV Zero
ssos (Pred (NV (SuccVal nv1))) = NV nv1
ssos (Pred t1) = Pred t1
ssos (IsZero (NV Zero)) = BV Tru
ssos (IsZero (NV (SuccVal nv1))) = BV Fal
ssos (IsZero t1) = IsZero t1
-- additional reflexivity rules
ssos (BV Tru) = BV Tru
ssos (BV Fal) = BV Fal
ssos (NV Zero) = NV Zero
ssos (NV (SuccVal nv1)) = NV (SuccVal nv1)

-- 1.3
eval :: T -> T
eval (IfThenElse t1 t2 t3) = ssos (IfThenElse (eval t1) (eval t2) (eval t3))
eval (Succ t) = ssos (Succ (eval t))
eval (Pred t) = ssos (Pred (eval t))
eval (IsZero t) = ssos (IsZero (eval t))
eval (BV bv) = ssos (BV bv)
eval (NV nv) = ssos (NV nv)



-- test cases;
-- Pred $ Succ $ Succ $ Succ $ Pred $ Pred $ Succ $ Succ $ Succ $ NV Zero 
-- IfThenElse (IsZero (Succ (NV Zero))) (BV Tru) (Succ (NV Zero))
-- IsZero $ BV Tru





