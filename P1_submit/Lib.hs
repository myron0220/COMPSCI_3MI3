module Lib
    ( someFunc,
      ssos
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
       | Wrong
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
-- 2 begin
ssos (Wrong) = Wrong
ssos (IfThenElse Wrong t2 t3) = Wrong
ssos (IfThenElse t1 Wrong t3) = Wrong
ssos (IfThenElse t1 t2 Wrong) = Wrong
ssos (Succ Wrong) = Wrong
ssos (Pred Wrong) = Wrong
ssos (IsZero Wrong) = Wrong
ssos (IfThenElse (NV _) t2 t3) = Wrong
ssos (Succ (BV _)) = Wrong
ssos (Pred (BV _)) = Wrong
ssos (IsZero (BV _)) = Wrong
-- 2 end
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

-- 3
bsos :: T -> T
-- Deal with Wrong begin
bsos (Wrong) = Wrong
bsos (IfThenElse Wrong t2 t3) = Wrong
bsos (IfThenElse t1 Wrong t3) = Wrong
bsos (IfThenElse t1 t2 Wrong) = Wrong
bsos (Succ Wrong) = Wrong
bsos (Pred Wrong) = Wrong
bsos (IsZero Wrong) = Wrong
bsos (IfThenElse (NV _) t2 t3) = Wrong
bsos (Succ (BV _)) = Wrong
bsos (Pred (BV _)) = Wrong
bsos (IsZero (BV _)) = Wrong
-- Deal with Wrong end
bsos (BV bv) = BV bv
bsos (NV nv) = NV nv
bsos (IfThenElse (BV Tru) (BV bv) t3) = BV bv
bsos (IfThenElse (BV Tru) (NV nv) t3) = NV nv
bsos (IfThenElse (BV Fal) t2 (BV bv)) = BV bv
bsos (IfThenElse (BV Fal) t2 (NV nv)) = NV nv
bsos (IfThenElse t1 t2 t3) = bsos (IfThenElse (bsos t1) (bsos t2) (bsos t3))
bsos (Succ (NV nv)) = NV (SuccVal nv)
bsos (Succ t1) = bsos (Succ (bsos t1))
bsos (Pred (NV Zero)) = NV Zero
bsos (Pred (NV (SuccVal nv))) = NV nv
bsos (Pred t1) = bsos (Pred (bsos t1))
bsos (IsZero (NV Zero)) = BV Tru
bsos (IsZero (NV (SuccVal nv))) = BV Fal
bsos (IsZero t1) = bsos (IsZero (bsos t1))

-- test cases;
-- Pred $ Succ $ Succ $ Succ $ Pred $ Pred $ Succ $ Succ $ Succ $ NV Zero 
-- IfThenElse (IsZero (Succ (NV Zero))) (BV Tru) (Succ (NV Zero))
-- IsZero $ BV Tru





