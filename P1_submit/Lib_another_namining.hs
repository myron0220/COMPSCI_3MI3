module Lib
    ( someFunc
    ) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- 1.1
data T = IfThenElse T T T
       | Succ T
       | Pred T
       | IsZero T
       | V Bv
       | V Nv
  deriving (Eq, Show)

data Bv = Tru
        | Fal
  deriving (Eq, Show)
         
data Nv = Zero 
        | SuccVal Nv  -- Should take care here.
  deriving (Eq, Show)
       

-- 1.2
-- small-steps operational semantics
ssos :: T -> T
ssos (IfThenElse Tru t2 t3) = t2
ssos (IfThenElse Fal t2 t3) = t3
ssos (IfThenElse t1 t2 t3) = (IfThenElse t1 t2 t3)
ssos Succ t1 = Succ t1
ssos Pred V Zero = V Zero
ssos Pred V SuccVal nv1 = V nv1
ssos Pred t1 = Pred t1
ssos IsZero V Zero = V Tru
ssos IsZero V SuccVal nv1 = V Fal
ssos IsZero t1 = IsZero t1
-- additional reflexivity rules for Bv and Nv
ssos V Tru = V Tru
ssos V Fal = V Fal
ssos V Zero = V Zero
ssos V SuccVal nv1 = V SuccVal nv1
-- transform a successor to a value-successor
ssos Succ V nv = V SuccVal nv













