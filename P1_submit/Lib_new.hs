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
       | V BV
       | V NV
  deriving (Eq, Show)

data BV = Tru
        | Fal
  deriving (Eq, Show)
         
data NV = Zero 
        | SuccVal NV  -- Should take care here.
  deriving (Eq, Show)
       

-- 1.2
-- small-steps operational semantics
ssos :: T -> T
ssos (IfThenElse (V Tru) t2 t3) = t2
ssos (IfThenElse (V Fal) t2 t3) = t3