module ULC where

import Data.List


-- q1
data T = Var Alphabet
       | L Alphabet T
       | App T T
  deriving (Eq, Show)

data Alphabet = A | B | C | D | E | F | G | H | I | J | K | M | N | O | P | Q | R | S | U | V | W | X | Y | Z
  deriving (Eq, Show)

-- q2
fv :: T -> [Alphabet]
fv (Var x) = [x]
fv (L x t1) = (fv t1) \\ [x]
fv (App t1 t2) = (fv t1) `union` (fv t2)

-- q3
relabelling :: T -> Alphabet -> Alphabet -> T
relabelling (Var x1) x2 x3
   | x1 == x2 = Var x3
   | otherwise = Var x1
relabelling (L x1 t) x2 x3
   | x1 == x2 = L x3 (relabelling t x2 x3)
   | otherwise = L x1 (relabelling t x2 x3)
relabelling (App t1 t2) x2 x3 = App (relabelling t1 x2 x3) (relabelling t2 x2 x3)

-- q4
sub :: T -> Alphabet -> T -> T
sub (Var y) x s
   | y == x = s
   | otherwise = Var y
sub (L y t1) x s
   | y /= x && not (elem y (fv s)) = L y (sub t1 x s)
--   -- W is hard-coded for now
--   | y /= x && elem y (fv s) = sub (relabelling (L y t1) y W) x s
   | y /= x && elem y (fv s) = sub (relabelling (L y t1) y (head notFreeVariableList)) x s
   where notFreeVariableList = [w | w <- [A, B, C, D, E, F, G, H, I, J, K, M, N, O, P, Q, R, S, U, V, W, X, Y, Z], not (elem w (fv s))]
sub (App t1 t2) x s = App (sub t1 x s) (sub t2 x s)
-- otherwise, don't change
-- assume when there is NO sub rule can be applied, just return the original expression.
sub t _ _ = t


-- q5
-- data T = Var Alphabet
--        | L Alphabet T
--        | App T T
-- key point: v <=> isNF(t) == true
--            t1 -> t1' <=> isNF(t1) == false
isNF :: T -> Bool
isNF (Var _) = True
isNF (L _ _) = True
isNF (App (L _ _) t2)
  | isNF(t2) == True = False -- E-APPABS
isNF (App t1 t2)
  | isNF(t1) == False = False -- E-APP1
  | isNF(t1) == True && isNF(t2) == False = False -- E-APP2
  | otherwise = True -- NO evaluation rules can be applied

-- q6
ssos :: T -> T
ssos (Var x) = (Var x)
ssos (L x t) = (L x t)
ssos (App (L x t12) t2)
  | isNF(t2) == True = sub t12 x t2 -- E-APPABS
ssos (App t1 t2)
  | isNF(t1) == False = (App (ssos t1) t2) -- E-APP1
  | isNF(t1) == True && isNF(t2) == False = (App t1 (ssos t2)) -- E-APP2
  | otherwise = error "CANNOT BE EVALUATED ANYMORE" -- NO evaluation rules can be applied

-- q7
eval :: T -> T
eval t
  | isNF t == False = eval (ssos t)
  | otherwise = t


---------------------------------------- test cases -----------------------------------------------

--exp = (App (L X (Var X)) (App (L Y (Var Y)) (Var M)))
--isNF exp -- should return: False
--ssos exp -- should return: App (L X (Var X)) (Var M)
--ssos (ssos exp) -- should return: Var M



