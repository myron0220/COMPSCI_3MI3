module Lib
    (
      ssos
    ) where

import Data.List
import Debug.Trace

data T = App T T
       | If T T T 
       | Succ T
       | Pred T
       | IsZero T
       | Val V
       | Let Label T T
       | Seq T T
       | Alloc T
       | DeRef T
       | Assign T T 
  deriving (Show, Eq)
  
data V = Tru | Fls | Z | SuccNV V | UnitV | Location Loc | Var Label | L Label Type T deriving(Show, Eq)
  
data Label = A | C | D | E | F | G | H | I | J | K 
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type deriving (Show, Eq)

type Gamma = [(Label, Type)] 

type Mu = [(Loc, V)]

freeVars :: T -> [Label]
freeVars (Val (Var x)) = [x]
freeVars (Val (L x _ t1)) = (freeVars t1) \\ [x]
freeVars (App t1 t2) = (freeVars t1) `union` (freeVars t2)
freeVars _ = []

relabel :: T -> Label -> Label -> T
relabel (Val (Var x1)) x2 x3
   | x1 == x2 = Val (Var x3)
   | otherwise = Val (Var x1)
relabel (Val (L x1 typ t)) x2 x3
   | x1 == x2 = Val (L x3 typ (relabel t x2 x3))
   | otherwise = Val (L x1 typ (relabel t x2 x3))
relabel (App t1 t2) x2 x3 = App (relabel t1 x2 x3) (relabel t2 x2 x3)


sub :: T -> Label -> T -> T
sub (Val (Var y)) x s
   | y == x = s
   | otherwise = Val (Var y)
sub (Val (L y typ t1)) x s
   | y /= x && not (elem y (freeVars s)) = Val (L y typ (sub t1 x s))
--   -- W is hard-coded for now
   | y /= x && elem y (freeVars s) = sub (relabel (Val (L y typ t1)) y (head notFreeVariableList)) x s
   where notFreeVariableList = [w | w <- [A , C , D , E , F , G , H , I , J , K 
                                              , M , O , P , Q , R , S , U , W , X , Y], not (elem w (freeVars s))]
sub (App t1 t2) x s = App (sub t1 x s) (sub t2 x s)
sub (If t1 t2 t3) x s = If (sub t1 x s) (sub t2 x s) (sub t3 x s)
sub (Succ t) x s = Succ (sub t x s)
sub (Pred t) x s = Pred (sub t x s)
sub (IsZero t) x s = IsZero (sub t x s)
-- Let Label T T ?
-- otherwise, don't change
sub t _ _ = t

isNF :: T -> Bool
isNF (Val _) = True
isNF _ = False

ssos :: (T, Mu) -> (T, Mu)
-- Boolean
ssos ((If (Val Tru) t _), mu) = (t, mu)               -- E-IfTrue
ssos ((If (Val Fls) _ t), mu) = (t, mu)               -- E-IfFalse
ssos (If t1 t2 t3, mu) = (If t1' t2 t3, mu')          -- E-If
  where (t1', mu') = ssos (t1, mu)
-- Naturals
ssos (Succ (Val nv), mu) = (Val (SuccNV nv), mu)      -- Translate Succ to SuccNV
ssos (Succ t1, mu) = (Succ t1', mu')                  -- E-Succ
  where (t1', mu') = ssos (t1, mu)
ssos (Pred (Val Z), mu) = (Val Z, mu)                 -- E-PredZero
ssos (Pred (Val (SuccNV nv1)), mu) =  (Val nv1, mu)   -- E-PredSucc
ssos (Pred t1, mu) = (Pred t1', mu')                  -- E-Pred
  where (t1', mu') = ssos (t1, mu)
ssos (IsZero (Val Z), mu) = (Val Tru, mu)            -- E-IsZeroZero
ssos (IsZero (Val (SuccNV nv1)), mu) = (Val Fls, mu) -- E-IsZeroSucc
ssos (IsZero t1, mu) = (IsZero t1', mu')             -- E-IsZero
  where (t1', mu') = ssos (t1, mu)
-- Lambda-Calculus
ssos (App (Val (L x typ11 t12)) t2, mu)              -- E-APPABS
  | isNF t2 = ((sub t12 x t2), mu)
ssos (App t1 t2, mu)                                 -- E-APP1
  | not (isNF t1) = (App t1' t2, mu')
  where (t1', mu') = ssos (t1, mu)
ssos (App t1 t2, mu)                                 -- E-APP2
  | isNF t1 = (App t1 t2', mu')
  where (t2', mu') = ssos (t2, mu)
-- Let Bindings
ssos (Let x t1 t2, mu)                               -- E-LetV
  | isNF t1 = (sub t2 x t1, mu)
ssos (Let x t1 t2, mu)                               -- E-Let
  | not (isNF t1) = (Let x t1' t2, mu')
  where (t1', mu') = ssos (t1, mu)
-- The Sequencing Operator
ssos (Seq t1 t2, mu)                                 -- E-Seq
  | not (isNF t1) = (Seq t1' t2, mu')
  where (t1', mu') = ssos (t1, mu)
ssos (Seq (Val UnitV) t2, mu) = (t2, mu)             -- E-SeqNext
-- Reference Operations
ssos (Alloc (Val v1), mu) = (Val (Location l), mu ++ [(l, v1)])     -- E-RefV
  where Val (Location l) = Val (Location (head [e | e <- [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9], not (e `elem` (map fst mu))]))
ssos (Alloc t1, mu)                                                 -- E-Ref
  | not (isNF t1) = (Alloc t1', mu')
  where (t1', mu') = ssos (t1, mu)
ssos (DeRef (Val (Location l)), mu)                                 -- E-DerefLoc
  | not (lst == []) = (Val (snd (head lst)), mu)
  where lst = [(l', v) | (l', v) <- mu, l' == l]
ssos (DeRef t1, mu)                                                 -- E-Deref
  | isNF t1 = (DeRef t1', mu')
  where (t1', mu') = ssos (t1, mu)
ssos (Assign (Val (Location l)) (Val (Location l')), mu)            -- E-Assign
  = (Val UnitV, map (\ x -> if (fst x) == l then (l', (snd x)) else x) mu)
ssos (Assign t1 t2, mu)                                             -- E-Assign1
  | not (isNF t1) = (Assign t1' t2, mu')
  where (t1', mu') = ssos (t1, mu)
ssos (Assign t1 t2, mu)                                             -- E-Assign2
  | (isNF t1) && not (isNF t2) = (Assign t1 t2', mu')
  where (t2', mu') = ssos (t2, mu)





-- test for 90% marking
-- x = Seq (Val UnitV) $ Seq (Val UnitV) $ Seq (Val UnitV) $ (Val Tru)
-- run x


typeCheck :: Gamma -> T -> Maybe Type
-- Boolean
typeCheck gamma (Val Tru) = Just BOOL                 -- T-True
typeCheck gamma (Val Fls) = Just BOOL                 -- T-False
typeCheck gamma (If t1 t2 t3)                         -- T-If
  | (typeCheck gamma t1 == Just BOOL && typeCheck gamma t2 == typeCheck gamma t3) = typeCheck gamma t2
-- Naturals
typeCheck gamma (Val Z) = Just NAT                    -- T-Zero
typeCheck gamma (Succ t1)                             -- T-Succ
  | (typeCheck gamma t1 == Just NAT) = Just NAT
typeCheck gamma (Pred t1)                             -- T-Pred
  | (typeCheck gamma t1 == Just NAT) = Just NAT
typeCheck gamma (IsZero t1)
  | (typeCheck gamma t1 == Just NAT) = Just BOOL      -- T-IsZero
-- Lambda-Calculus
typeCheck gamma (Val (Var x))                         -- T-Var
-- Gamma :: [(Label, Type)]
  | not (filteredGamma == []) = Just typ
  where filteredGamma = [e | e <- gamma, (fst e) == x]
        typ = snd (head filteredGamma)
typeCheck gamma (Val (L x typ1 t2))                   -- T-ABS
  | isJust (typeCheck (gamma ++ [(x, typ1)]) t2) = Just (Arrow typ1 typ2)
  where (Just typ2) = typeCheck (gamma ++ [(x, typ1)]) t2
typeCheck gamma (App t1 t2)                           -- T-APP
  | isArrowType (typeCheck gamma t1)
    && isJust (typeCheck gamma t2)
    && typ11 == typ11'
    = Just typ12
  where (Just (Arrow typ11' typ12)) = (typeCheck gamma t1)
        (Just typ11) = (typeCheck gamma t2)
typeCheck gamma (Val UnitV) = Just Unit                    -- T-Unit
typeCheck gamma (Let x t1 t2)                              -- T-Let
  | isJust (typeCheck gamma t1)
    &&
    isJust (typeCheck (gamma ++ [(x, typ1)]) t2)
    = Just typ2
  where (Just typ1) = (typeCheck gamma t1)
        (Just typ2) = (typeCheck (gamma ++ [(x, typ1)]) t2)
typeCheck gamma (Seq t1 t2)
  | typeCheck gamma t1 == Just Unit
    &&
    isJust (typeCheck gamma t2)
    = Just typ2
  where (Just typ2) = (typeCheck gamma t2)
typeCheck 

-- NOTHING
typeCheck gamma _ = Nothing

isArrowType :: Maybe Type -> Bool
isArrowType (Just (Arrow _ _)) = True
isArrowType _ = False

isJust :: Maybe Type -> Bool
isJust (Just _) = True
isJust _ = False

eval :: T -> T 
eval t
  | not (isNF t) = eval t'
  | otherwise = t
  where (t', []) = ssos (t, [])

run :: T -> T
run t
  | (typeCheck [] t == Nothing) = error "Error! Typechecking Failed!"
  | otherwise = eval(t)


-- exp = App (Val (L X (Arrow NAT BOOL) (App (Val (Var X)) (Val Z)))) (Val (L Y NAT (IsZero (Val (Var Y)))))
-- ssos (exp, [])

-- exp2 = App (Val (L X NAT (Val (Var Y)))) (Val Z)
-- exp3 = App (Val (L X NAT (Val (Var X)))) (Val Z)
--ssos (App (Val (L x typ11 t12)) t2, mu)              -- E-APPABS
--  | isNF t2 = ((sub t12 x t2), mu)
--  x = X
--  typ11 = NAT
--  t12 = Val (Var X)
--  t2 = Val Z
--  sub (Val (Var X)) X (Val Z)

