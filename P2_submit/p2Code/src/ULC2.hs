module ULC2 where

import ULC

-------------- haskell definition ---------------
--fls = L X (L Y (Var Y))
--tru = L X (L Y (Var X))
--not = L B (App (App (Var B) fls) tru)
--and = L B (L C (App (App (Var B) (Var C)) fls))
--or = L B (L C (App (App (Var B) (Var B)) (Var C)))

-- q8(a)
calNot :: T -> T
calNot cb = eval (App not cb)
  where fls = L X (L Y (Var Y))
        tru = L X (L Y (Var X))
        not = L B (App (App (Var B) fls) tru)

-- q8(b)
calAnd :: T -> T -> T
calAnd cb1 cb2 = eval (App (App and cb1) cb2)
  where fls = L X (L Y (Var Y))
        and = L B (L C (App (App (Var B) (Var C)) fls))

-- q8(c)
calOr :: T -> T -> T
calOr cb1 cb2 = eval (App (App or cb1) cb2)
  where or = L B (L C (App (App (Var B) (Var B)) (Var C)))

-------------- formal definition ---------------
-- plus = λm.λn.λs.λz.m s (n s z)
-- mult = λm.λn.λs.m (n s)
-- pair = λf. λs. λb. b f s
-- c0 = λs. λz. z
-- c1 = λs. λz. s z
-- fst = λp. p tru
-- snd = λp. p fls
-- zz = pair c0 c0
-- ss = λp. pair (snd p) (plus c1 (snd p))
-- prd = λm. fst (m ss zz)
-- alternative definition
-- prd = λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)

-------------- haskell definition ---------------
--plus = L M (L N (L S (L Z (App (App (Var M) (Var S)) (App (App (Var N) (Var S)) (Var Z))))))
--mult = L M (L N (L S (App (Var M) (App (Var N) (Var S)))))
--prd = L N (L F (L X (expAll)))
--expAll = (App (App (App exp1 exp2) exp3) exp4) -- (λg.λh.h (g f)) (λu.x) (λu.u)
--exp1 = (Var N)  -- n
--exp2 = (L G (L H (App (Var H) (App (Var G) (Var F))))) -- (λg.λh.h (g f))
--exp3 = (L U (Var X)) -- (λu.x)
--exp4 = (L U (Var U)) -- (λu.u)

---------------------- IMPORTANT -------------------------
-- Call by value cannot fully evaluate numeric functions.
-- To evaluate them fully, we will need a slightly modified version of previous functions
-- they are denoted as isNF', ssos', and eval'.
-- the modifications are:
-- isNF' (\ x . t) = isNF' t
-- ssos' (\ x . t) = if (isNF' t) then (\ x . t) else (\ x . (ssos' t))

isNF' :: T -> Bool
isNF' (Var _) = True
isNF' (L x t) = isNF' t
isNF' (App (L _ _) t2)
  | isNF'(t2) == True = False -- E-APPABS
isNF' (App t1 t2)
  | isNF'(t1) == False = False -- E-APP1
  | isNF'(t1) == True && isNF'(t2) == False = False -- E-APP2
  | otherwise = True -- NO evaluation rules can be applied

ssos' :: T -> T
ssos' (Var x) = (Var x)
ssos' (L x t) = if (isNF' t) then (L x t) else (L x (ssos' t))
ssos' (App (L x t12) t2)
  | isNF'(t2) == True = sub t12 x t2 -- E-APPABS
ssos' (App t1 t2)
  | isNF'(t1) == False = (App (ssos' t1) t2) -- E-APP1
  | isNF'(t1) == True && isNF'(t2) == False = (App t1 (ssos' t2)) -- E-APP2
  | otherwise = error "CANNOT BE EVALUATED ANYMORE" -- NO evaluation rules can be applied

eval' :: T -> T
eval' t
  | isNF' t == False = eval' (ssos' t)
  | otherwise = t

-- q9(a)
calSum :: T -> T -> T
calSum cn1 cn2 = eval' (App (App plus cn1) cn2)
  where plus = L M (L N (L S (L Z (App (App (Var M) (Var S)) (App (App (Var N) (Var S)) (Var Z))))))

-- q9(b)
calTimes :: T -> T -> T
calTimes cn1 cn2 = eval' (App (App mult cn1) cn2)
  where mult = L M (L N (L S (App (Var M) (App (Var N) (Var S)))))

-- q9(c)
calPred :: T -> T
calPred cn = eval' (App prd cn)
  where prd = L N (L F (L X (expAll)))
        expAll = (App (App (App exp1 exp2) exp3) exp4) -- (λg.λh.h (g f)) (λu.x) (λu.u)
        exp1 = (Var N)  -- n
        exp2 = (L G (L H (App (Var H) (App (Var G) (Var F))))) -- (λg.λh.h (g f))
        exp3 = (L U (Var X)) -- (λu.x)
        exp4 = (L U (Var U)) -- (λu.u)


---------------------- Sum test ----------------------
--c0 = L S (L Z (Var Z))
--c1 = L S (L Z (App (Var S) (Var Z)))
--c2 = L S (L Z (App (Var S) (App (Var S) (Var Z))))
--c3 = L S (L Z (App (Var S) (App (Var S) (App (Var S) (Var Z)))))
--c1_ans = calSum c0 c1 -- should return c1
--c2_ans = calSum c0 c2 -- should return c2
--c3_ans = calSum c1 c2 -- should return c3

---------------------- Times test ----------------------
--c0 = L S (L Z (Var Z))
--c1 = L S (L Z (App (Var S) (Var Z)))
--c2 = L S (L Z (App (Var S) (App (Var S) (Var Z))))
--c3 = L S (L Z (App (Var S) (App (Var S) (App (Var S) (Var Z)))))
--c0_ans = calTimes c0 c1 -- should return c0
--c3_ans = calTimes c1 c3 -- should return c3
--c6_ans = calTimes c2 c3 -- should return c6

---------------------- Pred test ----------------------
--c0 = L S (L Z (Var Z))
--c1 = L S (L Z (App (Var S) (Var Z)))
--c2 = L S (L Z (App (Var S) (App (Var S) (Var Z))))
--c3 = L S (L Z (App (Var S) (App (Var S) (App (Var S) (Var Z)))))
--c0_ans = calPred c1 -- should return c0
--c2_ans = calPred c3 -- should return c2
--no_ans = calPred c0 -- should return c0
