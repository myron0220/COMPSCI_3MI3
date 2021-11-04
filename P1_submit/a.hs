ssos :: T -> T
ssos (IfThenElse (Bv Tru) t2 t3) = t2
ssos (IfThenElse (Bv Fal) t2 t3) = t3
ssos (IfThenElse t1 t2 t3) = IfThenElse t1 t2 t3

ssos (Succ t1) = Succ t1
ssos (Pred (Nv Zero)) = Nv Zero
ssos (Pred (Nv SuccVal)) nv1 = Nv nv1
ssos (Pred t1) = Pred t1

ssos (IsZero (Nv Zero)) = Bv Tru
ssos (IsZero (Nv (SuccVal nv1))) = Bv Fal
ssos (IsZero t1) = IsZero t1

-- additional reflexivity rules for Bv and Nv
ssos (Bv Tru) = Bv Tru
ssos (Bv Fal) = Bv Fal
ssos (Nv Zero) = Nv Zero
ssos (Nv (SuccVal nv1)) = Nv (SuccVal nv1)

-- transform a successor to a value-successor
ssos (Succ (Nv nv)) = Nv (SuccVal nv)

-- test cases;
Pred $ Succ $ Succ $ Succ $ Pred $ Pred $ Succ $ Succ $ Succ $ NV Zero 
IfThenElse (IsZero (Succ (NV Zero))) (BV Tru) (Succ (NV Zero))
IsZero $ BV Tru