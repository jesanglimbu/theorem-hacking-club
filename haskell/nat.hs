(?) = undefined

data Exp = Num Integer
         | Add Exp Exp
         | Mul Exp Exp
         | ITE Boolean Exp Exp
         deriving Show

data Boolean = T
             | F
             | AND Boolean Boolean
             | OR Boolean Boolean
             | NEG Boolean

  deriving Show

simplify :: Exp -> Exp
simplify (Num n) = Num n

-- Add
simplify (Add (Num 0) n) = n
simplify (Add n (Num 0)) = n

-- Considering the case that n 'computes to' interp 0
-- Add (Add (Num 0) (Num 0)) m
simplify (Add n m) = aux (simplify n)
  where
    aux (Num 0) = m
    aux _ = Add n m
    
simplify (Add n m) = aux (simplify m)
  where
    aux (Num 0) = n
    aux _ = Add n m

-- Mul
simplify (Mul n m) = Mul n m
-- TODO: simplify this expression
--       considering the cases where either n or m computes to interp 0

simplify (Mul (Num 0) n) = Num 0
simplify (Mul n (Num 0)) = Num 0
simplify (Mul (Num 1) n) = n
simplify (Mul n (Num 1)) = n

-- ITE
simplify (ITE T n m) = n
simplify (ITE F n m) = m
simplify (ITE b n m) = ITE b n m

-- TODO: simplifyB Boolean -> Boolean
--       simplify stuff like Or T a


-- interp turns an expression 'Exp' into an integer
interp :: Exp -> Integer
interp (Num i) = i
interp (Add n m) = interp(n) + interp(m)
interp (Mul n m) = interp(n) * interp(m)
interp (ITE b n m) = if interpB(b) then interp(n) else interp(m)

interpB :: Boolean -> Bool
interpB (T) = True
interpB (F) = False
interpB (AND a b) = interpB(a) && interpB(b)
interpB (OR a b) = interpB(a) || interpB(b)
interpB (NEG a) = not (interpB a)

someExp :: Exp
someExp = (?)

main :: IO ()

main = print (simplify(Mul someExp (Num 0)))


