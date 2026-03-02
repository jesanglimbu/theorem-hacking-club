(?) = undefined

data Exp = Num Integer
         | Add Exp Exp
         | Mul Exp Exp
         | Ite Boolean Exp Exp
         deriving Show

data Boolean = T
             | F
             | And Boolean Boolean
             | Or Boolean Boolean
             | Neg Boolean
             deriving Show

-- Simplify functions
simplify :: Exp -> Exp
simplifyB :: Boolean -> Boolean

-- Base case for simplify
simplify (Num n) = Num n


-- Simplifying addition
simplify (Add (Num 0) n) = n
simplify (Add n (Num 0)) = n

-- 1a. Add (Num 0) m -> m
-- 1b. Add (Add (Num 0) (Num 0)) m -> m
-- etc.
-- 2a. Add n (Num 0) -> n
-- 2b. Add n (Add (Num 0) (Num 0)) -> n
-- etc.
simplify (Add n m) = aux (simplify n) (simplify m)
  where
    aux (Num 0) m' = m'
    aux n'(Num 0) = n'
    aux n' m' = Add n' m'

-- 1. Mul n 0 = n
-- 2. Mul 0 m = m
simplify (Mul n m) = aux (simplify n) (simplify m)
  where
    aux (Num 0) m' = Num 0
    aux n' (Num 0) = Num 0
    aux (Num 1) m' = m'
    aux n' (Num 1) = n'

-- TODO: simplify this expression
--       considering the cases where either n or m computes to interp 0
simplify (Mul (Num 0) n) = Num 0
simplify (Mul n (Num 0)) = Num 0
simplify (Mul (Num 1) n) = n
simplify (Mul n (Num 1)) = n

-- ITE
simplify (Ite b n m) = Ite (simplifyB b) (simplify n) (simplify m)

-- TODO: simplifyB Boolean -> Boolean
--       simplify stuff like Or T a
simplifyB T = T
simplifyB F = F


simplifyB (Or a b) = aux (simplifyB a) (simplifyB b)
  where
    aux T b' = T
    aux a' T = T
    aux F F = F
    aux a' b' = Or a' b'
      
simplifyB (And a b) = aux (simplifyB a) (simplifyB b)
  where
    aux T b' = b'
    aux a' T = a'
    aux F F = F

simplifyB (Neg a) = aux (simplifyB a)
  where
    aux T = F
    aux F = T

-- Assume we have a negation.
-- Could we simplify (Neg a a) to Num 0?
-- Where to go next?
  -- 1. Lambda-calculus
  -- 2. Stateful computation
pred:: Integer -> Integer
pred 0 = 0
pred n = n - 1

add :: Integer -> Integer -> Integer
add 0 m = m -- base case
add n m = succ (add (n - 1) m ) -- recursive call

-- interp turns an expression 'Exp' into an integer
interp :: Exp -> Integer
interp (Num i) = i
interp (Add n m) = interp(n) + interp(m)
interp (Mul n m) = interp(n) * interp(m)
interp (Ite b n m) = if interpB(b) then interp(n) else interp(m)

interpB :: Boolean -> Bool
interpB (T) = True
interpB (F) = False
interpB (And a b) = interpB(a) && interpB(b)
interpB (Or a b) = interpB(a) || interpB(b)
interpB (Neg a) = not (interpB a)

main :: IO ()

main = print (interp (simplify (Ite (Neg T) (Add (Mul (Num 4) (Num 0)) (Num 10)) (Num 14))))


