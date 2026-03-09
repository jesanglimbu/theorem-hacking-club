(?) = undefined


-- Goal:
-- x + 10 where x is a variable
-- defined by:
-- Let x := 5
-- Let x:= 5 in (x + (Let x := 4 in x))
data Exp = Num Integer
         | Add Exp Exp
         | Mul Exp Exp
         | Ite Boolean Exp Exp
         | Var String
         | Let String Exp Exp -- "Let s n m" where s := n in the expression m
         deriving Show

-- x + 10
example1 :: Exp
example1 = Add (Var "x") (Num 10)

-- Let x:= 5 in x + 10
example2 :: Exp
example2 = Let ("x") (Num 5) (example1)

-- Let x := 5 in (x + (Let x := 4 in x))
example3 :: Exp
example3 = Let "x" (Num 5) (Add (Var "x") (Let "x" (Num 4) (Var "x")))

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
  -- 1. Stateful computation
  -- 2. Lambda-calculus
pred:: Integer -> Integer
pred 0 = 0
pred n = n - 1

add :: Integer -> Integer -> Integer
add 0 m = m -- base case
add n m = succ (add (n - 1) m ) -- recursive call

type State = [(String , Integer)]

initialState :: State
initialState = []

-- 'insert v n s' adds up (v,n) to the front of the list
insert :: String -> Integer -> State -> State
insert v n s = (v,n) : s

defaultValue :: Integer
defaultValue = 0

-- for now we will simply return a defualt value
-- if the variable is not in the state
lup :: String -> State -> Integer
lup v [] = defaultValue -- case where state is empty
lup v ((w,n):s) = if v==w then n else lup v s -- case where state has one element

-- interp turns an expression 'Exp' into an integer
interp :: State -> Exp -> Integer
interp state (Num i) = i
interp state (Add n m) = interp state n + interp state m
interp state (Mul n m) = interp state n * interp state m
interp state (Ite b n m) = if interpB b then interp state n else interp state n
interp state (Var x) = lup x state -- looking up the variable x in the given state
interp state (Let x n m) =
  let valueOfX = interp state n
  in interp (insert x valueOfX state) m
  
  

interpB :: Boolean -> Bool
interpB (T) = True
interpB (F) = False
interpB (And a b) = interpB(a) && interpB(b)
interpB (Or a b) = interpB(a) || interpB(b)
interpB (Neg a) = not (interpB a)

main :: IO ()

main = print (interp initialState example3)


