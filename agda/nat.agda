open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ ; _+_ ; _*_)
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Equality

data Boolean : Set where
  True  : Boolean
  False : Boolean
  And   : Boolean → Boolean → Boolean
  Or    : Boolean → Boolean → Boolean
  Neg   : Boolean → Boolean

data Exp : Set where
  Num : ℕ → Exp
  Add : Exp → Exp → Exp
  Mul : Exp → Exp → Exp
  Ite : Boolean → Exp → Exp → Exp

interp  : Exp → ℕ
interpB : Boolean → Bool

interp (Num x) = x
interp (Add n m) = interp n + interp m
interp (Mul n m) = interp n * interp m
interp (Ite b n m) = if interpB b then interp n else interp m

interpB True = true
interpB False = false
interpB (And a b) = interpB a ∧ interpB b
interpB (Or a b) = interpB a ∨ interpB b
interpB (Neg b) = not (interpB b)

-- We want to express that (Add n (Num 0)) is 'equivalent' to n
-- which we can write as Add n (Num 0) ∼ n
-- We will define an equivalence between the expressions a and b as:
  -- a and b interpret to the same value (the same nat)

_∼_ : (a b : Exp) → Set
a ∼ b = interp a ≡ interp b

-- cong says that if 'a ≡ b' then 'f a ≡ f b'
-- so, to prove if 'f a ≡ f b' apply 'cong f e', where e is a proof of 'a ≡ b'

0-is-right-identity-of-+ : (n : ℕ) → n + 0 ≡ n
0-is-right-identity-of-+ ℕ.zero = refl
0-is-right-identity-of-+ (ℕ.suc n) = cong ℕ.suc (0-is-right-identity-of-+ n)


example∼ : (n : Exp) → Add n (Num 0) ∼ n
example∼ n = 0-is-right-identity-of-+ (interp n)

~refl : (e : Exp) → e ∼ e
~refl e = refl

-- C-u C-u C-c C-.
-- C-u C-u C-c C-,

∼sym : (a b : Exp) → a ∼ b → b ∼ a
∼sym a b a∼b = sym a∼b

∼trans : (a b c : Exp) → a ∼ b → b ∼ c → a ∼ c
∼trans a b c a∼b b∼c = trans a∼b b∼c

example2∼ : (n m : Exp) → Ite True n m ∼ n
example2∼ n m = refl

example3∼ : (a : Boolean) (n : Exp) → Ite a n n ∼ n
example3∼ a n with interpB a
... | true = refl
... | false = refl

-- simeq
_≃_ : (a b : Boolean) → Set
_≃_ a b = interpB a ≡ interpB b

example4∼ : (a : Boolean) → Or False a ≃ a
example4∼ a = refl

example5∼ : (a : Boolean) → Or True a ≃ True
example5∼ a = refl

-- lemmas for example 6 and 7
∨false : (a : Bool) → a ∨ false ≡ a
∨false false = refl
∨false true = refl

∨true : (a : Bool) → a ∨ true ≡ true
∨true false = refl
∨true true = refl

example6∼ : (a : Boolean) → Or a False ≃ a
example6∼ a = ∨false (interpB a)

example7∼ : (a : Boolean) → Or a True ≃ True
example7∼ a = ∨true (interpB a)

-- example5∼ : 


{--
example5∼ : (a : Exp) → Or a True ∼ True
example5∼ a = ?
--}


{-- 

data Nat : Set where
  Zero : Nat
  Suc  : Nat → Nat

{--
data Prop : Set where
 Atom : Nat → Prop -- takes a nat as the name of the atom
 _∧_  : Prop → Prop → Prop -- takes 2 arguments
 _∨_  : Prop → Prop → Prop
 _⇒_  : Prop → Prop → Prop
 ¬_   : Prop → Prop -- takes 1 argument

-- data List : Set
-- data Tree : Set
-- data Word : Set

a0 : Prop
a0 = Atom Zero

a1 : Prop
a1 = Atom (Suc Zero)

example : Prop
example = a0 ∧ a1
--}

{-- for later
_+_ : Nat → Nat → Nat
Zero + b = b
(Suc a) + b = Suc (a + b)
--}



-- Equal symbol: \==

-- We will use cong: a ≡ b → f a ≡ f b
-- for example: a ≡ b → Suc a ≡ Suc b

-- for all a : ℕ, a + 0 ≡ a
-- by induction: C-c C-c: a
--+0 : (a : Nat) → a + Zero ≡ a
--+0 Zero = refl -- refl is a proof that x ≡ x
--+0 (Suc a) = cong Suc (+0 a)

-- refl  : a ≡ a
-- sym   : a ≡ b → b ≡ a
-- trans : a ≡ b → b ≡ c → a ≡ c
-- cong  : a ≡ b → f a ≡ f b

-- C-c C-l: load
-- C-c C-r: refine a goal
-- C-c C-c: pattern matching on a variable

+Suc : (a : Nat) (b : Nat) → Suc (a + b) ≡ a + Suc b
+Suc Zero b = refl
+Suc (Suc a) b = cong Suc (+Suc a b) -- ← recursive call is using our IH

-- for all a and b : Nat, a + b = b + a
+comm : (a : Nat) (b : Nat) → a + b ≡ b + a
+comm Zero b = sym (+0 b)
+comm (Suc a) b = trans (cong Suc (+comm a b)) (+Suc b a)

--  we're proving: Suc (a + b) ≡ (b + Suc a)
--  using transitivity: Suc (a + b) ≡ T ≡ (b + Suc a)
--  what is T?
--  use +Suc                          ^ Suc (b + a)
--
-- by Ind: Suc (b + a) ≡ (b + Suc a)
-- then use +Suc

variable A : Set -- Read 'Set' as Formula
variable B : Set
variable C : Set
variable D : Set
variable E : Set

{--

example0 : Nat → Nat
example0 n = n

example1 : A → B → A
example1 a b = a

-- \wedge \and
-- ∧
data _∧_ (A B : Set) : Set where
  _,_ : (a : A) (b : B) → A ∧ B -- pairing operator

example∧ : Nat ∧ Bool
example∧ = Zero , True

example∧′ : Nat ∧ Bool
example∧′ = Zero , False

example2 : A → B → A ∧ B
example2 x y = x , y

example3 : A ∧ B → B ∧ A
example3 (a , b) = b , a

example4 : A ∧ (B ∧ C) → (A ∧ B) ∧ C
example4 (a , (b , c)) = (a , b) , c

-- \vee \or
-- ∨
data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

example∨1 : Nat ∨ Bool
example∨1 = left Zero

example∨2 : Nat ∨ Bool
example∨2 = right False

example∨3 : (A ∨ B) → (B ∨ A)
example∨3 (left x) = right x
example∨3 (right x) = left x

-- False: \bot
-- ⊥
data ⊥ : Set where
-- no constructor

⊥-elim : ⊥ → A
⊥-elim ()

-- Negation: \neg
-- ¬
¬ : Set → Set
¬ A = A → ⊥

example⊥1 : (A ∧ ¬ A) → ⊥
example⊥1 (x , f) = f(x)

example5 : (A → B) → (B → C) → (A → C)
example5 f g x = g (f x)

example6 : (A → ¬ B) → (C → B) → C →  ¬ A
example6 f g c a = f a (g c)
-- f : A → B → ⊥
-- g c : B
-- f a : ¬ B

example7a : (A ∧ B) → (A ∨ B)
example7a (a , b) = left a

example7b : (A ∧ B) → (A ∨ B)
example7b (a , b) = right b

-- We're using here an anonymous function: λ a → xxx
-- where the λ is typed using \lambda
example8 : ¬ (A ∨ B) → (¬ A ∧ ¬ B)
example8 x = (λ a → x (left a)) , (λ b → {!!})

-- Similar to above but instead of proving ¬ A
-- using an inlined anonymous function (λ a → xxx),
-- we're proving ¬ A using a sub-definition
-- (called notA below)
-- We had to add the parameters (A B : Set) to the
-- definition, otherwise Agda thought that the A
-- in ¬ (A ∨ B) → xxx was different from the A in ¬ A
example8-v2 : (A B : Set) → ¬ (A ∨ B) → (¬ A ∧ ¬ B)
example8-v2 A B x = notA , notB
  where
  notA : ¬ A
  notA a = {!!}

  notB : ¬ B
  notB b = {!!}

-- Can we prove that?
example9 : (A ∨ B) → (A ∧ B)
example9 = {!!}

example10 :
  (A B C D E : Set) →
  (A → B ∨ C) → (B → D) → (C → B ∨ E) → ¬ (D ∨ E) → ¬ A
example10 A B C D E f g h i a = i (sub1 (f a))
  where
  sub1 : (B ∨ C) → (D ∨ E)
  sub1 (left x) = {!!}
  sub1 (right x) = {!!}

∨E : (A ∨ B)
   → (A → C)
   → (B → C)
   → C
∨E (left a) f g = f(a)
∨E (right b) f g = g(b)

-- on one line
example10-v2 :
  (A → B ∨ C) → (B → D) → (C → B ∨ E) → ¬ (D ∨ E) → ¬ A
example10-v2 f g h i a =
  ∨E (f a)
     (λ b → i (left (g(b))))
     (λ c → ∨E (h c)
               (λ b → i (left (g(b))))
               (λ e → i (right e)))

example11 : (A ∨ B) → (B ∨ A)
example11 (left y) = right y
example11 (right z) = left z

-- can we prove
example12 : A ∨ ¬ A
example12 = {!!}

example13 : (A → B ∨ C) → (B → C) → ¬ (A ∧ C) → ¬ A
example13 f g h a = h (a , ∨E (f a) g (λ c → c))

example14 : (A → C) → ¬ (B ∨ C) → ¬ (A ∨ B)
example14 = {!!}

example15 : (A → B ∨ C) → (B → D) → (C → B ∨ E) → ¬ (D ∨ E) → ¬ A
example15 = {!!}

example16 : ((¬ (¬ (A ∨ B))) → (¬ D ∨ C)) → (¬ D → C) → A → C
example16 = {!!}

example17 : (A ∧ B) → (B ∧ A)
example17 (x , y) = y , x

example18 : (A ∨ B) → (B ∨ A)
example18 (left x) = right x
example18 (right y) = left y

example19 : (A → B) → (B → C) → (A → C)
example19 f g x = g (f x)

example20 : (A → B) → (B → C) → (C → D) → (A → D)
example20 f g h x = h (g (f x))

example21 : (A → B ∨ C) → (B → D) → (C → D) → A → D
example21 f g h x = ∨E (f x) g h

-- define ¬: ¬ A ↔ A → ⊥

-- neg : Bool → Bool
-- neg = ?

-- and : Bool → Bool → Bool
-- and = ?

-- ≡ ?
-- comm : (a b : Nat) → add a b ≡ add b a
--}
--}
