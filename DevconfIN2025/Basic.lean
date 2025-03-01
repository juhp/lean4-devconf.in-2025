-- # Lean4 primitive types

def num : Nat := 1  -- Natural number (>= 0)

example : Nat := 0

example : Char := 'a'

example : Bool := true || false  -- Boolean

def hello := "world"  -- String

#check hello

#eval hello

#eval (hello, num)  -- a pair or tuple

#eval (hello, (true, num))  -- right associative

-- also `int`, `uint`, `usize`, `uint16`, etc


-- # Natural numbers

-- GADT _(Generalized Algebraic Data Type)_
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat -> MyNat

#check MyNat.succ (MyNat.succ MyNat.zero)

example : MyNat := MyNat.zero.succ.succ
example : MyNat := .succ MyNat.zero.succ.succ

open MyNat in
#check succ (succ zero)

-- # Universes of types

example: Type := Nat

-- There is a hierarchy of Type Universes
-- (to avoid Russell's paradox)
-- - first (lowest) universe is `Prop` (proposition)
--   or `Sort 0`
-- Values of propositions are proofs
-- - see "Propositions as Types"
-- Like types, all proofs also erased from compiled code
-- `Sort 1` is `Type` (short for `Type 0`)

example : Type := Prop
example : Type (n+1) := Type n

-- # Propositions and Equality types

-- Equality types
#check 2 = 2

#check Nat = Nat
#check Eq (1+1) 2 = (1 + 1 = 2)

theorem one_plus_one_is_two : 1 + 1 = 2 := Eq.refl 2

theorem two_is_two : Eq 2 2 := by rfl  -- proof by a Tactic

-- Note propositions (including Eq types) cannot be evaluated


-- # Positive Integers (first example of a dependent type)

def Pos : Type := {x : Nat // x > 0}  -- a Subtype

def pos : Pos := ⟨1, by simp⟩

#eval pos


-- # MyFin

-- index family of (dependent) types
structure MyFin (n : Nat) where
  val  : Nat
  isLt : val < n

-- MyFin 0 is empty (uninhabited)
-- 0 : MyFin 1
-- 0, 1 : MyFin 2
-- 0, 1, 2 : MyFin 3
-- 0, 1, 2, 3 : MyFin 4
-- :... etc

#eval (⟨5,by decide⟩ : MyFin 8)

#eval (⟨1,by simp⟩ : MyFin 2)

-- # Fin

-- Fin is the built-in finite type

#eval (5 : Fin 7)

def size : Nat := 4
def three_of n := Fin.ofNat' (n+1) 2

#eval IO.println s!"This is {three_of size + 1} out of {size}"


-- # Option type

example : Option Char := some 'a'

example : Option a := none  -- polymorphic

#print Option

-- # Lists!

inductive MyList (α : Type)  : Type where
  | nil : MyList α
  | cons (head : α) (tail : MyList α) : MyList α

example : MyList α := .nil
example : MyList Nat := .cons 1 .nil

example : List Bool := .cons true (.cons false .nil)
example : List Bool := [true, false]

-- finally a function!!
def MyList.length : MyList α -> Nat
  | nil => 0
  | cons _ t => 1 + length t

#eval (List.length ([1,2,3] : List Nat))

def ls := [1,2,3]

#eval ls.head?
#eval ([] : List Char).head?
#eval ls.tail
#eval ls[3]?
#eval ls.map (· * 2)  -- fun n => n * 2

#eval [1,2] ++ [3,4]
#eval [1,2].append [3,4,5]

-- # Vectors (sized lists)  (dependent!)

-- Indexed Families
inductive Vect (α : Type) : Nat → Type where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

open Vect

def v2 := cons 2 (cons 1 nil)
def v3 := cons 1 (cons 2 (cons 3 nil))

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

#eval Vect.replicate 2 'a'



def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

#eval Vect.zip v3 v3

-- # Array

def arr := #[1,2,3]

#eval arr.size
#eval arr[2]


-- # Termination
-- functions in Lean are Total: ie must terminate

-- Ackermann function
def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n + 1, 0 => ackermann n 1
  | n + 1, m + 1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)
