/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
-- "&&" is the Boolean and
#check b1 && b2
-- Boolean or
#check b1 || b2
-- Boolean "true"
#check true

/- Evaluate -/
#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat
#check Nat -> Nat
#check Nat × Nat
#check Prod Nat Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2
#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2

-- Types themselves are objects with "type"
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

-- declare constants for types
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G
#check G α
#check G α β
#check G α Nat

#check Prod α β
#check α × β
#check Prod Nat Nat
#check Nat × Nat


#check List α
#check List Nat

#check Type

#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Type
#check Type 0

#check List
#check Prod (Type 2) (Type 4)
