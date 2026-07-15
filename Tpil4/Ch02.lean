-- 2.1 Simple Type Theory
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

-- 2.2. Types as objects
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

-- polymorphic over type universes
#check List
#check Prod (Type 2) (Type 4)
#check Prod

section
-- definie polymorphic universe constants
universe u
def F₁ (α : Type u) : Type u := Prod α α
#check F₁
end

-- the same without explicit universe declaration
def F₂.{u} (α : Type u) : Type u := Prod α α
#check F₂

-- 2.3. Function Abstraction and Evaluation
#check fun (x : Nat) => x + 5

-- λ and fun mean the same thing
#check λ (x : Nat) => x + 5

-- Nat can be inferred without explicit type declaration
#check fun x => x + 5
#check λ x => x + 5

#eval (λ x : Nat => x + 5) 10


#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x
#check fun _x : Nat => true
#check fun x : Nat => g (f x)
#check fun x => g (f x)

#eval (fun x : Nat => g (f x)) 18544

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)


#check (fun x : Nat => x) 1
#check (fun _x : Nat => true) 1
#check (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0

#eval (fun x : Nat => x) 1
#eval (fun _x : Nat => true) 1

-- 2.4 Definitions
def double (x : Nat) : Nat :=
  x + x

#eval double 4

def double₁ : Nat → Nat :=
  fun x => x + x

#eval double₁ 3

def double₂ :=
  fun (x : Nat) => x + x

#eval double₂ 3

def pi := 3.141592654

def add (x y : Nat) :=
  x + y

#eval add 3 2



def add₂ (x : Nat) (y : Nat) :=
  x + y

#eval add₂ (double 3) (7 + 9)

def greater (x y : Nat) :=
  if x > y then x
  else y

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3

-- 2.5 Local Definitions

#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2
/- -- does not type check
  def bar := (fun a => fun x : a => x + 2) Nat
-/

-- 2.6. Variables and Sections
namespace TwoSix

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

-- variable command to make the above more compact
variable (α β γ : Type)

def compose₁ (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice₁ (h : α → α) (x : α) : α :=
  h (h x)

def doThrice₁ (h : α → α) (x : α) : α :=
  h (h (h x))

-- variables can be of any type
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose₂ := g (f x)
def doTwice₂ := h (h x)
def doThrice₂ := h (h (h x))

#print compose
#print doTwice
#print doThrice

-- Limiting variable scope using section
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose₃ := g (f x)
  def doTwice₃ := h (h x)
  def doThrice₃ := h (h (h x))

end useful

end TwoSix

-- 2.7. Namespaces

namespace Foo
  def a : Nat := 5
  def f₁ (x : Nat) : Nat := x + 7

  def fa : Nat := f₁ a
  def ffa : Nat := f₁ (f₁ a)
namespace Nested

def xx := 1
#check xx
#check Nested.xx
#check Foo.Nested.xx

end Nested

#check a
#check f
#check fa
#check ffa
#check Foo.fa
end Foo

--check a  -- error
-- check f₁ -- error

#check Foo.a
#check Foo.f₁
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f₁
#check fa
#check Foo.fa

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

-- nested namespaces

namespace Foo1
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

#check fa
#check ffa
end Bar

#check fa
#check Bar.ffa
end Foo1

#check Foo1.fa
#check Foo1.Bar.ffa
open Foo1

#check fa
#check Bar.ffa

-- reopening closed namespace
namespace Foo2
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo2

#check Foo2.a
#check Foo2.f

namespace Foo2
  def ffa : Nat := f (f a)
end Foo2

#check Foo2.ffa

-- 2.8. What makes dependent type theory dependent?

namespace Dep

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat
#check cons Bool
#check cons

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append


universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5

end Dep

-- 2.9. Implicit Arguments
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs

#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append

#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs

-- type arguments can be inferred
#check Lst.cons _ 0 (Lst.nil _)

def as₁ : Lst Nat := Lst.nil _
def bs₁ : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as₁ bs₁

namespace ImplicitArgs
universe v
def Lst (α : Type v) : Type v := List α

def Lst.cons {α : Type v} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type v} : Lst α := List.nil
def Lst.append {α : Type v} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs

def ident {α : Type u} (x : α) := x


#check (ident)
#check ident
#check @ident
#check ident 1
#check ident "hello"

#check (List.nil)
#check (id)
#check (List.nil : List Nat)
#check (id : Nat → Nat)

#check 2
#check (2 : Nat)
#check (2 : Int)
end ImplicitArgs

#check id
#check @id
#check @id Nat
#check @id Bool
#check @id Nat 1
#check @id Bool true
