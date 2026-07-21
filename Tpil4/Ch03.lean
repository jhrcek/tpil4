-- 3.1. Propositions as Types
def Implies (p q : Prop) : Prop := p → q

#check And
#check Or
#check Not
#check Implies

variable (p q r : Prop)

#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)


structure Proof (p : Prop) : Type where
  proof : p

#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q


axiom modus_ponens (p q : Prop) :
  Proof (Implies p q)
  → Proof p
  → Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

-- 3.2. Working with Propositions as Types
set_option linter.unusedVariables false

variable {p : Prop}
variable {q : Prop}

-- `theorem` is like `def` but involving `Prop`s (?)
theorem t1 : p → q → p :=
  fun hp : p => fun hq : q => hp

#print t1

-- using `show` statement to explicitly specify the type of the final term
theorem t2 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

#print t2

-- We can move the lambda-abstracted variables to the left
theorem t3 (hp : p) (hq : q) : p := hp

#print t3

-- Using the theorem as a function
axiom hp : p

theorem t4 : q → p := t3 hp

-- axiom postulates the existence of an element and may compromise ligical consistency

axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

-- We can move all of the params to the right of := as well
theorem t5 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp


-- automatic generalization of variables
variable {p q : Prop}

theorem t6 : p → q → p := fun (hp : p) (hq : q) => hp


theorem t7 (p q : Prop) (hp : p) (hq : q) : p := hp
variable (p q r s : Prop)

#check t7 p q
#check t7 r s
#check t7 (r → s) (s → r)

variable (h : r → s)
#check t7 (r → s) (s → r) h

variable (p q r s : Prop)

theorem t8 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

theorem t9 (h₁ : q → r) (h₂ : p → q) (h₃ : p) : r :=
  show r from h₁ (h₂ h₃)

-- 3.3. Propositional Logic
variable (p q : Prop)

#check p → q → p ∧ q

#check ¬p → p ↔ False

#check p ∨ q → q ∨ p

-- 3.3.1 Conjunction

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq


variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h


variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)

#check List.length xs

-- syntactic shorthand if xs has type List
#check xs.length

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  -- flattening nested constructors that associate to the right
  ⟨h.right, h.left, h.right⟩

-- 3.3.2. Disjunction
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (hp : p) : p ∨ q := Or.inl hp
example (hq : q) : p ∨ q := Or.inr hq

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example (h : p ∨ q) : q ∨ p :=
  h.elim Or.inr Or.inl

-- 3.3.3. Negation and Falsity
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

variable (p q : Prop)

theorem and_swap₂ : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap₂ p q).mp h

-- 3.4. Introducing Auxiliary Subgoals
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from h.right

-- 3.5. Classical Logic
open Classical

variable (p : Prop)

#check em p

-- Double Negation Elimination
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- As an exercise, you might try proving the converse,
-- that is, showing that em can be proved from dne.
theorem em₁ {p : Prop} (hdne : ∀ {q : Prop}, ¬¬q → q) : p ∨ ¬p :=
  hdne (fun h : ¬(p ∨ ¬p) => -- ¬(p ∨ ¬p) is like `(p ∨ ¬p) → False`
    have hnp : ¬p := fun hp : p => h (Or.inl hp)
    h (Or.inr hnp))

-- the same with each step named, so each type is visible:
theorem em₂ {p : Prop} (hdne : ∀ {q : Prop}, ¬¬q → q) : p ∨ ¬p :=
  have dn : ¬¬(p ∨ ¬p) :=
    fun h : ¬(p ∨ ¬p) =>
      have hnp : ¬p := fun hp : p => h (Or.inl hp)
      show False from h (Or.inr hnp)
  show p ∨ ¬p from hdne dn

-- tactic mode: commands that transform the goal step by step
theorem em₃ {p : Prop} (hdne : ∀ {q : Prop}, ¬¬q → q) : p ∨ ¬p := by
  apply hdne          -- goal becomes ¬¬(p ∨ ¬p)
  intro h             -- h : ¬(p ∨ ¬p), goal becomes False
  apply h             -- goal becomes p ∨ ¬p
  exact Or.inr (fun hp => h (Or.inl hp))

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

-- For people not used to constructive thinking it might not be ovious
-- when classical reasoni0ng is used.
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p => Or.inr
      (show ¬q from
        fun hq : q => h (And.intro hp hq)))
    (fun hnp : ¬p => Or.inl hnp)

-- 3.6. Examples of Propositional Validities

-- Commutativity
-- 1
#check and_comm
-- 2
#check or_comm

-- associativity
-- 3
#check and_assoc
-- 4
#check or_assoc

-- distributivity
-- 5
#check and_or_left
-- 6
#check or_and_left
--
#check and_or_right
--
#check or_and_right

-- other properties
-- 7
#check and_imp
#check and_imp.symm

-- 8
#check or_imp

-- 9
#check not_or

-- 10
#check not_and_of_not_or_not

--11
#check and_not_self

-- 12
#check not_imp_of_and_not

-- 13
#check absurd
#check Not.elim

-- 14
#check Or.neg_resolve_left

-- 15
-- ?p ∨ False ↔ ?p
-- stated with = instead of ↔ (propext); bridge with iff_of_eq if needed
#check or_false
#check false_or

--16
-- ?p ∧ False ↔ False
#check and_false
#check false_and

-- 17
#check iff_not_self

-- 18. mt = modus tollens
#check mt

-- 19
-- (?p → ?r ∨ ?s) → ((?p → ?r) ∨ (?p → ?s))
-- not in core stdlib; Mathlib has imp_or

-- 20
#check Classical.not_and_iff_not_or_not

-- 21
#check not_imp

-- 22
#check Decidable.not_or_of_imp


-- 23
-- (¬?q → ¬?p) → (?p → ?q)
-- not in core stdlib; Mathlib has not_imp_not

-- 24
-- ?p ∨ ¬?p
#check em
#check Classical.em

-- 25
-- (((?p → ?q) → ?p) → ?p)
-- not in core stdlib; Mathlib has peirce
-- peirce' is a constructive variant (∀ b in the hypothesis makes it weaker)
#check peirce'


open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim h.right
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → p → q :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)

-- 3.7 Exercises

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun hpq : p ∧ q => ⟨ hpq.right, hpq.left ⟩)
    (fun hqp : q ∧ p => ⟨ hqp.right, hqp.left ⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ hpq : p ∨ q => Or.elim hpq
      (λ hp : p => Or.inr hp)
      (λ hq : q => Or.inl hq))
    (λ hqp : q ∨ p => Or.elim hqp
      (λ hq : q => Or.inr hq)
      (λ hp : p => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ pqr : (p ∧ q) ∧ r => ⟨pqr.left.left, ⟨pqr.left.right, pqr.right⟩⟩)
    (λ pqr : p ∧ (q ∧ r) => ⟨⟨pqr.left, pqr.right.left⟩, pqr.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ pqr : (p ∨ q) ∨ r =>
      Or.elim pqr
        (λ hpq : p ∨ q =>
          Or.elim hpq
            (λ hp : p => Or.inl hp)
            (λ hq : q => Or.inr (Or.inl hq)))
        (λ hr : r => Or.inr (Or.inr hr)))
    (λ pqr : p ∨ (q ∨ r) =>
      Or.elim pqr
        (λ hp : p => Or.inl (Or.inl hp))
        (λ hqr : q ∨ r =>
          Or.elim hqr
            (λ hq : q => Or.inl (Or.inr hq))
            (λ hr : r => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (λ hpqr : p ∨ (q ∧ r) =>
      Or.elim hpqr
        (λ hp : p => And.intro (Or.inl hp) (Or.inl hp))
        (λ hqr : q ∧ r => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (λ hpqpr : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim hpqpr.left
        (λ hp : p => Or.inl hp)
        (λ hq : q =>
          Or.elim hpqpr.right
            (λ hp : p => Or.inl hp)
            (λ hr : r => Or.inr ⟨hq, hr⟩)))

-- Exportation (a.k.a. Currying, via the Curry–Howard correspondence)
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ (hpqr : p → q → r) (hpq : p ∧ q) => hpqr hpq.left hpq.right)
    (λ (hpqr : p ∧ q → r) (hp : p) (hq : q) => hpqr ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    Iff.intro
      (λ hpqr : (p ∨ q) → r => ⟨λ hp : p => hpqr (Or.inl hp), λ hq : q => hpqr (Or.inr hq)⟩)
      (λ ⟨ pr, qr ⟩ (hpq : p ∨ q) =>
        Or.elim hpq
          (λ hp : p => pr hp )
          (λ hq : q => qr hq))

-- De Morgan's Law: ¬(p ∨ q) ↔ ¬p ∧ ¬q
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ hnpq : ¬(p ∨ q) =>
      ⟨ λ hp : p => hnpq (Or.inl hp)
      , λ hq : q => hnpq (Or.inr hq)
      ⟩)
    (λ hnpnq : ¬p ∧ ¬q => λ (hpq : p ∨ q) =>
      Or.elim hpq
        (λ hp : p => hnpnq.left hp)
        (λ hq : q => hnpnq.right hq))

-- De Morgan's Law (constructive half): ¬p ∨ ¬q → ¬(p ∧ q)
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ hpq : ¬p ∨ ¬q =>
    λ hpaq : p ∧ q => Or.elim hpq
      (λ hnp : ¬p => hnp hpaq.left)
      (λ hnq : ¬q => hnq hpaq.right)

-- Law of Non-Contradiction
example : ¬(p ∧ ¬p) :=
  λ panp : p ∧ ¬p => absurd panp.left panp.right

example : p ∧ ¬q → ¬(p → q) :=
  λ panq : p ∧ ¬q => λ pimpq : p → q => absurd (pimpq panq.left) panq.right

-- Paradox of Material Implication (a false premise implies anything)
example : ¬p → (p → q) :=
  λ (hnp : ¬p) (hp : p) => absurd hp hnp

-- Material Conditional (relates to the Resolution rule in logic)
example : (¬p ∨ q) → (p → q) :=
    λ npq : ¬p ∨ q => λ hp : p =>
      Or.elim npq
        (λ hnp : ¬p => absurd hp hnp)
        (λ hq : q => hq)

-- Identity Law (∨ with False)
example : p ∨ False ↔ p :=
    Iff.intro
      (λ hpf : p ∨ False =>
        Or.elim hpf
          (λ hp : p => hp)
          (λ hf : False => False.elim hf))
      (λ hp : p => Or.inl hp)


-- Domination Law (∧ with False)
example : p ∧ False ↔ False :=
  Iff.intro
    (λ hpaf => hpaf.right)
    (λ hf => False.elim hf)

-- Modus Tollens
example : (p → q) → (¬q → ¬p) :=
   λ hpimpq nq hp => absurd (hpimpq hp) nq

-- Exercises requiring classical reasoning:

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ piqr : p → q ∨ r =>
    Or.elim (em p)
     (λ hp : p =>
       Or.elim (piqr hp)
         (λ hq => Or.inl (λ _ => hq))
         (λ hr => Or.inr (λ _ => hr)))
     (λ hnp : ¬p =>  Or.inl (λ hp => absurd hp hnp))

-- De Morgan's Law (classical half, needs excluded middle): ¬(p ∧ q) → ¬p ∨ ¬q
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h => Or.elim (em p)
    (λ hp : p => Or.elim (em q)
      (λ hq : q => absurd ⟨ hp, hq ⟩ h)
      (λ hnq : ¬q => Or.inr hnq))
    (λ hnp : ¬p => Or.inl hnp)

-- Negation of the Conditional (completes ¬(p → q) ↔ p ∧ ¬q; needs excluded middle)
example : ¬(p → q) → p ∧ ¬q :=
  λ npimpq : ¬(p → q) => Or.elim (em p)
    (λ hp : p =>
      have nq : ¬q := λ hq : q => npimpq (λ _ => hq)
      And.intro hp nq)
    (λ hnp : ¬p =>
        False.elim (npimpq (λ hp : p => absurd hp hnp)))

-- Material Conditional (other direction, needs excluded middle)
example : (p → q) → (¬p ∨ q) :=
  λ hpiq : p → q => Or.elim (em p)
    (λ hp : p => Or.inr (hpiq hp))
    (λ hnp : ¬p => Or.inl hnp)

-- Contraposition / Law of Transposition (converse direction, needs excluded middle)
example : (¬q → ¬p) → (p → q) :=
  λ hnqnp hp => Or.elim (em q)
    (λ hq : q => hq)
    (λ hnq : ¬q => absurd hp (hnqnp hnq))

-- Law of Excluded Middle (LEM)
example : p ∨ ¬p := em p

-- Pierce's Law
example : ((p → q) → p) → p :=
  λ pqp : (p → q) → p =>
    Or.elim (em p)
      (λ hp : p => hp)
      (λ hnp : ¬p => pqp (λ hp : p => absurd hp hnp ))
