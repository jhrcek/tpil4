-- 5. Tactics
-- 5.1. Entering Tactic Mode

-- term style
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  ⟨hp, hq, hp⟩

-- tactic style
theorem test₁  (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

-- Looking at the resulting proof term
#print test₁
-- theorem test₁ : ∀ (p q : Prop), p → q → p ∧ q ∧ p :=
--   fun p q hp hq => ⟨hp, ⟨hq, hp⟩⟩

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

-- alternative one line syntax + semicolon
theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

-- Using `case <tag>` to structure
theorem test₄ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro -- apply introduces `left` and `right` subgoal based on And.intro's parameter names
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

-- Using case tags to swap the order of goals
theorem test₅  (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

-- "bullet" notation for structuring the proof
theorem test₆ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

-- 5.2. Basic Tactics

-- 1) intro
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    · intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x


-- intro several vars at once
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁


example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩ -- intro allows using implicit `match`
  exact ⟨w, hqw, hpw⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro -- intro allows using implicit `match` with multiple alternatives
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

-- `assumption`
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃

-- `assumption` will unify metavariables in the conclusion if necessary
example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃

-- `intros` command to introduce the three variables and two hypotheses automatically
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- The introduced variables introduced by `intros` above are hygienic
-- (inaccessible by default).
--  But name hygiene can be disabled using `unhygienic`
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros -- thanks to `unhygienic` introduces regular names,
         -- but makes the code brittle (to the changes of naming strategy)
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

-- Alternatively use rename_i to rename the most recent inaccssible names in the context
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  -- introduce hygienic variables for a b c d and the 3 assumptions
  rename_i h1 _ h2 -- rename the last and 3rd to last of the above ^
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

-- `rfl`
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl

-- `repeat` - apply tactic several times
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- `revert` is "inverse" of intro
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

-- moving a hypothesis into the goal yields an implication
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

--
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

-- `generalize` = replace arbitrary expression in the goal by a fresh variable
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- not every generalization preserves the validity of the goal, e.g.
example : 2 + 3 = 5 := by
  generalize 3 = x
  sorry

-- can optionally provide a label for the generalication equation (here "h :")
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- 5.3. More Tactics

-- `cases` can be used to decompose a disjunction
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

-- alternative `cases` syntax without `with`
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

-- `cases` useful when multiple goals can be solved by the same tactic
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

-- Using `<;>` combinator to achieve the same as above
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

-- combining `cases` with ·
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

-- combining `cases` with `case`
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

-- mixing both · and `case`
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
-- using `cases` to decompose a conjunction
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; exact hp; apply Or.inl hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; exact hp; apply Or.inr hr

-- `constructor` applies the first applicable constructor of
-- inductive type or fails. Here, using it with existential quantifier:
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with -- leaves the x implicit, inferred later by `exact px`
  | intro x px => constructor; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with -- using `exists x` to provide witness first
  | intro x px => exists x; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x

-- Using the above tactics to define normal function on data
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

-- using cases to do case dictionction on Nat
open Nat
example (P : Nat → Prop)
    (h₀ : P 0)
    (h₁ : ∀ n, P (succ n))
    (m : Nat) :
    P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'

-- `contradiction` searches for a contradiction
-- among the hypotheses of the current goal
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

-- can use `match` in tactic blocks
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr

-- or "combine" intro with match using this syntax
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption

-- 5.4. Structuring Tactic Proofs
