-- 4.1. The Universal Quantifier
example (α : Type) (p q : α → Prop) :
   (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

-- Example: proof of transitivity of relation r
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check @trans_r

#check trans_r

#check trans_r a b c

#check trans_r a b c hab

#check trans_r a b c hab hbc

-- Making the inferrable arguments implicit
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r

#check trans_r hab

#check trans_r hab hbc


variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

-- 4.2 Equality

#check Eq.refl

#check Eq.symm

#check Eq.trans

universe u

#check @Eq.refl.{u}

#check @Eq.symm.{u}

#check @Eq.trans.{u}


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

-- The same example using project notation
example : a = d :=
  (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

#check Eq.subst

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- 4.3. Calculational Proofs

variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

-- using rw
variable (a b c d e : Nat)
theorem T₁
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

variable (a b c d e : Nat)
theorem T₂
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

-- calc is usable for any relation that implements Trans type class
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

theorem divides_trans {x y z} (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

theorem divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example {x y z} (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " | " => divides

example {x y z} (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..

variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]

variable (x y : Nat)

-- alternative with using _ even in the first "equation" for nicer alighment
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   :=
      by rw [←Nat.add_assoc]

variable (x y : Nat)
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

-- 4.4. The Existential Quantifier

-- introduction
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

-- intro using anonymous constructor
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

--
variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

--set_option pp.explicit true  -- display implicit arguments

#print gex1

#print gex2

#print gex3

#print gex4

-- elim
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, And.symm hw⟩)

-- elim with match
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, And.symm hw⟩

-- the same with type annotations
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, And.symm hw⟩

-- the same but also decomposing the "and" on the input side
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

-- or we can use pattern matching let expression
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

-- Or using implicit match in the fun expression
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

-- TODO continue from "In the following example, we define IsEven"
def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

-- more concise version of the above
theorem even_plus_even₁ (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

-- Exercises
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
    λ he => Exists.elim he (λ _x hr => hr)


example (a : α) : r → (∃ _x : α, r) :=
  λ hr => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ he =>
      Exists.elim he (λ hx conj => ⟨Exists.intro hx conj.left, conj.right⟩))
    (λ conj =>
      Exists.elim conj.left (λ hx hpx => Exists.intro hx ⟨hpx, conj.right⟩))

-- The same as above, more concise
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ ⟨hx, ⟨hpx, hr⟩⟩ => ⟨⟨hx, hpx⟩, hr⟩)
    (λ ⟨⟨hx, hpx⟩, hr⟩ => ⟨hx, ⟨hpx, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (λ ⟨hx, hpoq⟩ =>
      Or.elim hpoq
        (λ hpx => Or.inl ⟨hx, hpx⟩)
        (λ hqx => Or.inr ⟨hx, hqx⟩))
    (λ heoe =>
      Or.elim heoe
        (λ ⟨hx, hpx⟩ => ⟨hx, Or.inl hpx⟩)
        (λ ⟨hx, hqx⟩ => ⟨hx, Or.inr hqx⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (λ hfxpx ⟨hx, npx⟩ => npx (hfxpx hx))
    (λ hnegEx hx => byContradiction (λ nphx => hnegEx ⟨hx, nphx⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (λ ⟨hx, hpx⟩ hfxnpx => hfxnpx hx hpx)
    (λ hnfxnpx : ¬∀ x, ¬p x => byContradiction
      (λ hnexpx : ¬∃ x, p x  =>
        have hfxnpx : ∀ x, ¬p x := λ hx hnpx => hnexpx ⟨ hx, hnpx ⟩
        hnfxnpx hfxnpx
     ))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (λ (hne : ¬∃ x, p x) (hx : α) (hpx : p hx) => hne ⟨hx, hpx⟩ )
    (λ (hfx : ∀ x, ¬p x) ⟨hx, hpx⟩ => hfx hx hpx)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ nfxpx =>
        byContradiction (λ hnexnpx : ¬∃ x, ¬p x =>
          have h1 : ∀ x, p x := λ hx => byContradiction (λ hnpx => hnexnpx ⟨hx, hnpx⟩ )
          nfxpx h1))
    (λ ⟨hx, hnpx⟩ hfx => hnpx (hfx hx))


example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ hfx ⟨hx, hpx⟩ => hfx hx hpx)
    (λ hexToR hx phx => hexToR ⟨hx, phx⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
   Iff.intro
      (λ ⟨hx, hf⟩ f => hf (f hx))
      (λ f => Or.elim (em (∀ x, p x))
        (λ g => ⟨ a, λ _ => f g  ⟩ )
       (λ nfx =>
          have hex : ∃ x, ¬ p x :=
            byContradiction (λ hnexnpx : ¬∃ x, ¬p x =>
              nfx (λ hx => byContradiction (λ hnpx => hnexnpx ⟨hx, hnpx⟩)))
          Exists.elim hex (λ hx hnpx => ⟨hx, λ hpx => absurd hpx hnpx⟩))
        )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ ⟨hx, hf⟩ f => hf (f hx))
    (λ f =>
      byContradiction (λ hnex : ¬∃ x, p x → r =>
        have h1 : ∀ x, p x := λ x =>
          Or.elim (em (p x))
            id
            (λ hnpx => False.elim (hnex ⟨x, λ hpx => absurd hpx hnpx⟩))
        hnex ⟨a, λ _ => f h1⟩))


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ ⟨hx, hf⟩ hr => ⟨hx, hf hr⟩ )
    (fun f =>
      Or.elim (em r)
      (λ hr : r =>
        match f hr with
         | ⟨x, hpx⟩ => ⟨x, λ _ => hpx⟩)
      (λ hnr : ¬r => ⟨a, λ hr => False.elim (hnr hr)⟩)
    )

-- 4.5. More on the Proof Language
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

-- 4.6. Exercises

-- 1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (λ hfa => And.intro (λ hx => (hfa hx).left) (λ hx => (hfa hx).right))
    (λ ⟨hfp, hfq⟩ hx => ⟨hfp hx, hfq hx⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    λ hfpq hfp hx => (hfpq hx) (hfp hx)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ hpq hx =>
    Or.elim hpq
      (λ hfp => Or.inl (hfp hx))
      (λ hfq => Or.inr (hfq hx))

-- 2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  λ ha : α => Iff.intro
    (λ (hfr : ∀ x, r) => hfr ha)
    (λ hr : r => λ _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ hfpr => Or.elim (em r)
      (λ hr => Or.inr hr)
      (λ hnr : ¬r => Or.inl (λ hx => Or.elim (hfpr hx)
        (λ hpx => hpx)
        (λ hr => False.elim (hnr hr)))))
    (λ hor hx => Or.elim hor
      (λ hfx => Or.inl (hfx hx))
      (λ hr => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ hf hr hx => hf hx hr)
    (λ hf hx hr => hf hr hx)

-- 3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  Or.elim (em (shaves barber barber))
    (λ hp => (h₁.mp hp) hp)
    (λ hnp => hnp (h₁.mpr hnp))

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have hn : ¬ shaves barber barber := fun hp => h₁.mp hp hp
  hn (h₁.mpr hn)

-- 4
variable (n m : Nat)

def even (n : Nat) : Prop :=
  ∃ m : Nat, n = 2 * m

def prime (n : Nat) : Prop :=
  n ≥ 2 ∧ ∀ m : Nat, m | n → m = 1 ∨ m = n

def infinitely_many_primes : Prop :=
  -- my first attempt:
  --∀ n : Nat, (prime n → ∃ m : Nat, n < m ∧ prime m)
  -- Claude:
  ∀ n : Nat , ∃ p, p > n ∧ prime p

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ k : Nat, n = 2^(2^k) + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, ∃ p, p > n ∧ Fermat_prime p

def goldbach_conjecture : Prop :=
  ∀ n : Nat, 2 < n ∧ even n → ∃ p q : Nat, n = p + q ∧ prime p ∧ prime q

-- is the proposition that every odd number greater than 5 can be expressed as
-- the sum of three (not necessarily distinct) primes.
def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, 5 < n ∧ ¬even n → ∃ p q r : Nat, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop :=
  ¬ ∃ a b c n : Nat, n > 2 ∧ a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n
