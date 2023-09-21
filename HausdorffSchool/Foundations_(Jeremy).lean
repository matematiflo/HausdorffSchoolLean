/-
Notes on dependent type theory and Lean's formal foundation
Jeremy Avigad
Hausdorff School: *Formal Mathematics and Computer-Assisted Proving*
September 18 - 22, 2023

https://tinyurl.com/bonn-dtt
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Explode

/-
Outline:

Dependent Type Theory as a foundation for mathematics
- from propositional logic to DTT
    logic
    history
- overview of DTT itself
    syntax
    core system
      universes
      dependent function types
      inductive types
    additional axioms / constructions
      propositional extensionality
      quotients (=> function extensionality)
      choice

References:
- Avigad, "Foundations"
    https://arxiv.org/abs/2009.09541
- Theorem Proving in Lean 4
    https://leanprover.github.io/theorem_proving_in_lean4/
- Avigad, *Mathematical Logic and Computation*,
    https://doi-org.cmu.idm.oclc.org/10.1017/9781108778756
- Sørensen and Urzyczyn, Lectures on the Curry-Howard Isomorphism
- The HoTT book (the appendices)
    https://homotopytypetheory.org/book/
- Mimram, *Program=Proof*
    http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/course.pdf
- Nordström, Petersson, and Smith, *Programming in Martin-Löf's Type Theory: An Introduction*
- Nederpelt and Geuvers, *Type Theory and Formal Proof: An Introduction*
-/

/-
Propositional logic.
-/

section propositional_logic

variable (P Q R : Prop)

#check P ∧ Q
#check P ∨ Q
#check P → Q
#check True
#check False
#check ¬ P
#check P ↔ Q

#check true

#check @And
#check @Or
#check @Not

/-
Semantics

- classical: truth table semantics, Boolean algebras
- intuitionistic: Kripke models, heyting algebras

Deduction

- Lean is a variant of Natural Deduction (Gentzen, 1930s)
- introduction and elimination rules

  Γ ⊢ A
  Γ ⊢ B
  ---------
  Γ ⊢ A ∧ B

  Γ ⊢ A ∧ B
  ---------
  Γ ⊢ A

  Γ ⊢ A ∧ B
  ---------
  Γ ⊢ B

  Γ, A ⊢ B
  ---------
  Γ ⊢ A → B

  Γ ⊢ A → B
  Γ ⊢ A
  ---------
  Γ ⊢ B
  
etc.
  
Actually, in Lean, the built-in ∧ elimination rule looks more like the one for ∨.
-/

theorem and_example : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  . exact h2
  . exact h1

#explode and_example

theorem or_example : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with h1 |  h2
  . right; exact h1
  . left; exact h2

#explode or_example

end propositional_logic

/-
First-order logic
-/

section first_order_logic

variable (U : Type)

-- function symbols
variable (f : U → U) (g : U → U → U)
variable (P : U → Prop) (R : U → U → Prop)

#check ∀ x, P x → ∃ y, R y (f x)

/-
Semantics

- classical: models, complete Boolean algebras
- intuitionsitic: Kripke models, Beth models, categorical semantics,
  complete Heyting algebras

Deduction

- extend natural deduction with rules for ∀, ∃, =

Expressivity

- The set of provable sentences in first-order logic and any reasonable
  "foundational" extension thereof is Sigma_1 complete (under 1-1 reduction),
  i.e. equivalent (in a strong sense) to the Halting problem.

- So, in principle, it's all you need.

Other logics move the content (e.g. set theory) into the logical framework.
The logical framework becomes more complex, but also more useful:

- error checking
- filling in implicit information
-/

-- A slight variant: many-sorted first-order logic

variable (U1 U2 U3 : Type*)
variable (h : U1 → U1 → U2)
variable (q : U1 → U3 → Prop)

variable (Point Line Plane : Type*)
variable (onl : Point → Line → Prop)

variable (ax1 : ∀ p q : Point, ∃ L : Line, onl p L ∧ onl q L)
variable (ax2 : ∀ p q : Point, ∀ L M : Line, p ≠ q → onl p L ∧ onl q L →
  onl p M → onl q M → L = M)

end first_order_logic

/-
Simply typed lambda calculus
-/

section

#check Nat
#check Bool
#check Nat → Bool
#check Nat → Bool → Bool

#check λ x : Nat ↦ x
#check λ (x : Nat) ↦ x
#check fun x : Nat => x
#check fun (x : Nat) => x

variable (f : Nat → Nat) (g : Nat → Bool)

#eval (fun (f : Nat → Nat) => (fun x => f (f x))) Nat.succ 0
#eval (fun x => if x > 3 then 1 else 0) 5

def fact : Nat → Nat
  | 0 => 1
  | x + 1 => (x + 1) * fact x

#eval fact 100

end

/-
Higher-order logic
-/

section higher_order_logic

/-
There were various formulations in the early 20th century.

Russell and Whitehead used a *ramified type theory*, but also added an
axiom of reducibility.

In the late 1920s, Frank Ramsey and Leon Chwistek described versions of type
theory without reducibility.

In 1940, Alonzo Church gave an elegant formulation, "Simple type theory."
- simple types
- simply typed lambda calculus
- add a type of propositions

Conceptually, we define:
- the simple types
- the terms
- proofs
-/

variable (B1 B2 B3 B4 : Type*)

-- simple types: start with basic types, close under constructions

#check B1 → B2
#check B1 → (B2 → B3)
#check B1 × B2

-- simply typed lambda calculus: add lambda, application (and pairs and projections ...)

variable (f : B1 → B1)
variable (g : B1 → B2)
variable (h : B1 → B2 → B1)
variable (a : B1)

#check (fun x => g (f (f x))) (f a)
#check Prod.snd (a, a)

-- you can make this a first-order theory: add beta, eta

#check (fun x => ∀ y, ∃ z, f (f y) = h x (g z))

-- simply type theory: add Prop

#check (fun x : B1 => ∀ y, ∃ z, f (f y) = h x (g z))

-- add axioms for an infinite type (or add N as a basic type with induction) = higher-order arithmetic
-- add axioms for an infinite type (or add N as a basic type with induction) = higher-order arithmetic

#check fun f : Nat → Nat => ∃ x y, f (f x) = y + y

#check setOf
#check setOf (fun f : Nat → Nat => ∃ x y, f (f x) = y + y)

#check {f : Nat → Nat | ∃ x y, f (f x) = y + y}


example : (fun f : Nat → Nat => ∃ x y, f (f x) = y + y) =
           {f : Nat → Nat | ∃ x y, f (f x) = y + y} := rfl

end higher_order_logic

/-
Interlude

Notice the kinds of syntactic objects we need.

FOL:
- terms
- formulas
- proofs

Simple Type Theory:
- types
- terms
- (formulas a terms of type Prop)
- proofs

**In dependent type theory**,
- types,
- terms,
- formulas,
- proofs
are **all expressions in the same language**.
-/

/-
Dependent type theory: **types can depend on parameters**

So a function can return a type, and we may then have elements of that type
-/

section dependent_type_theory

variable (n : ℕ)

#check List ℕ
#check List (ℕ × ℕ) 
#check List (List ℕ) 

#check List
#check @List

#check Vector ℕ 5
#check Vector ℕ (n + 3)
#check Fin 5
#check @Vector
#check @Fin
#check @Matrix
#check Matrix ℝ (Fin 5) (Fin n)

variable (M : Matrix ℝ (Fin 5) (Fin n))

/-
We need a language where types are objects.
`T : Type`
`t : T`

As in simple type theory, we can add a type of propositions, Prop.
This gives us `P : Prop`.

While we are at it, we can add `p : P` for proofs. The language of
DTT is flexible enough to make this work, and then we have one language
for everything.

The syntax becomes more complicated, with basic judgments:
- Γ is a context
- Γ ⊢ t : T
- t ≡ t' : definitional equality

Everything lives in one language:
- `T : Type` is a data type
- `t : T` is an object of that type
- `P : Prop` is a proposition
- `p : P` is a proof of that proposition

E.g. `{x : ℕ // Even x ∧ x > 3}` builds an object out of a proposition
   (really, a function that returns a proposition)
We can write a function `f (x : ℝ) (h : x ≠ 0) : ℝ := ...`

Note that abstraction and application play dual roles:

- Given `f : ℕ → ℕ` and `a : ℕ`, we have `f x : ℕ`
- Given `h : P → Q` and `h' : P`, we have `h h' : Q`
-/

#check fun x : ℕ => x + 3
#check fun h : Even 3 => And.intro h h

#check @Even ℕ _ 

variable (t : Even 3)

#check (fun h : Even 3 => And.intro h h) t
example : Even 3 ∧ Even 3 := (fun h : Even 3 => And.intro h h) t
example : Even 3 ∧ Even 3 := And.intro t t

#reduce (fun h : Even 3 => And.intro h h) t

example : (fun h : Even 3 => And.intro h h) t = (And.intro t t) 
  := by
    rfl
    done

def two_is_even : Even 2 := by 
  unfold Even
  use 1
  done

#reduce (fun h : Even 2 => And.intro h h) two_is_even

/-
Definitions and theorems are essentially the same.

Definitions usually return an element of a type. Theorems usually return a proofs of a proposition.

The main difference is that Theorems are marked as opaque.
-/

def a : ℕ := 2

#check a

theorem foo : 2 + 2 = 4 := rfl 

-- `rfl : a = a` is the unique constructor of the equality type. This is the same as Eq.refl except that it takes `a` implicitly instead of explicitly.

theorem foo' : 2 + 2 = 4 := Eq.refl 4
theorem foo'' : 2 + 2 = 4 := Eq.refl (2 + 2)

#check foo
#check foo'
#check foo''

/-
Lean's logic has:
- Universes
- Dependent function types
- Inductive types

Additions:
- propositional extensionality
- quotients (which imply function extensionality)
- choice
-/

end dependent_type_theory

/-
History:
  Leibniz, seventeenth century: algebraic treatment of logic (calculemus!)
  1850s: Boole, DeMorgan: algebraic presentations of propositional logic
  later 19th century: Peirce, Schröder, others: functions, relations, and quantifers
  Frege: functions, relations, and quantifiers over higher-order logic
  1903: Russell's paradox
  1910-1913: Principia Mathematica
  Zermelo 1908: axiomatization of set theory (informally!)
  Hilbert school: 1910's: clear formulation of first-order logic
  1929: Gödel's completeness theorem (for first-order logic)
  1931: Gödel's incompleteness theorem (for arithmetic)
  1930's: computability and undecidability (Turing, Post, Church, Herbrand, Gödel)
  1940: simple type theory
  1930: Heyting, axiomatization of constructive logic
  1972: Martin-Löf, intuitionistic type theory
  1988: Thierry Coquand and Gerard Huet, calculus of constructions
  1990s: Paulin-Mohring, Dybjer: inductive types
-/

/-
For most types, we need:
- type formation rules (how to construct the type)
- introduction rules (how to build an element of the type)
- elimination rules (how to use an element of the type)
- computation rules (definitional equality)
-/

namespace dependent_type_theory

/-
Universes:

  Prop   = Sort 0
  Type 0 = Sort 1
  Type 1 = Sort 2
  Type 2 = Sort 3
  ...
-/

#check Prop
#check Type
#check Type 1
#check Type 2

#check (Prop : Type)
#check (Type : Type 1)
#check (Type 1 : Type 2)
#check (Type 2 : Type 3)

example : Sort 0 = Prop := rfl
example : Sort 1 = Type := rfl

#check Type*

universe u
universe v

#check Type u

/-
Dependent function types (aka Pi types)
-/

section
variable (A : Type u) (B : A → Type v)

-- formation
#check (x : A) → B x

variable (f : (x : A) → B x) (g : A → A) (a : A)

-- introduction
#check fun x : A ↦ f (g x)

-- elimination
#check f a

-- computation
example : (fun x : A ↦ f (g x)) a = f (g a) := rfl  -- beta
example : (fun x : A ↦ f x) = f := rfl              -- eta

#reduce (fun x : A ↦ f (g x)) a
#reduce (fun x : A ↦ f x)

end

-- When `B` does not depend on `A`, `(x : A) → B x` is written `A → B`.
-- These are the ordinary function types.

section
variable (A : Type u) (B : Type v)

-- formation
#check (x : A) → B

variable (f : A → B) (g : A → A) (a : A)

-- introduction
#check fun x : A ↦ f (g x)

-- elimination
#check f a

end

/-
Inductive types
-/

-- type former
inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

-- introduction rules
#check Nat.zero
#check Nat.succ

-- elimination rules
#check @Nat.rec

#check @Nat.rec ?P

def pred : Nat → Nat
  | Nat.zero     => Nat.zero
  | (Nat.succ n) => n

-- computation rules
example : pred (Nat.succ (Nat.succ (Nat.succ Nat.zero))) =
  Nat.succ (Nat.succ Nat.zero) := rfl

def add : Nat → Nat → Nat
  | x, Nat.zero   => x
  | x, Nat.succ y => Nat.succ (add x y)

inductive List (α : Type*)
| nil  : List α
| cons : α → List α → List α

/-
The pattern:
- Constructions can have parameters.
- There are zero or more constructors.
- Constructors can be recursive.
- The elimination rule says that to define a function on the type,
  it suffices to give a value for each constructor.
-/

inductive Foo
| bar : Foo → Foo

#check Foo
#check @Foo.bar

/-
enumerated types
-/

inductive Weekday : Type
| sunday : Weekday
| monday : Weekday
| tuesday : Weekday
| wednesday : Weekday
| thursday : Weekday
| friday : Weekday
| saturday : Weekday

inductive Unit : Type
| star : Unit

inductive Bool : Type
| false : Bool
| true  : Bool

inductive Empty : Type

/-
nonrecursive data types
-/

inductive Prod (α : Type u) (β : Type v)
| mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v)
| inl (a : α) : Sum α β
| inr (b : β) : Sum α β

inductive Sigma {α : Type u} (β : α → Type v)
| dpair : (a : α) → β a → Sigma β

inductive Option (α : Type*)
| none  : Option α
| some  : α → Option α

inductive Inhabited (α : Type*)
| mk : α → Inhabited α

/-
some more recursive types:
-/

inductive BinaryTree
| leaf : BinaryTree
| node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree
| leaf : CBTree
| sup : (ℕ → CBTree) → CBTree

-- a puzzle: what are the elements of this type?

inductive Foo'
| bar : Foo' → Foo'

def aux : (x : Foo') → (x ≠ x) := by
  {
    intro x
    induction x with
    | bar y ih => 
    by_contra _
    exact ih (Eq.refl y) 
  }

-- variable (X : Foo')
-- #check aux X 

#check Foo'

-- a challenge for Lean users: define a function of type `Foo' → Empty`

def f : Foo' → Empty := λ x => False.elim (aux x (Eq.refl x))

def g : Empty → Foo' := by 
{
  intro h
  cases h
}

-- def g' : Empty → Foo' := fun x => nomatch x 
def g' : Empty → Foo' := (nomatch ·)

theorem identify_Foo' : Foo' ≃ Empty where
  toFun := f
  invFun := g
  left_inv := (False.elim $ aux · rfl)
  -- left_inv := fun x => (aux x rfl).elim
  -- left_inv := fun x => (aux x (Eq.refl _)).elim
  right_inv := by {
    simp [Function.RightInverse, Function.LeftInverse]
    intro x
    cases x
  }

/-
Where does logic come from?

If `A B : Prop`, `A → B` is ordinary implication.

If `A : Type`, `B : A → Prop`, `(x : A) → B` **is** `∀ x : A, B`.

The other connectives (`True`, `False`, `∧`, `∨`, `∃`) are all defined inductively!
-/

section
variable (A B C : Prop)

variable (h1 : A → B) (h2 : B → C) (h3 : A)

-- elimination
#check h1 h3
#check h2 (h1 h3)

-- introduction
#check fun h : A ↦ h2 (h1 h)

theorem foo : A → C := by
  intro h
  apply h2
  apply h1
  apply h

example : A → C :=
  fun h : A ↦ h2 (h1 h)

#explode foo

end

section
variable (A : Type u) (B : A → Prop) (C : A → Prop)

#check (x : A) → B x

variable (h1 : ∀ x, B x) (h2 : ∀ x, B x → C x) (a : A)

-- elimination
#check h1 a
#check h2 a
#check h2 a (h1 a)

-- introduction
#check fun x => h2 x (h1 x)

example : ∀ x, C x := by
  intro x
  apply h2
  apply h1

theorem baz : ∀ x, C x := fun x => h2 x (h1 x)

#explode baz

end

/-
Define propositions inductively:
-/

inductive False : Prop

inductive True : Prop
| intro : True

inductive And (a b : Prop) : Prop
| intro : a → b → And a b

inductive Or (a b : Prop) : Prop
| inl : a → Or a b
| inr : b → Or a b

inductive Exists {α : Type*} (q : α → Prop) : Prop
| intro : ∀ (a : α), q a → Exists q

inductive Subtype {α : Type*} (p : α → Prop)
| mk : (x : α) → p x → Subtype p

#check Subtype

/-
structures are inductive types with a single constructor:
-/

structure Color where
 red : Nat
 green : Nat
 blue : Nat

inductive Color'
| mk (red : Nat) (green : Nat) (blue : Nat) : Color'

structure Semigroup :=
(Carrier : Type u)
(mul : Carrier → Carrier → Carrier)
(mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

#check Semigroup

class Semigroup' :=
(Carrier : Type u)
(mul : Carrier → Carrier → Carrier)
(mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

#check Semigroup'

/-
We have just described core Lean:
- Universes
- Dependent function types
- Inductive types

This gives logic, lots of data types, and algebraic structures.

For classical mathematics, Lean adds three axioms:

Additions:
- propositional extensionality
- quotients (which imply function extensionality)
- choice

For the additional axioms, see:
https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html

-/

/-
Propositional extensionality.

**This is why you can use "rewrite" with iff!**
-/

axiom propext {a b : Prop} : (a ↔ b) → a = b

def toEmpty : Foo → Empty
| Foo.bar f => toEmpty f

/-
Function extensionality.
-/

#check @funext

/-
Choice.
-/

class inductive Nonempty (α : Sort _) : Prop
| Intro : α → Nonempty α

axiom choice {α : Sort _} : Nonempty α → α

theorem choice2 {α : Sort _} {P : α → Prop} : (∃ x, P x) → {x // P x} := by
  intro h
  apply choice
  rcases h with ⟨a, ha⟩
  exact ⟨a, ha⟩

theorem choice3 {α β : Sort _} (R : α → β → Prop) (h : ∀ x, ∃ y, R x y) :
  ∃ f : α → β, ∀ x, R x (f x) := by
  use fun x => (choice2 (h x)).val
  intro x
  apply (choice2 (h x)).property

section
variable {α : Type*} {P : α → Prop} (h : ∃ x, P x)

#check Classical.choose h
#check Classical.choose_spec h

end

end dependent_type_theory

/-
Diaconescu's theorem (see TPIL)
-/

section
variable (P : Prop)

#check Classical.em P
#check Decidable P
#print Decidable
#check Classical.dec P

open Classical

theorem em_new (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩

  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV

  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne

  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _

  match not_uv_or_p with
    | Or.inl hne => Or.inr (mt p_implies_uv hne)
    | Or.inr h   => Or.inl h

end

/-
Quotients - see TPIL.
-/