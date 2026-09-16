/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import Mathlib.Basic.Real.Basic -- We import the real numbers
import Mathlib.Analysis.Real.Sqrt  -- We import square roots of real numbers

/-!
Some of these exercises are adapted from the talk about structures and classes from LftCM 2022:
<https://icerm.brown.edu/video_archive/?play=2897>
-/

noncomputable section

open Nat

/-! # Structures

A `structure` is a collection of data fields, possibly with restrictions that these fields must
satisfy.

An `instance` of a structure is a concrete collection of data that satisfy the constraints.

-/

/-- An element of ℝ³ is a tuple of three real numbers. -/
@[ext] structure R3 where
  x : ℝ
  y : ℝ
  z : ℝ

/- Marking the definition with the `@[ext]` tag makes Lean generate theorems to prove that two
terms of type `R3` are equals when their components agree. It will also allow us to use the `ext`
tactic on goals of that type. -/
/- What is the type of `R3`? -/
--#check R3

/- There are several ways to create an instance of the structure `R3` -/

/- If we do not know which fields we need to provide to create an instance of a structure, we can
replace the sorry by an underscore `_`, click on the lightbulb, and select the option
 "Generate a skeleton for the structure under construction".-/
def R3_ex : R3 := sorry

-- This syntax also allows us to specify the fields in a different order.
--#check ({x := 1, z := 3.5, y := Real.sqrt 2,} : R3)

-- The default constructor is called `R3.mk`.
--#check R3.mk 1 (Real.sqrt 2) 3.5

-- We can also use the anonymous constructor syntax.
--#check (⟨1, Real.sqrt 2, 3.5⟩ : R3)

/- Two instances of `R3` are equal when their three fields agree. -/

example (a b : R3) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  exacts [hx, hy, hz] -- with this syntax, we can close all 3 goals simultaneously.

/- Given an instance of `R3`, we can access each of the coordinates: -/

def v : R3 := ⟨1, 2, 3⟩
--#check R3.x
--#check v.z

/- Structures can also have propositional fields. -/

@[ext] structure R3_plus where
  (x y z : ℝ)
  x_pos : x > 0
  y_pos : y > 0
  z_pos : z > 0

--#check R3_plus.mk

/- When are two terms of `R3_plus` equal? -/

example (a b : R3_plus) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  exacts [hx, hy, hz]

/- Lastly, we can also create structures with parameters. -/

/-- We define ℝ^n, where `n` is a natural number. -/
structure Rn (n : ℕ) where
  coeff : Fin n → ℝ

--variable (n : ℕ)
--#check Rn n

--#check Rn.mk
--#check Rn.mk (fun (k : Fin 5) ↦ k)
--def ex : Rn 5 := ⟨fun k ↦ k⟩

/-- The following definition is different: it includes n-tuples of real numbers for any `n`. -/
structure Rn' where
  n : ℕ
  coeff : Fin n → ℝ

--#check Rn'.mk 5 (fun k ↦ k)

/-!
## Exercises about creation of structures
In the following exercises, you are asked to create a structure in Lean to represent each of the
described mathematical objects. The proposed solutions are not always unique; please ask me if
you are not sure of whether your solution is correct.
-/

/- Create a type `EvenNaturalNumber`, consisting of pairs in thich the first component is a natural
number and the second is a proof that the number is even. -/
structure EvenNaturalNumber : Type where
  n : ℕ
  even_n : Even n

/- Define a structure whose terms are two distinct natural numbers. -/
structure TwoDistinctPoints where
  x : ℕ
  y : ℕ
  x_ne_y : x ≠ y

/- Define a structure of eventually constant sequences `ℕ → ℕ`. The first field will be a sequence
  `seq : ℕ → ℕ`, and the second will be the statement that `seq` satisfies the desired property. -/
structure EventConstSeq where
  seq : ℕ → ℕ
  event_const : ∃ N : ℕ, ∀ n ≥ N, seq n = seq N

/- Define a multiplicative group structure on a type `G`. To do this, you will need data fields to
indicate the operations and the identity element, and propositional fields to establish the desired
axioms. -/
structure MyGroup (G : Type) where
  one : G
  mul : G → G → G
  inv : G → G
  mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z) --∀ x y z, (x*y)*z = x*(y*z)
  one_mul : ∀ (x : G), mul one x = x --∀ x, 1*x = x
  inv_mul_self : ∀ (x : G), mul (inv x) x = one -- --∀ x, x⁻¹ * x = 1
