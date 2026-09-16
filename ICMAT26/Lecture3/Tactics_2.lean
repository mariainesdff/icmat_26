/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import Mathlib.Tactic

/-!
# New tactics
* `ext`
* `swap`
* `simp` (`simp only`, `simp_rw`)
* `group`
* `abel`
-/

/- ## ext
To prove that two sets are equal, it is enough to show that they have the same elements.
Given the goal `⊢ S = T`, where `S` and `T` are sets (of elements of the same type), `ext a`
changes the goal to `⊢ a ∈ S ↔ a ∈ T`.
-/

example (X : Type) (S T : Set X) (hST : S ⊆ T) (hTS : T ⊆ S) : S = T := by
  ext a
  constructor
  · apply hST
  · apply hTS

example (X Y : Type) (f : X → Y) : id ∘ f = f := by
  ext x
  rw [Function.comp_apply, id_eq]

/- ## swap
The `swap` tactic exchanges the next two goals.

The related tactic `pick_goal n` moves the `n`th goal to the front.
-/

example {Ω : Type} {X Y : Set Ω} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := by
  ext a
  constructor
  swap
  · apply hYX
  · apply hXY


/- ## simp
In Mathlib, many equality or logical equivalence lemmas are tagged with `@[simp]`. We can also tag
lemmas we prove in other projects.

The `simp` tactic tries to find lemmas whose left hand side appears in the goal, and use them to
rewrite the LHS to the RHS (therefore, in lemmas tagged with `@[simp]`, the RHS whould be the
simpler expression).

We can provide extra arguments to the simplifier using the syntax `simp [lemma1, lemma2, ...]`.

`simp` can be used at local hypothesis, by writing `simp at h`.

`simp` should not be used in the middle of a proof before non-flexible tactics; in those cases
it should be replaced by a `simp only [...]` application, as explained below.
-/

example : (0 : ℝ) + 1 = 1 + 0 := by simp

example (n : ℕ) : ∑ i ∈Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp -- the sum over the empty set is 0 * (0 - 1) / 2
  | succ n hn =>
    rw [Finset.sum_range_succ, hn]
    simp -- reduces the goal to a ⊢ ↑n * (↑n - 1) / 2 + ↑n = (↑n + 1) * ↑n / 2
    ring


/- ### simp only
When we write `simp only [h₁, h₂, ..., hₙ]` instead of `simp [h₁, h₂, ..., hₙ]`, the simplifier
will only use the lemmas `hᵢ`, but not those tagged with `@[simp]`.
-/

example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, zero_sub, mul_neg,
        mul_one, neg_zero, zero_div] -- the sum over the empty set is 0 * (0 - 1) / 2
    | succ n hn =>
      rw [Finset.sum_range_succ, hn]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      -- the simp step reduces the goal to a ⊢ ↑n * (↑n - 1) / 2 + ↑n = (↑n + 1) * ↑n / 2
      ring -- to solve equations in commutative rings

/- ### simp?
`simp?` can be used to obtain the list of lemmas used in an application of `simp`.
-/

--example : (0 : ℝ) + 1 = 1 + 0 := by simp?

/- ## group and abel
The `group` tactic simplifies expressions in multiplicative groups, without assuming commutativity.

It does not use the local hypotheses, so it often needs to be combined with other tactics like `rw`.

`abel` solves equations in additive commutative groups. The related tactic `abel_nf` rewrites
all additive group expressions into a normal form
-/

example {G : Type} [Group G] (a b c d : G) (h : c = (a * b ^ 2) * ((b * b)⁻¹ * a⁻¹) * d) :
    a * c * d⁻¹ = a := by
  group at h -- normalizes `h` to `h : c = d`
  rw [h]     -- the goal is now `a * d * d⁻¹ = a`
  group      -- closes the goal

example {G : Type} [AddCommGroup G] (a b c d : G) (h : c = (a + 2 • b) + (-(b + b) + -a) + d) :
    a + c + -d = a := by
  abel_nf at h -- normalizes `h` to `h : c = d`
  rw [h]    -- the goal is now `a + d + -d = a`
  abel      -- closes the goal
