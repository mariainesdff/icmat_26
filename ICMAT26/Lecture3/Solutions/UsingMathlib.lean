/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
## Tools for using Mathlib effectively:
+ Search and automation tactics: `exact?`, `apply?`, `rw?`, `simp?`, `hint`, ...
+ Specialized tactics: `abel`, `ring`, `linarith`, `continuity`, ...
+ [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)
  Does not include Mathlib specific tactics.
+ [Tactic cheatsheet](https://leanprover-community.github.io/papers/lean-tactics.pdf)
+ [Tactic list](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)
  Incomplete, but contains most of the main tactics up to 2024.
+ [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  is great reference, but you either need to know where to look, or what names to expect. To help
  with naming, you can reference the
  [naming conventions](https://leanprover-community.github.io/mathlib_docs/naming.html).
+ [LeanSearch](https://leansearch.net/) is useful using natural language queries.
+ [Loogle](https://loogle.lean-lang.org) is useful if you know somehings about the types appearing
  in the statement.
+ [Zulip](https://leanprover.zulipchat.com‌/) in the `Is there code for X?` stream is a good place
  to ask for help.
+ [The undergrad list](https://leanprover-community.github.io/undergrad.html) gives some sense of
  what is available in Mathlib, but it's not exhaustive.
+ [Mathlib Changelog](https://mathlib-changelog.org/v4) helps with change tracking in Mathlib.

  Partially based on the LftCM 2024 talk by Jireh Loreaux, available at
  https://github.com/riccardobrasca/LFTCM2024/blob/master/LFTCM2024/UsingMathlib/Main.lean
-/

noncomputable section

/-!  ### Search and automation tactics.  -/

example (x : ℝ) : x.sqrt ^ 2 = x := by
  --exact? -- `exact?` could not close the goal. Try `apply?` to see partial suggestions.
  sorry

example (x : ℝ) : x.sqrt ^ 2 = x := by
  refine Real.sq_sqrt ?h -- We forgot the hypothesis `0 ≤ x`.
  sorry

example (x : ℝ) (hx : 0 ≤ x) : x.sqrt ^ 2 = x := by
  exact Real.sq_sqrt hx -- suggested by exact?

open scoped Real in
example : Real.sqrt π ^ 2 = π := by
  apply Real.sq_sqrt
  exact? says exact Real.pi_nonneg

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  -- Applying `rw?` twice gives
  rw [add_add_sub_cancel]
  rw [add_sub_cancel]

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  --`hint` suggests
  norm_num

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp only [fac]

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  continuity
  --exact continuous_iff_continuous_dist.mp hf -- suggested by hint

example {a b c d e : ℕ} (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  --`hint` suggests
  omega
  -- Note that it also suggests `norm_num`, which does not work in this case.

/-!  ### Domain-specific tactics.  -/

-- Continuity.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X : Type*} [TopologicalSpace X] {f : ℝ → X} (hf : Continuous f) :
    Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  continuity

-- Inequalities
example {a b c d e : ℕ} (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  omega -- For natural and integer linear arithmetic problems.

example {a b c d e : ℝ} (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith -- For inequalities in abstract types with a strict linear order.
  --omega --fails

example {X : Type*} [CommRing X] [LinearOrder X] [IsStrictOrderedRing X] {a b d : X}
    (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith -- For inequalities in abstract types with a strict linear order.

-- Abstract algebra

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel -- Normalize expressions in commutative groups

open commutatorElement -- to get the bracket notation for the commutator

/-Here the commutator of two elements of a group is denoted by `⁅g, h⁆`
and is defined to be `g * h * g⁻¹ * h⁻¹`.  -/
example {G : Type} [Group G] (g h : G) : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by
  group -- Normalize expressions in (non-commutative) groups

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

/-! ### [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)

Tip: search using lowercase letters and without spaces or underscores.

The search is "half case-sensitive" : if you write a capital letter, it will only match with
capital letters.
-/

/-! ### [LeanSearch](https://leansearch.net/) is useful for natural language queries. -/

/- Let's go back to the first example using LeanSearch. We might search for:
  [`The square of the square root of a real number is itself.`](https://leansearch.net/?q=The+square+of+the+square+root+of+a+real+number+is+itself.)-/
example {x : ℝ} (hx : 0 ≤ x) : x.sqrt ^ 2 = x := by
  exact Real.sq_sqrt hx -- Fourth suggestion (might vary)


/-! ### [Loogle](https://loogle.lean-lang.org) -/
/-
We go back to the first example, now using Loogle, which allow us to search for regular expressions.
* [`sqrt, ?x ^ 2`](https://loogle.lean-lang.org/?q=sqrt%2C+%3Fx+%5E+2)
  returns "unknown identifier `sqrt`", so we should use `Real.sqrt` instead.
+ [`Real.sqrt`](https://loogle.lean-lang.org/?q=Real.sqrt) 252 hits, our result is #37
+ [`Real.sqrt, ?x ^ 2`](https://loogle.lean-lang.org/?q=Real.sqrt%2C+%3Fx+%5E+2)
  returns all theorems involving `Real.sqrt` and `?x ^ 2`, but many more besides the one we want
+ [`⊢ Real.sqrt ?x ^ 2 = ?x`](https://loogle.lean-lang.org/?q=⊢+Real.sqrt+%3Fx+%5E+2+%3D+%3Fx)
  returns a result with this type in the conclusion, the only hit is the result we want.
-/
example {x : ℝ} (hx : 0 ≤ x) : x.sqrt ^ 2 = x := by
  exact Real.sq_sqrt hx

/-! ### Exercises. -/

/- 1) Prove the following lemmas using search, automation, or specialized tactics: -/

example {α : Type*} (s t u : Set α) (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  gcongr --suggested by hint

example {α : Type*} (s t u : Set α) : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  simp_all only [Set.mem_inter_iff, Set.mem_union, true_and] --suggested by hint

example {a b : ℝ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := by positivity
  linarith

/- 2) Use LeanSearch or Loogle to find the following results: -/

example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* RingHom.range f := by
  exact RingHom.quotientKerEquivRangeS f

/-
- LeanSearch: Search for [`First isomorphism theorem for commutative rings`](https://leansearch.net/?q=%E2%80%8BFirst+isomorphism+theorem+for+commutative+rings)
- Loogle: Search for [`_ ⧸ RingHom.ker _ ≃+* RingHom.range _`](https://loogle.lean-lang.org/?q=_+%E2%A7%B8+RingHom.ker+_+%E2%89%83%2B*+RingHom.range+_)
-/

/- Note : `Filter.Tendsto g (nhds b) (nhds a)` means that `g(x) : α` tends to `a : α` when `x : β`
  tends to `b : β`. -/
example {α β : Type*} [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [OrderTopology α]
    {f : β → α} {g : β → α} {h : β → α} {b : β} {a : α} (hg : Filter.Tendsto g (nhds b) (nhds a))
    (hh : Filter.Tendsto h (nhds b) (nhds a)) (hgf : g ≤ f) (hfh : f ≤ h) :
    Filter.Tendsto f (nhds b) (nhds a) := by
  exact Filter.Tendsto.squeeze hg hh hgf hfh

/-
- LeanSearch: Search for [`Sandwich lemma`](https://leansearch.net/?q=Sandwich+lemma)
- Loogle: Search for [`?f ≤ ?h, ?g ≤ ?f, |- Filter.Tendsto ?f _ (nhds _)`](https://loogle.lean-lang.org/?q=%3Ff+%E2%89%A4+%3Fh%2C+%3Fg+%E2%89%A4+%3Ff%2C+%7C-+Filter.Tendsto+%3Ff+_+%28nhds+_%29)
-/
