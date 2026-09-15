/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic

/-! # Sets -/

/- We define a type `Ω` and three sets `X`, `Y`, `Z` with elements of type `Ω`.
  (While this is not precise, you can think of `X, Y, Z` as subsets of a set `Ω`).
  We define terms `a, b, c, x, y, z` in `Ω`. -/
variable (Ω : Type) (X Y Z : Set Ω) (a b c x y z : Ω)

-- We open a custom `namespace` to avoid conflicts with Mathlib lemmas.
namespace Sets

/-!

# Subsets

The symbol `⊆` can be writte as `\sub` or `\ss`
-/

-- By definition, `X ⊆ Y` means `∀ a, a ∈ X → a ∈ Y`.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y := by rfl

lemma subset_refl : X ⊆ X := by
  intro x hx
  exact hx

/- In this lemma, after writing `rw [subset_def] at *`, hypothesis `hYZ` becomes
`hYZ : ∀ a ∈ Y, a ∈ Z` (and similarly for `hXY`).
Once we reduce the goal to`a ∈ Z`, we can continue the proof with `apply hYZ`.
It is often useful to think of `hYZ` as a function which, given a term `a` of type `Ω` and a proof
of `a ∈ Y`, returns a proof of `a ∈ Z`.
-/
lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z := by --Exercise
  rw [subset_def] at *
  intro a haX
  exact hYZ a (hXY a haX)

/-! # Equality of sets
Two sets are equal if and only if they have the same elements. In Lean, this lemma is called
`Set.ext_iff`. -/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) := by
  exact Set.ext_iff

/- When we want to reduce the goal `⊢ X = Y` to `a ∈ X ↔ a ∈ Y` for arbitrary `a : Ω`,
we use the `ext` tactic. -/
lemma Subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := by
  ext a
  exact ⟨fun haX ↦ hXY haX, fun haY ↦ hYX haY⟩

--Alternative proof:
lemma Subset.antisymm' (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := by
  ext a
  rw [subset_def] at *
  constructor
  · apply hXY
  · apply hYX

/-! ### Unions and intersections

Notation: use `\cup` or `\un` to obtain `∪`, and `\cap` or `\i` for `∩`. -/

lemma mem_union : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y := by rfl

lemma mem_inter : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y := by rfl

/- Unions. -/

lemma union_self : X ∪ X = X := by
  ext a
  rw [mem_union]
  tauto

lemma subset_union_left : X ⊆ X ∪ Y := by
  intro a haX
  left
  exact haX

lemma subset_union_right : Y ⊆ X ∪ Y := by -- Exercise
  intro a haY
  tauto

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z := by -- Exercise
  constructor
  · intro h
    constructor
    · intro a ha
      apply h
      apply subset_union_left
      exact ha
    · intro a ha
      apply h
      apply subset_union_right
      exact ha
  · intro ⟨hXZ, hYZ⟩ a ha
    rw [mem_union] at ha
    rcases ha with (hX | hY)
    · apply hXZ hX
    · apply hYZ hY

variable (W : Set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z := by -- Exercise
  intro a ha
  rw [mem_union] at *
  -- tauto -- closes the goal. Step by step below:
  rcases ha with (hW | hY)
  · left
    apply hWX hW
  · right
    apply hYZ hY

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z := by -- Exercise
  intro a ha
  rw [mem_union] at ha ⊢
  rcases ha with (hX | hZ)
  · left
    apply hXY hX
  · right
    exact hZ

/- Intersetions -/

lemma inter_subset_left : X ∩ Y ⊆ X := by
  intro x h
  rw [mem_inter] at h
  tauto

lemma inter_self : X ∩ X = X := by -- Exercise
  ext x
  rw [mem_inter]
  tauto

lemma inter_comm : X ∩ Y = Y ∩ X := by -- Exercise
  ext x
  simp only [mem_inter]
  tauto

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z := by -- Exercise
  ext a
  constructor
  · intro ⟨haX, haY, haZ⟩
    exact ⟨⟨haX, haY⟩, haZ⟩
  · intro ⟨⟨haX, haY⟩, haZ⟩
    exact ⟨haX, haY, haZ⟩

/-! ### Universal and exitential quantifiers -/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) := by -- Exercise
  constructor
  · intro h a ha
    apply h ⟨a, ha⟩
  · intro h ⟨x, hx⟩
    exact h x hx

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) := by -- Exercise
  constructor
  · intro h
    by_contra h'
    apply h
    intro a
    by_contra ha
    apply h' ⟨a, ha⟩
  · intro ⟨x, hx⟩ h'
    exact hx (h' x)

end Sets
