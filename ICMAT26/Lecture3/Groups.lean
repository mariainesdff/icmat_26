/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Group

/-!
# Subgroups and group homomorphisms

To practice using lemmas from the Mathlib library, we will create our own definition of
subgroup and prove results about it using Mathlib's groups API.

Next, we will prove some lemmas about group homomorphisms (for which we will use Mathlib's
definition of subgroup). -/

/-- `MySubgroup G` is the type of subgroups of a gorup `G`. -/
@[ext] structure MySubgroup (G : Type) [Group G] where
  carrier : Set G -- `carrier` is a subset of `G`
  one_mem' : (1 : G) ∈ carrier
-- we will later add a new version `one_mem` of this axiom which does not mention the `carrier`
  mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier -- same for `mul_mem`
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier -- same for `inv_mem`

/- NOTE: we do not want `MySubgroup` to be a class, since `G` can have multiple subgroups. -/

/- Thanks to the `@[ext]` tag, the `ext` tactic works on subgroups and allows us to replace an
  equality of subgroups `H₁ = H₂` by `∀ g, g ∈ H₁ ↔ g ∈ H₂`. -/

namespace MySubgroup

-- Let `G` be a group and `H` a subgroup of `G`.
variable {G : Type} [Group G] (H : MySubgroup G)

/-- This instance allows us to talk about elements of a subgroup, with the notation `x ∈ H`. -/
instance : Membership G (MySubgroup G) where
  mem H m := m ∈ H.carrier

/-- This instance allows us to regard `H : MySubgroup G` as a set `H : Set G`. -/
instance : Coe (MySubgroup G) (Set G) where
  coe H := H.carrier

/-- `g` is an element of `H` viewed as a subgroup of `G` if and only if `g` is an element of the
  subgroup `H` of `G`. -/
@[simp] lemma mem_coe {g : G} : g ∈ (H : Set G) ↔ g ∈ H := by
  -- These concepts mean the same thing
  rfl

/-- We add a new extensionality lemma: two subgroups of a group are equal if and only if they
  have the same elements. -/
@[ext] lemma ext' (H K : MySubgroup G) (h : ∀ g : G, g ∈ H ↔ g ∈ K) : H = K := by
  ext x
  exact h x

theorem one_mem : (1 : G) ∈ H := by
  apply H.one_mem'

theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := by
  apply H.mul_mem'

theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := by
  apply H.inv_mem'

/- ## Exercises about subgroups
In this section you can find some theorems about subgroups. To prove them, you need to use the
previous three lemmas, as well as some results available in Mathlib.

If `H : MySubgroup G`, and `x y : G`, the previous lemmas say:
`H.one_mem : (1 : G) ∈ H`
`H.mul_mem : x ∈ H → y ∈ H → x * y ∈ H`
`H.inv_mem : x ∈ H → x⁻¹ ∈ H`
-/


@[simp] theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H := by
  sorry

theorem mul_mem_cancel_left {x y : G} (hx : x ∈ H) : x * y ∈ H ↔ y ∈ H := by
  sorry -- Exercise

-- You will need the following lemma from Mathlib
--#check Set.mem_setOf_eq
/-- `Conjugate H g` is the Conjugate subgroup `gHg⁻¹` of `H`. -/
def Conjugate (H : MySubgroup G) (g : G) : MySubgroup G where
  carrier := { a : G | ∃ h ∈ H, a = g * h * g⁻¹ }
  one_mem' := by
    sorry
  inv_mem' := by
    sorry -- Exercise
  mul_mem' := by
    sorry -- Exercise

end MySubgroup

/-
# Group Homomorphisms
We create the type `GroupHom G H` of group homomorphisms from `G` to `H`, and we set up the
notation `G →** H`, that is, `f : G →** H` denotes a group homomorphism `f` from `G` to `H`. -/

/-- `GroupHom G H` is the type of group homomorphisms from `G` to `H`. -/
@[ext] structure GroupHom (G H : Type) [Group G] [Group H] where
  to_fun : G → H
  map_mul' (a b : G) : to_fun (a * b) = to_fun a * to_fun b

namespace GroupHom

-- `G` and `H` are groups
variable {G H : Type} [Group G] [Group H]


-- We fix the notation
infixr:25 " →** " => GroupHom

/-- This instance allows us to treat a group homomorphism as a function. -/
instance : CoeFun (G →** H) (fun _ ↦ G → H) where
  coe := GroupHom.to_fun

/- The previous instance allows us to write `f a`. -/
lemma map_mul (f : G →** H) (a b : G) :
  f (a * b) = f a * f b := by
  -- `f.map_mul` and `f.map_mul'` are *definitionally equal*, but *syntactically different*.
  exact f.map_mul' a b

/- ## Group homomorphism exercises -/

-- Let `f` be a group homomorphism.
variable (f : G →** H)

-- The following lemma suggests a useful lemma for the proof of  `map_one`.
--example (a b : G) : a * b = b ↔ a = 1 := by apply?
-- Then use the tactic `swap` to switch the order of the goals
@[simp] lemma map_one : f 1 = 1 := by
  sorry -- Exercise

lemma map_inv (a : G) : f a⁻¹ = (f a)⁻¹ := by
  sorry

variable (G)

/-- `id G` is the identity homomorphism from `G` to `G`. -/
def id : G →** G where
  to_fun   := fun a ↦ a
  map_mul' := by sorry -- Exercise

variable {K : Type} [Group K] {G}

/-- `φ.comp ψ` is the composition of `φ` and `ψ`. -/
def comp (φ : G →** H) (ψ : H →** K) : G →** K where
  to_fun := fun g ↦ ψ (φ g)
  map_mul' := fun a b ↦ by sorry

lemma id_comp : (id G).comp f = f := by
  sorry -- Exercise

lemma comp_assoc {L : Type} [Group L] (φ : G →** H) (ψ : H →** K) (ρ : K →** L) :
    (φ.comp ψ).comp ρ = φ.comp (ψ.comp ρ) := by
  sorry -- Exercise

-- Recall the lemma `Set.mem_setOf_eq`.
--#check Set.mem_setOf_eq

/-- The kernel of a group homomorphism, as a subgroup of the domain. -/
def ker (f : G →** H) : Subgroup G where
  carrier := {g : G | f g = 1} -- Exercise
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

/-- The image of a group homomorphism, as a subgroup of the codomain. -/
def im (f : G →** H) : Subgroup H where
  carrier := {h : H | ∃ g : G, f g = h} -- Exercise
  one_mem' := by
    sorry
  mul_mem' :=  by
    sorry
  inv_mem' := by
    sorry

end GroupHom
