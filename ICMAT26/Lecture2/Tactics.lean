/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic -- imports all Mathlib tactics

/-! # Tactics

In this file we describe the behaviour of the following Lean tactics and we give some examples.
* `sorry`
* `intro`
* `exact`
* `apply`
* `rcases`
* `constructor`
* `left`
* `right`
* `by_contra`
* `by_cases`
* `rfl`
* `rw`
* `have`
* `use`

TIP: Take advantage of Lean's interactive features. Inside a proof in tactic mode (starting with
`by`), by clicking at the end of each line, we can see in the `Lean InfoView` window the current
state of our proof.
-/

/- # Tactics -/

--  `P`, `Q` and `R` denote propositions.
variable (P Q R : Prop)

/- ## sorry
  `sorry` closes any goal and gives raise to a warning which appears in the "All Messages" section
  of the "Lean InfoView". At the bottom of the screen, we can see the total number of warnings.
-/

theorem fermats_last_theorem : ∀ (x y z : ℤ), ∀ n ≥ 3, x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  sorry

/- ## exact
If our goal is to prove `P` and we have the hypothesis `hP : P` available, we can close the goal by
using `exact hP`.

NOTE: `exact P` does not work (we should not confuse the proposition `P` with its proof `hP`).  -/

example (hP : P) (_hQ : Q) : P := by
  exact hP

/-  ## intro

Given the goal `P → Q`, the tactic `intro hP` introduces a local hypothesis `hP : P` and replaces
the goal by `Q`.

VARIANT: `intro` can also be used to introduce several variables at the same time. -/

example (hQ : Q) : P → Q := by
  intro hP
  exact hQ

example : Q → P → Q := by
  intro hQ hP
  exact hQ

/- ## apply

The `apply` tactic can be use to reason backwards. For example, given the tactic state

hPQ : P → Q
⊢ Q,

the effect of `apply hPQ` will be to change it to

hPQ : P → Q
⊢ P.

That is, proving `Q` gets reduced to proving `P`, and the active hypotheses do not change.

In general, `apply h` tries to unify the current goal with the conclusion of the term `h`. If it
succeeds, the goal is replaced by one or several goals (as many as the number of premises of `h`).
-/

example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP


-- In this example, `apply` generates two subgoals
example (hP : P) (hQ : Q) (h : P → Q → Q) : Q := by
  apply h
  /- STYLE RECOMMENDATION: when the application of a goal introduces several new subgoals, it is
    recommended to use a central dot `·` before the proof of each of the goals.
    The dots are optional, but they serve to focus the goal: within the block introduced by the dot,
    only one goal is visible, and it must be completed before the end of the block -/
  · exact hP
  · exact hQ


/- ## rcases

`rcases` is a general purporse tactic to deconstruct hypotheses. Here we present some of the most
basic use cases.


### Examples

1) Given the hypothesis `hPaQ : P ∧ Q`, the instruction `rcases hPaQ with ⟨hP, hQ⟩` will delete
`hPaQ` and replace it by the two hypotheses
```
hP : P
hQ : Q
```
-/

example (hPaQ : P ∧ Q) : P := by
  rcases hPaQ with ⟨hP, hQ⟩
  exact hP

/-
2) Given the hypothesis `hPiQ : P ↔ Q`, `rcases hPiQ with ⟨hPQ, hQP⟩` will replace `hPiQ` by the
two hypotheses
```
hPQ : P → Q
hQP : Q → P
```

On the other hand, we will later see that the tactic `rw` can also be used with hypotheses of the
form  `h : P ↔ Q`, and we will need to figure out which tactic is more useful in each case. -/

example (hPiQ : P ↔ Q) (hQ : Q) : P := by
  rcases hPiQ with ⟨hPQ, hQP⟩
  exact hQP hQ

/-
3) Given the hypothesis `hPQ : P ∨ Q`, `rcases hPQ with (hP | hQ)`  divides the proof of the goal
in two cases: one assuming `hP : P` and one assuming `hQ : Q`.
-/

example (hPQ : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  rcases hPQ with (hP | hQ)
  · exact hPR hP
  · exact hQR hQ


/- ## constructor

If the current goal is a conjunction `⊢ P ∧ Q`, we can used the tactic `constructor` to replace it
by the two goals `⊢ P` and `⊢ Q`.

After using `constructor`, the style recommendation is to use a central dot `·` to indicate the
start of the proof of each of the new goals.

```
constructor
· proof of P
· proof of Q
```

Similarly, `constructor` transforms the goal `⊢ P ↔ Q` in two goals `⊢ P → Q` and `⊢ Q → P`.

-/

/- ## left

The tactic `left` replaces the goal `⊢ P ∨ Q` by `⊢ P`. -/

example (hP : P) : P ∨ Q := by
  left
  exact hP

/- ## right

The tactic `right` replaces the goal `⊢ P ∨ Q` by `⊢ Q`. -/

example (hQ : Q) : P ∨ Q := by
  right
  exact hQ

/- ## by_contra
The tactic `by_contra` allows us to write proofs by contradiction. Given the goal
```
⊢ P
```

the instruction `by_contra h` will change the "Tactic state" to

```
h : ¬P
⊢ false
```

-/

/-## by_cases

Given a proposition `P`, the tactic `by_cases h : P` divides the proof of the goal in two cases:
one assuming `h : P` and one assuming `h : ¬P`.
-/

example : P ∨ ¬ P := by
  by_cases hP : P
  · left
    exact hP
  · right
    exact hP

/- ## rfl
The `rfl` tactic closes goals of the form `⊢ P = Q` where `P` and `Q` are definitionally equal.
It also closes goals of the form `R x y`, where `x` and `y` are definitionally equal, and `R` is a
reflexive binary relation. -/

example : ¬ P ↔ P → False := by
  rfl

/- ## rw

Given an hypothesis `h : P = Q`, we can use `rw [h]` to replace each `P` in the goal by `Q`.
We can also use this tactic when `h` is a logical equivalence instead of an equality.
The argument `h` can be either a local hypothesis or a theorem.

NOTES:

1) If we want to use `h : P = Q` to replace `Q` by `P`, the syntax is `rw [← h]`. We can get the
arrow `←` by typing `\l`.

2) `rw` ONLY works with hypotheses of the form `a = b` or `P ↔ Q`, but not with simple implications
`P → Q` (in that situation, we would use the `apply` tactic).

3) `rw` can be applied to hypotheses, using the keyword `at`.

WARNING: `rw` always invokes the `rfl` tactic.
-/

example (a b : ℕ) (hab : a = b) (hb : b + 1 = 3) : a + 1 = 3 := by
  rw [hab]
  exact hb

example (h1 : P ↔ Q) (h2 : Q → R) : P → R := by
  rw [h1]
  exact h2

example (hQ : ¬ Q) : ¬ (P ∧ Q)  := by
  -- `not_and` is a proof of `¬(P ∧ Q) ↔ (P → ¬Q)`.
  rw [not_and]
  intro _
  exact hQ

example (hP : ¬P) (hPQ : P = Q) : ¬ Q := by
  rw [← hPQ]
  exact hP

example (h1 : P ↔ Q) (h2 : P → R) : Q → R := by
  rw [h1] at h2
  exact h2

/- ## have

`have`  is used to add a new hypothesis to the tactic state, which we will need to prove using
the existing hypotheses.

To use this tactic, we write
```
  have h : t := by
    p
```
where `h` is the name of the new hypothesis, `t` is what we want to show, and `p`
is a proof of it.  -/

example : (P → Q) → (¬ Q → ¬ P) := by
  intro hPQ hnQ hP
  have hQ : Q := by -- we introduce the hypothesis, which appears as a new goal in the tactic state
    --apply hPQ
    --exact hP
    exact hPQ hP -- we prove the new hypothesis
  exact hnQ hQ    -- we use it to prove the main goal


/- ## use
Given a goal `⊢ ∃ a, P a`, where `P a` is a proposition, if `x : X` is the term that we want to use
in the proof, the instruction `use x` will change the goal to `⊢ P x`.
-/

example : ∃ P : Prop, P ∧ True ↔ False := by
  use False
  tauto  -- closes the goal by creating a truth table


/- ## intro (new use case)
If the goal is of the form `∀ x : t, u x`, then `intro x` adds a local hypothesis
`x : t`  and replaces the goal by `⊢ u x`.
 -/

example (X : Type) : ∀ x : X, x = x := by
  intro x
  rfl

/- # A comment about `∀`
Whenever we have an hypothesis of the form `∀ x : t, u x`, we can instantiate it at any
particular term of type `t`.
-/
example (h : ∀ n : ℕ, n < n + 1) : 3 < 4 := by
  exact h 3


/- ## rcases (new use case)
Given a hypothesis `h : ∃ a : X, P a`, where `P a` is a proposition, the tactic
`rcases h with ⟨y, hy⟩` produces a term `x : X` and a proof `hx : P x`.
-/
example (X : Type) (P Q : X → Prop) (h : ∃ x : X, P x) :
    ∃ x : X, P x ∨ Q x := by
  rcases h with ⟨y, hy⟩
  use y
  left
  exact hy
