import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Example (from Patrick Massot's "Glimpse of Lean" tutorial)

Link to full tutorial: https://github.com/PatrickMassot/GlimpseOfLean

If you have a small screen and you are reading this in VSCode, you can press
`alt-Z` (or `option-Z`) to enable word wrap.

First let us see what a Lean proof looks like, without trying to understand any syntactical
detail yet. You won't have to type anything in this file.

If everything works, you currently see a panel to the right of this text with a
message like "No info found."
This panel will start displaying interesting things inside the proof.

Note that any text between `/-` and `-/` or after a `--` is a comment for you
that is ignored by Lean.

First let us review two calculus definitions.

-/

/-- A sequence `u` of real numbers converges to `l` if `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`.
This condition will be spelled `seqLimit u l`. -/
def seqLimit (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/- In the above definition, note that the `n`-th term of the sequence `u` is denoted
simply by `u n`.

Similarly, in the next definition, `f x` is what we would write `f(x)` on paper.
Also note that implication is denoted by a single arrow.

Something more subtle is that we write `l : ℝ` to say `l` is a real number, where you
may write `l ∈ ℝ` on paper.
-/

/-- A function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`.
This condition will be spelled `continuousAt f x₀`. -/
def continuousAt (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/-- Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.
Every thing on the next line describes the objects and assumptions, each with its name.
The following line is the claim we need to prove. -/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seqLimit u x₀) (hf : continuousAt f x₀) :
  seqLimit (f ∘ u) (f x₀) := by -- This `by` keyword marks the beginning of the proof
  -- Put your text cursor here and watch the panel to the right.
  -- To the right of the blue `⊢` symbol is what we are trying to prove. Above this
  -- is our list of variables and hypotheses. As you read the proof, move your cursor from
  -- line to line (for example with the down-arrow button) and watch the panel change.

  -- Our goal is to prove that, for any positive `ε`, there exists a natural
  -- number `N` such that, for any natural number `n` at least `N`,
  --  `|f(u_n) - f(x₀)|` is at most `ε`.
  unfold seqLimit
  -- Fix a positive number `ε`.
  intros ε hε
  -- By assumption on `f` applied to this positive `ε`, we get a positive `δ`
  -- such that, for all real numbers `x`, if `|x - x₀| ≤ δ` then `|f(x) - f(x₀)| ≤ ε` (1).
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- The assumption on `u` applied to this `δ` gives a natural number `N` such that
-- for every natural number `n`, if `n ≥ N` then `|u_n - x₀| ≤ δ`   (2).
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- Let's prove `N` is suitable.
  use N
  -- Fix `n` which is at least `N`. Let's prove `|f(u_n) - f(x₀)| ≤ ε`.
  intros n hn
  -- Thanks to (1) applied to `u_n`, it suffices to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property (2) and our assumption on `n`.
  apply Hu n hn
  -- This finishes the proof!
