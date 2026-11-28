/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FrobeniusRiesz.CharacterAverage

/-!
# Main terms in the slope comparison for theta chains

The root-discriminant contribution to the logarithm of the Chowla–Selberg period
cancels the one in the level-prime bound. After cancellation the Stirling and level
terms together give exactly the main term of the Frobenius Riesz sum. In the
comparison for each word, the bulk divisibility and the type-prime contributions
also cancel, leaving only the net gain, the main term and the error budgets.

The main-term identity is Levent Alpöge's
`Formalism.RankGapBounds.WeightedMeanData.Data.key_identity`
in [`WeightedMeanData.lean`][key-identity]. The slope comparison follows
`Formalism.LFunctionChainParameters.WeightedSlopeBounds.each_unit_bound_statement`
in [`LevelOfCongruence.lean`][slope-comparison].

[key-identity]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean
[slope-comparison]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean
-/

public section

open Finset
open scoped BigOperators

namespace MonoidHom

variable {N : ℕ} [NeZero N] {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- The sum of the Frobenius main terms over the lifts `J` and top places `S` equals
Stirling's main term minus the CM period and the main term of the level-prime bound.
Here `rd` is the root discriminant and `dlog` is the real part of the quadratic
logarithmic derivative at `1`. The caps need only be nonzero on the quadratic kernel. -/
theorem sum_frobeniusRieszMainTerm_re_eq_stirling_sub_level
    (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ) {ι κ : Type*}
    (J : Finset ι) (S : Finset κ) (a : κ → ℝ) (w : ι → G → ℝ) {rd : ℝ}
    (hrd : rd ≠ 0) (hw : ∀ j ∈ J, ∀ g ∈ q.ker, w j g ≠ 0) :
    let dlog := (logDeriv (TauCeti.PrimitiveDirichletCharacter.of
      (MulChar.ofUnitHom (q.comp f))).character.LFunction 1).re
    let logPeriod := Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rd) - dlog
    (∑ j ∈ J, ∑ τ ∈ S, (f.frobeniusRieszMainTerm q (w j) (a τ)).re) =
      (J.card : ℝ) * (∑ τ ∈ S, (a τ * Real.log (a τ) - a τ - a τ * logPeriod)) -
        (∑ τ ∈ S, a τ) * ∑ j ∈ J, 𝔼 g with q g = 1, Real.log (w j g * rd / (2 * Real.pi)) := by
  intro dlog logPeriod
  let K := univ.filter fun g ↦ q g = 1
  have hK : K.Nonempty := ⟨1, by simp [K]⟩
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  have hlog : Real.log (2 * Real.pi / rd) = -Real.log (rd / (2 * Real.pi)) := by
    simp [Real.log_div, hπ, hrd, neg_sub]
  have hmean (j : ι) (hj : j ∈ J) :
      (𝔼 g ∈ K, Real.log (w j g * rd / (2 * Real.pi))) =
        (𝔼 g ∈ K, Real.log (w j g)) + Real.log (rd / (2 * Real.pi)) := by
    rw [← expect_const hK (Real.log (rd / (2 * Real.pi))), ← expect_add_distrib]
    -- Apply the log product law only on the kernel, where the caps are nonzero.
    refine expect_congr rfl fun g hg ↦ ?_
    have hq : q g = 1 := (mem_filter.mp hg).2
    rw [mul_div_assoc, Real.log_mul (hw j hj g (MonoidHom.mem_ker.mpr hq)) (div_ne_zero hrd hπ)]
  have hpoint (j : ι) (hj : j ∈ J) (τ : κ) :
      (f.frobeniusRieszMainTerm q (w j) (a τ)).re =
        (a τ * Real.log (a τ) - a τ) - a τ * logPeriod -
          a τ * (𝔼 g ∈ K, Real.log (w j g * rd / (2 * Real.pi))) := by
    rw [hmean j hj, frobeniusRieszMainTerm_def, ← Complex.ofReal_expect]
    simp only [Complex.re_ofReal_mul, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.one_re]
    dsimp only [logPeriod, dlog]
    rw [hlog]
    ring
  rw [sum_congr rfl (fun j hj ↦ sum_congr rfl fun τ _ ↦ hpoint j hj τ)]
  simp only [sum_sub_distrib, ← sum_mul, sum_const, nsmul_eq_mul, ← mul_sum]
  ring

open scoped Classical in
/-- Combine the source, division, level-prime, type-prime, frame and local-loss bounds
in a theta-chain slope comparison. The frame input is already bounded by `E₈ + E₉`;
the conclusion bounds the restricted prime sum minus its actual Frobenius main term.

`J` indexes the lifts, `S` the top places, and `W` the words of one translate. `src` and
`divided` are the source slopes before and after division, `height` bounds the pairing
height, and `target` is the target dual slope. `bulk` is the bulk divisibility;
`typeCost` and `loss` are the type-prime cost and remaining source loss at each word.
`logType` is the logarithm of the product of the type primes. Only words of
positive rank enter the comparison. `primeSum` is the restricted sum over all
top places and lifts, compared with `gain` by the local-loss bound. -/
theorem sub_sum_frobeniusRieszMainTerm_re_le_of_slope_bounds
    (f : (ZMod N)ˣ →* G) (q : G →* ℂˣ) {ι κ ω : Type*}
    (J : Finset ι) (S : Finset κ) (W : Finset ω) (a : κ → ℝ) (w : ι → G → ℝ)
    (rank : ω → ℕ) (hrank : 0 < ∑ u ∈ W, rank u) {rd : ℝ}
    (hrd : rd ≠ 0) (hw : ∀ j ∈ J, ∀ g ∈ q.ker, w j g ≠ 0)
    (ha : 0 ≤ ∑ τ ∈ S, a τ)
    {src divided height typeCost loss logLevel : ω → ℝ}
    {target gain bulk logType primeSum rankError E₂ E₃ E₄ E₅ E₆ E₇ E₈ E₉ : ℝ} :
    let A := ∑ τ ∈ S, a τ
    let logPeriod := Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rd) -
      (logDeriv (TauCeti.PrimitiveDirichletCharacter.of
        (MulChar.ofUnitHom (q.comp f))).character.LFunction 1).re
    let stirling := (J.card : ℝ) * ∑ τ ∈ S, (a τ * Real.log (a τ) - a τ - a τ * logPeriod)
    let level := ∑ j ∈ J, 𝔼 g with q g = 1, Real.log (w j g * rd / (2 * Real.pi))
    let typeTerm := (J.card : ℝ) * logType
    (∀ u ∈ W, rank u ≠ 0 → src u + gain + bulk - typeCost u - loss u ≤ divided u) →
    (∀ u ∈ W, rank u ≠ 0 → -E₅ ≤ src u) →
    (∀ u ∈ W, rank u ≠ 0 → target + height u - bulk ≤ stirling - A * logLevel u + E₂ + E₃) →
    (∀ u ∈ W, rank u ≠ 0 → level + typeTerm - rankError ≤ logLevel u) →
    (∀ u ∈ W, rank u ≠ 0 → typeCost u ≤ A * typeTerm + E₄) →
    (∀ u ∈ W, rank u ≠ 0 → loss u ≤ E₇) →
    (∑ u ∈ W, (rank u : ℝ) * (divided u - height u)) / (∑ u ∈ W, (rank u : ℝ)) -
      (E₈ + E₉) ≤ target →
    primeSum - gain ≤ E₆ →
    primeSum - (∑ j ∈ J, ∑ τ ∈ S, (f.frobeniusRieszMainTerm q (w j) (a τ)).re) ≤
      A * rankError + E₂ + E₃ + E₄ + E₅ + E₆ + E₇ + E₈ + E₉ := by
  intro A logPeriod stirling level typeTerm hsrc hsrc₀ hdiv hlevel htype hloss hframe hlocal
  let E := A * rankError + E₂ + E₃ + E₄ + E₅ + E₇
  have hword (u : ω) (hu : u ∈ W) (hu₀ : rank u ≠ 0) :
      gain + target - (stirling - A * level) - E ≤ divided u - height u := by
    have hlevel' := mul_le_mul_of_nonneg_left (hlevel u hu hu₀) ha
    -- The division bound cancels `bulk`; the level and type bounds cancel `A * typeTerm`.
    dsimp only [E]
    linarith only [hsrc u hu hu₀, hsrc₀ u hu hu₀, hdiv u hu hu₀, hlevel',
      htype u hu hu₀, hloss u hu hu₀]
  have hmass : 0 < ∑ u ∈ W, (rank u : ℝ) := by exact_mod_cast hrank
  have havg : gain + target - (stirling - A * level) - E ≤
      (∑ u ∈ W, (rank u : ℝ) * (divided u - height u)) / (∑ u ∈ W, (rank u : ℝ)) := by
    apply (le_div_iff₀ hmass).2
    rw [mul_comm, sum_mul]
    refine sum_le_sum fun u hu ↦ ?_
    by_cases hu₀ : rank u = 0
    · simp [hu₀]
    · exact mul_le_mul_of_nonneg_left (hword u hu hu₀) (Nat.cast_nonneg _)
  rw [f.sum_frobeniusRieszMainTerm_re_eq_stirling_sub_level q J S a w hrd hw]
  -- Use the same local names for the main term on both sides of the comparison.
  dsimp only [E] at havg
  linarith only [havg, hframe, hlocal]

end MonoidHom
