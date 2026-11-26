/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.SpecialFunctions.Laguerre.Measure
public import TauCeti.RingTheory.Polynomial.Laguerre.Basic
import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
import TauCeti.Analysis.SpecialFunctions.Laguerre.Orthogonality

/-!
# Hilbert bases from the Laguerre polynomials

For `α > -1` the Laguerre polynomials normalized by `√(Γ(n + α + 1) / n!)` form a Hilbert basis
of `L²(laguerreMeasure α)`. Multiplying these polynomials by `x ^ (α / 2) * exp (-x / 2)` gives
the Laguerre functions, a Hilbert basis for Lebesgue measure on `(0, ∞)`.

Completeness follows from the exact degrees and a finite exponential moment by
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`. The weighted and unweighted bases use
`TauCeti.hilbertBasisOfWeightedMeasure` and `TauCeti.hilbertBasisOfOrthogonalSystem`, respectively.
The Laguerre weight and squared norms are those of DLMF Table 18.3.1.
-/

public section

open MeasureTheory Set Real TauCeti

namespace Polynomial

variable {α : ℝ} {𝕜 : Type*} [RCLike 𝕜]

private theorem laguerre_normSq_pos (hα : -1 < α) (n : ℕ) :
    0 < Gamma (n + α + 1) / n.factorial :=
  div_pos (Gamma_pos_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])) (by positivity)

private theorem laguerreWeight_exp_moment (hα : -1 < α) :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => exp (a * |x|))
      ((volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (x ^ α * exp (-x))) := by
  rw [← laguerreMeasure_def]
  exact ⟨1 / 2, by norm_num, integrable_exp_mul_abs_laguerreMeasure hα (by norm_num)⟩

private theorem integral_laguerre_mul_laguerre_mul_weight (hα : -1 < α) (m n : ℕ) :
    (∫ x in Ioi 0, (laguerre α m).eval x * (laguerre α n).eval x * (x ^ α * exp (-x))) =
      if m = n then Gamma (n + α + 1) / n.factorial else 0 := by
  simpa only [integral_laguerreMeasure, smul_eq_mul, mul_comm (_ ^ α * exp _)] using
    integral_laguerre_mul_laguerre_laguerreMeasure hα m n

/-- For `-1 < α`, the Laguerre polynomials divided by `√(Γ(n + α + 1) / n!)` form a Hilbert
basis of `L²` for the Laguerre measure. -/
theorem exists_hilbertBasis_laguerreMeasure (hα : -1 < α) :
    ∃ b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (laguerreMeasure α)), ∀ n,
      ⇑(b n) =ᵐ[laguerreMeasure α] fun x =>
        algebraMap ℝ 𝕜 ((laguerre α n).eval x / sqrt (Gamma (n + α + 1) / n.factorial)) := by
  rw [laguerreMeasure_def]
  let w (x : ℝ) := x ^ α * exp (-x)
  let c (n : ℕ) := Gamma (n + α + 1) / n.factorial
  let f (n : ℕ) (x : ℝ) := (laguerre α n).eval x
  have hw := (ae_pos_laguerreWeight α).mono fun _ hx => hx.le
  have hm := aemeasurable_laguerreWeight α
  have hmem := memLp_two_bareNormalized (𝕜 := 𝕜) (laguerreWeight_exp_moment hα) (laguerre α) c
  have hcomplete := orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) (laguerre α) w c
    (degree_laguerre α) (laguerre_normSq_pos hα) (laguerreWeight_exp_moment hα) hmem
  refine ⟨hilbertBasisOfWeightedMeasure f w c hw hm (laguerre_normSq_pos hα)
    (integral_laguerre_mul_laguerre_mul_weight hα) hmem hcomplete, fun n => ?_⟩
  rw [coe_hilbertBasisOfWeightedMeasure]
  exact coeFn_bareNormalizedLp f w c hmem n

/-- For `-1 < α`, the normalized Laguerre functions form a Hilbert basis of `L²((0, ∞))`
for Lebesgue measure. The `n`-th function is the normalized Laguerre polynomial times
`x ^ (α / 2) * exp (-x / 2)`. -/
theorem exists_hilbertBasis_laguerreFunction (hα : -1 < α) :
    ∃ b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume.restrict (Ioi (0 : ℝ)))), ∀ n,
      ⇑(b n) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x =>
        algebraMap ℝ 𝕜 ((laguerre α n).eval x * x ^ (α / 2) * exp (-x / 2) /
          sqrt (Gamma (n + α + 1) / n.factorial)) := by
  let w (x : ℝ) := x ^ α * exp (-x)
  let c (n : ℕ) := Gamma (n + α + 1) / n.factorial
  let f (n : ℕ) (x : ℝ) := (laguerre α n).eval x
  have hw := ae_pos_laguerreWeight α
  have hm := aemeasurable_laguerreWeight α
  have hmem := memLp_two_bareNormalized (𝕜 := 𝕜) (laguerreWeight_exp_moment hα) (laguerre α) c
  have hcomplete := orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) (laguerre α) w c
    (degree_laguerre α) (laguerre_normSq_pos hα) (laguerreWeight_exp_moment hα) hmem
  refine ⟨hilbertBasisOfOrthogonalSystem f w c hw hm (laguerre_normSq_pos hα)
    (integral_laguerre_mul_laguerre_mul_weight hα) hmem hcomplete, fun n => ?_⟩
  refine (coeFn_hilbertBasisOfOrthogonalSystem f w c hw hm (laguerre_normSq_pos hα)
    (integral_laguerre_mul_laguerre_mul_weight hα) hmem hcomplete n).trans ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
  have hs : sqrt (x ^ α) = x ^ (α / 2) := by
    rw [sqrt_eq_rpow, ← rpow_mul hx.le, one_div, div_eq_mul_inv]
  dsimp only [f, w, c]
  rw [sqrt_mul (rpow_nonneg hx.le α), hs, ← exp_half, mul_assoc]

end Polynomial
