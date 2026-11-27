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

Over any `RCLike` scalar field, `Polynomial.exists_hilbertBasis_laguerreMeasure` and
`Polynomial.exists_hilbertBasis_laguerreFunction` identify the basis vectors by these formulas
almost everywhere for the Laguerre measure and for Lebesgue measure on `(0, ∞)`, respectively.

The bases specialize `TauCeti.hilbertBasisOfWeightedMeasure` and
`TauCeti.hilbertBasisOfOrthogonalSystem`, with completeness from
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`. The Laguerre weight and squared norms
are those of DLMF Table 18.3.1.
-/

public section

open MeasureTheory Set Real TauCeti

namespace Polynomial

variable {α : ℝ} {𝕜 : Type*} [RCLike 𝕜]

private theorem laguerre_basis_hypotheses (hα : -1 < α) :
    let w (x : ℝ) := x ^ α * exp (-x)
    let c (n : ℕ) := Gamma (n + α + 1) / n.factorial
    let f (n : ℕ) (x : ℝ) := (laguerre α n).eval x
    let μ : Measure ℝ := volume.restrict (Ioi 0)
    ∃ hmem : ∀ n, MemLp (fun x => algebraMap ℝ 𝕜 (f n x / sqrt (c n))) 2
        (μ.withDensity (fun x => ENNReal.ofReal (w x))),
      (∀ n, 0 < c n) ∧
      (∀ m n, (∫ x, f m x * f n x * w x ∂μ) = if m = n then c n else 0) ∧
      (Submodule.span 𝕜 (range (bareNormalizedLp f w c hmem)))ᗮ = ⊥ := by
  intro w c f μ
  have hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => exp (a * |x|)) (laguerreMeasure α) :=
    ⟨1 / 2, by norm_num, integrable_exp_mul_abs_laguerreMeasure hα (by norm_num)⟩
  rw [laguerreMeasure_def] at hexp
  have hc (n : ℕ) : 0 < c n :=
    div_pos (Gamma_pos_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])) (by positivity)
  have horth (m n : ℕ) :
      (∫ x, f m x * f n x * w x ∂μ) = if m = n then c n else 0 := by
    simpa only [f, w, c, μ, integral_laguerreMeasure, smul_eq_mul, mul_comm (_ ^ α * exp _)] using
      integral_laguerre_mul_laguerre_laguerreMeasure hα m n
  have hmem := memLp_two_bareNormalized (𝕜 := 𝕜) hexp (laguerre α) c
  exact ⟨hmem, hc, horth, orthogonal_span_range_bareNormalizedLp_eq_bot (laguerre α) w c
    (degree_laguerre α) hc hexp hmem⟩

/-- For `-1 < α`, the Laguerre polynomials divided by `√(Γ(n + α + 1) / n!)` form a Hilbert
basis of `L²` for the Laguerre measure. -/
theorem exists_hilbertBasis_laguerreMeasure (hα : -1 < α) :
    ∃ b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (laguerreMeasure α)), ∀ n,
      ⇑(b n) =ᵐ[laguerreMeasure α] fun x =>
        algebraMap ℝ 𝕜 ((laguerre α n).eval x / sqrt (Gamma (n + α + 1) / n.factorial)) := by
  rw [laguerreMeasure_def]
  obtain ⟨hmem, hc, horth, hcomplete⟩ := laguerre_basis_hypotheses (𝕜 := 𝕜) hα
  have hw := (ae_pos_laguerreWeight α).mono fun _ hx => hx.le
  have hm := aemeasurable_laguerreWeight α
  refine ⟨hilbertBasisOfWeightedMeasure _ _ _ hw hm hc horth hmem hcomplete, fun n => ?_⟩
  rw [coe_hilbertBasisOfWeightedMeasure]
  exact coeFn_bareNormalizedLp _ _ _ hmem n

/-- For `-1 < α`, the normalized Laguerre functions form a Hilbert basis of `L²((0, ∞))`
for Lebesgue measure. The `n`-th function is the normalized Laguerre polynomial times
`x ^ (α / 2) * exp (-x / 2)`. -/
theorem exists_hilbertBasis_laguerreFunction (hα : -1 < α) :
    ∃ b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume.restrict (Ioi (0 : ℝ)))), ∀ n,
      ⇑(b n) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x =>
        algebraMap ℝ 𝕜 ((laguerre α n).eval x * x ^ (α / 2) * exp (-x / 2) /
          sqrt (Gamma (n + α + 1) / n.factorial)) := by
  obtain ⟨hmem, hc, horth, hcomplete⟩ := laguerre_basis_hypotheses (𝕜 := 𝕜) hα
  have hw := ae_pos_laguerreWeight α
  have hm := aemeasurable_laguerreWeight α
  refine ⟨hilbertBasisOfOrthogonalSystem _ _ _ hw hm hc horth hmem hcomplete, fun n => ?_⟩
  refine (coeFn_hilbertBasisOfOrthogonalSystem _ _ _ hw hm hc horth hmem hcomplete n).trans ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
  simp only [sqrt_laguerreWeight hx.le, mul_assoc]

end Polynomial
