/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
public import TauCeti.MeasureTheory.Function.Lp.Dual
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak derivatives from `Lᵠ` test bounds

For conjugate exponents `1 < p, q < ∞`, a distributional directional derivative bounded by
the `Lᵠ` norm of test functions is represented by an `Lᵖ` weak derivative, with the same
bound. This applies to locally integrable functions without assuming differentiability or a
weak derivative in advance. The proof extends the distributional functional from the image
of test functions in `Lᵠ` by Hahn–Banach, then uses the integral representation of the dual.

The result assumes σ-finiteness on the open domain. The Hilbert-space theorem in
`TestFunctionLp/Basic` remains available without that measure hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.8.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {Ω : Opens E} [IsLocallyFiniteMeasure (μ.restrict Ω)]
  [SigmaFinite (μ.restrict Ω)] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- A distributional directional derivative bounded by the conjugate `Lᵠ` test norm is an
`Lᵖ` weak derivative with that bound. No regularity of `u` beyond local integrability is needed. -/
theorem exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le_eLpNorm {u : E → ℝ}
    (hq : 1 < q) (hq_top : q ≠ ⊤) (hu : LocallyIntegrableOn u Ω μ) (v : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓(Ω, ℝ),
      |∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ| ≤ C * (eLpNorm (φ : E → ℝ) q μ).toReal) :
    ∃ g : Lp ℝ p (μ.restrict Ω), ‖g‖ ≤ C ∧ HasWeakLineDerivOn μ Ω u g v := by
  obtain ⟨Λ, hΛnorm, hΛφ⟩ :=
    exists_dual_norm_le_of_abs_integral_lineDeriv_mul_le_eLpNorm hu v hC hbound
  let g := (Lp.dualEquiv ℝ (μ.restrict Ω) p q hq hq_top).symm (-Λ)
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, LinearIsometryEquiv.norm_map, norm_neg] using hΛnorm
  · refine hasWeakLineDerivOn_iff_testFunction.2
      ⟨inferInstance, hu, Lp.locallyIntegrableOn g Fact.out, fun φ => ?_⟩
    have hpair : ∫ x in Ω, g x * testFunctionLp (mu := μ) q φ x ∂μ =
        -Λ (testFunctionLp (mu := μ) q φ) := by
      dsimp only [g]
      rw [Lp.integral_dualEquiv_symm_mul, neg_apply]
    have hrepr : ∫ x, (φ : E → ℝ) x • g x ∂μ = -(∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ) := by
      rw [← setIntegral_smul_eq_integral_smul φ]
      calc ∫ x in Ω, (φ : E → ℝ) x • g x ∂μ =
          ∫ x in Ω, g x * testFunctionLp (mu := μ) q φ x ∂μ := by
             apply integral_congr_ae
             filter_upwards [testFunctionLp_apply_ae (mu := μ) q φ] with x hx
             simp [hx, mul_comm]
           _ = _ := hpair.trans (congrArg Neg.neg (hΛφ φ))
    rw [hrepr, neg_neg]
    simp only [smul_eq_mul]

end TauCeti
