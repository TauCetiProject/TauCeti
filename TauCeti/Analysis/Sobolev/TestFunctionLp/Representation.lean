/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp
public import TauCeti.MeasureTheory.Function.Lp.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak derivatives from `Lᵠ` test bounds

For conjugate exponents `1 < p, q < ∞`, a distributional directional derivative bounded by
the `Lᵠ` norm of test functions is represented by an `Lᵖ` weak derivative, with the same
bound. This applies to locally integrable functions without assuming differentiability or a
weak derivative in advance. The proof extends the distributional functional from the image
of test functions in `Lᵠ` by Hahn–Banach, then uses the integral representation of the dual.

The result assumes σ-finiteness on the open domain. The Hilbert-space theorem in
`TestFunctionLp` remains available without that measure hypothesis.

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
  [μ.IsOpenPosMeasure] {Ω : Opens E} [IsLocallyFiniteMeasure (μ.restrict Ω)]
  [SigmaFinite (μ.restrict Ω)] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- A distributional directional derivative bounded by the conjugate `Lᵠ` test norm is an
`Lᵖ` weak derivative with that bound. No regularity of `u` beyond local integrability is needed. -/
theorem exists_norm_le_hasWeakLineDerivOn_of_holderConjugate {u : E → ℝ}
    (hq : 1 < q) (hq_top : q ≠ ⊤) (hu : LocallyIntegrableOn u Ω μ) (v : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓(Ω, ℝ),
      |∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ| ≤ C * (eLpNorm (φ : E → ℝ) q μ).toReal) :
    ∃ g : Lp ℝ p (μ.restrict Ω), ‖g‖ ≤ C ∧ HasWeakLineDerivOn μ Ω u g v := by
  let T : 𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ q (μ.restrict Ω) :=
    { toFun := testFunctionLp q
      map_add' := testFunctionLp_add q
      map_smul' := testFunctionLp_smul q }
  let ℓ : 𝓓(Ω, ℝ) →L[ℝ] ℝ :=
    (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ) μ u).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v)
  have hℓ (φ : 𝓓(Ω, ℝ)) : ℓ φ = ∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ := by
    simp [ℓ, TestFunction.integralAgainstBilinCLM_eq_integral hu]
  let e := LinearEquiv.ofInjective T (testFunctionLp_injective q)
  let f₀ : LinearMap.range T →ₗ[ℝ] ℝ := ℓ.toLinearMap ∘ₗ e.symm.toLinearMap
  have hf₀ : ∀ s, ‖f₀ s‖ ≤ C * ‖s‖ := by
    intro s
    obtain ⟨φ, rfl⟩ := e.surjective s
    have hnorm : ‖e φ‖ = (eLpNorm (φ : E → ℝ) q μ).toReal := by
      rw [← Submodule.norm_coe, LinearEquiv.ofInjective_apply, ← toReal_enorm]
      exact congrArg ENNReal.toReal (enorm_testFunctionLp_eq_eLpNorm q φ)
    simpa [f₀, hℓ, hnorm] using hbound φ
  obtain ⟨Λ, hΛ, hΛnorm⟩ := exists_extension_norm_eq _ (f₀.mkContinuous C hf₀)
  let g := (Lp.dualEquiv ℝ (μ.restrict Ω) p q hq hq_top).symm (-Λ)
  refine ⟨g, ?_, ?_⟩
  · calc ‖g‖ = ‖Λ‖ := by simp [g]
         _ = ‖f₀.mkContinuous C hf₀‖ := hΛnorm
         _ ≤ C := LinearMap.mkContinuous_norm_le _ hC hf₀
  · refine hasWeakLineDerivOn_iff_testFunction.2
      ⟨inferInstance, hu, Lp.locallyIntegrableOn g Fact.out, fun φ => ?_⟩
    have hΛφ : Λ (T φ) = ℓ φ := by
      simpa [f₀, e, LinearEquiv.ofInjective_apply] using hΛ (e φ)
    have hpair : ∫ x in Ω, g x * T φ x ∂μ = -Λ (T φ) := by
      dsimp only [g]
      rw [← Lp.dualEquiv_apply hq hq_top, LinearIsometryEquiv.apply_symm_apply, neg_apply]
    have hrepr : ∫ x, (φ : E → ℝ) x • g x ∂μ = -ℓ φ := by
      rw [← setIntegral_smul_eq_integral_smul φ]
      calc ∫ x in Ω, (φ : E → ℝ) x • g x ∂μ = ∫ x in Ω, g x * T φ x ∂μ := by
             apply integral_congr_ae
             filter_upwards [testFunctionLp_apply_ae (mu := μ) q φ] with x hx
             simp [T, hx, mul_comm]
           _ = -ℓ φ := hpair.trans (congrArg Neg.neg hΛφ)
    rw [hrepr, neg_neg, hℓ]
    simp only [smul_eq_mul]

end TauCeti
