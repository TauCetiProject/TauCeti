/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
public import TauCeti.MeasureTheory.Function.Lp.Dual
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Weak derivatives from `Lᵠ` test bounds

For conjugate exponents `1 < p, q < ∞`, a distributional directional derivative bounded by
the `Lᵠ` norm of test functions is represented by an `Lᵖ` weak derivative, with the same
bound. This applies to locally integrable functions without assuming differentiability or a
weak derivative in advance. For a finite-dimensional real codomain the same holds coordinatewise,
with a constant depending only on the codomain. The proof extends the distributional functional
from the image of test functions in `Lᵠ` by Hahn–Banach, then uses the integral representation
of the dual.

The result assumes σ-finiteness on the open domain. The Hilbert-space theorem in
`TestFunctionLp/Basic` remains available without that measure hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.8.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter
open scoped ContDiff Distributions ENNReal NNReal

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

/-- **Vector-valued `Lᵖ` representation.** For a finite-dimensional real codomain, a
distributional directional derivative bounded by `M` times the conjugate `Lᵠ` test norm is an
`Lᵖ` weak derivative of norm at most `C * M`. The constant depends only on the codomain. The
scalar theorem is applied in the coordinates of a basis. -/
theorem exists_eLpNorm_le_hasWeakLineDerivOn_of_enorm_integral_lineDeriv_smul_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] (hq : 1 < q)
    (hq_top : q ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ u : E → G, LocallyIntegrableOn u Ω μ → ∀ (v : E) (M : ℝ≥0∞), M ≠ ⊤ →
      (∀ φ : 𝓓(Ω, ℝ), ‖∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ‖ₑ ≤
        M * eLpNorm (φ : E → ℝ) q μ) →
      ∃ g : E → G, HasWeakLineDerivOn μ Ω u g v ∧ eLpNorm g p (μ.restrict Ω) ≤ C * M := by
  classical
  have := FiniteDimensional.complete ℝ G
  let b := Module.finBasis ℝ G
  let c : Fin (Module.finrank ℝ G) → G →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap
    (b.coord i)
  refine ⟨∑ i, ‖c i‖₊ * ‖b i‖₊, fun u hu v M hM hbound => ?_⟩
  have hcu (i) : LocallyIntegrableOn (fun z => c i (u z)) Ω μ :=
    (c i).locallyIntegrableOn_comp hu
  have hscalar (i) : ∃ g : Lp ℝ p (μ.restrict (Ω : Set E)), ‖g‖ ≤ ‖c i‖ * M.toReal ∧
      HasWeakLineDerivOn μ Ω (fun z => c i (u z)) g v := by
    refine exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le_eLpNorm hq hq_top
      (hcu i) v (by positivity) fun φ => ?_
    have hφ : eLpNorm (φ : E → ℝ) q μ ≠ ⊤ :=
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).eLpNorm_ne_top
    have hint : ∫ z, lineDeriv ℝ (φ : E → ℝ) z v * c i (u z) ∂μ =
        c i (∫ z, lineDeriv ℝ (φ : E → ℝ) z v • u z ∂μ) := by
      rw [← (c i).integral_comp_comm (integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)]
      simp only [map_smul, smul_eq_mul]
    have hreal : ‖∫ z, lineDeriv ℝ (φ : E → ℝ) z v • u z ∂μ‖ ≤
        M.toReal * (eLpNorm (φ : E → ℝ) q μ).toReal := by
      rw [← ENNReal.toReal_mul, ← toReal_enorm]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hM hφ) (hbound φ)
    rw [hint, ← Real.norm_eq_abs, mul_assoc]
    exact ((c i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hreal (norm_nonneg _))
  choose g hgn hg using hscalar
  let w : E → G := fun z => ∑ i, (g i : E → ℝ) z • b i
  refine ⟨w, ?_, ?_⟩
  · refine (hasWeakLineDerivOn_iff_coordinates b).2 fun i => ?_
    refine (hg i).congr_ae_deriv (Eventually.of_forall fun z => ?_)
    simp [w, Finsupp.single_apply]
  · have hw : w = ∑ i, fun z => (g i : E → ℝ) z • b i := by
      funext z
      simp [w, Finset.sum_apply]
    rw [hw]
    refine (eLpNorm_sum_le Fact.out).trans ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hmeas : AEStronglyMeasurable (fun z => (g i : E → ℝ) z • b i)
        (μ.restrict (Ω : Set E)) :=
      (Lp.aestronglyMeasurable (g i)).smul_const _
    calc eLpNorm (fun z => (g i : E → ℝ) z • b i) p (μ.restrict (Ω : Set E))
        ≤ ‖b i‖₊ * eLpNorm (g i : E → ℝ) p (μ.restrict (Ω : Set E)) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas
            (Eventually.of_forall fun z => by rw [enorm_smul, mul_comm]; rfl) p
      _ ≤ ‖b i‖₊ * (‖c i‖₊ * M) := by
          gcongr
          rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_toReal hM,
            ← ENNReal.ofReal_coe_nnreal (p := ‖c i‖₊), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hgn i)
      _ = ↑(‖c i‖₊ * ‖b i‖₊) * M := by push_cast; ring

end TauCeti
