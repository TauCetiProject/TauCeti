/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Coarea
public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
import TauCeti.Analysis.BoundedVariation.Weighted.Gaussian
import TauCeti.Geometry.Euclidean.Volume.Sphere
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Checks for the weighted coarea formula

* **The norm on the Gaussian plane.** For `f(x) = ‖x‖` on `ℝ²`, `g = 1` and the Gaussian weight,
  the left side of the Lipschitz weighted coarea formula is `∫ ‖∇f‖ dγ = 1`
  (`lintegral_enorm_fderiv_norm_gaussianWeight`), since `‖∇f‖ = 1` off the origin, and the right
  side is computed independently: the level set `{‖x‖ = t}` is the circle of radius `t`, of length
  `2πt`, on which `e^{−W} = (2π)^{−1} e^{−t²/2}`, so it is
  `∫_0^∞ (2π)^{−1} e^{−t²/2} 2πt dt = 1` (`lintegral_setLIntegral_norm_preimage_gaussianWeight`).
* **Indicators.** For `u = 1_U` the superlevel set `{u > t}` is the whole space for `t < 0`, `U`
  for `0 ≤ t < 1` and empty for `t ≥ 1`, so for a `C¹` weight
  `∫_ℝ P_μ({1_U > t}; Ω) dt = ∫_0^1 P_μ(U; Ω) dt = P_μ(U; Ω)`
  (`lintegral_weightedPerimeter_setOf_lt_indicator`), as the weighted coarea formula requires of
  `V_μ(1_U; Ω) = P_μ(U; Ω)` (`weightedPerimeter_eq_lintegral_weightedPerimeter_setOf_lt_indicator`).
* **The identity on the Gaussian line.** For `u(t) = t` on `ℝ` with the Gaussian weight, the
  superlevel sets are the half-lines `(s, ∞)`, of Gaussian perimeter `φ(s)`
  (`gaussianPerimeter_Ioi`), so `∫_ℝ P_γ((s, ∞)) ds = ∫ φ = 1`
  (`lintegral_gaussianPerimeter_Ioi`) and the weighted coarea formula gives `V_γ(id; ℝ) = 1`
  (`weightedVariation_gaussianWeight_id`).
-/

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open scoped ENNReal RealInnerProductSpace

public noncomputable section

namespace TauCeti.Examples.WeightedCoarea

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E}

/-- The weighted perimeters of the superlevel sets of an indicator integrate to the weighted
perimeter of the set: `∫_ℝ P_μ({1_U > t}; Ω) dt = P_μ(U; Ω)`. -/
theorem lintegral_weightedPerimeter_setOf_lt_indicator (hW : ContDiff ℝ 1 W) (U : Set E) :
    ∫⁻ t, weightedPerimeter W Ω {x | t < U.indicator (1 : E → ℝ) x} = weightedPerimeter W Ω U := by
  have h : (fun t : ℝ => weightedPerimeter W Ω {x | t < U.indicator (1 : E → ℝ) x}) =
      (Ico 0 1).indicator fun _ => weightedPerimeter W Ω U := by
    funext t
    by_cases ht0 : t < 0
    · have : {x | t < U.indicator (1 : E → ℝ) x} = univ :=
        eq_univ_of_forall fun x => ht0.trans_le (indicator_nonneg (fun _ _ => zero_le_one) x)
      rw [this, weightedPerimeter_univ hW, indicator_of_notMem (by simp [ht0])]
    by_cases ht1 : t < 1
    · have : {x | t < U.indicator (1 : E → ℝ) x} = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, ht1, not_lt.1 ht0]
      rw [this, indicator_of_mem (by simp [not_lt.1 ht0, ht1])]
    · have : {x | t < U.indicator (1 : E → ℝ) x} = ∅ := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, not_lt.1 ht0, not_lt.1 ht1]
      rw [this, weightedPerimeter_empty, indicator_of_notMem (by simp [ht1])]
  rw [h, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- The weighted coarea formula for an indicator is the identity `P_μ(U; Ω) = P_μ(U; Ω)`. -/
theorem weightedPerimeter_eq_lintegral_weightedPerimeter_setOf_lt_indicator (hW : ContDiff ℝ 1 W)
    {U : Set E} (hU : MeasurableSet U) :
    weightedPerimeter W Ω U = ∫⁻ t, weightedPerimeter W Ω {x | t < U.indicator (1 : E → ℝ) x} := by
  rw [weightedPerimeter_def]
  exact weightedVariation_eq_lintegral_weightedPerimeter hW
    (locallyIntegrableOn_indicator_const hU.nullMeasurableSet (1 : ℝ))

/-- The Gaussian perimeter of the half-line `(s, ∞)` is `φ(s)`. -/
theorem gaussianPerimeter_Ioi (s : ℝ) :
    gaussianPerimeter (Ioi s) = ENNReal.ofReal (gaussianPDFReal 0 1 s) := by
  have h : Ioi s =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] {x : ℝ | ⟪x, (1 : ℝ)⟫ < s}ᶜ := by
    refine ae_restrict_of_ae ?_
    have : {x : ℝ | ⟪x, (1 : ℝ)⟫ < s}ᶜ = Ici s := by ext x; simp
    rw [this]
    exact Ioi_ae_eq_Ici
  rw [gaussianPerimeter_def, weightedPerimeter_congr_ae h,
    weightedPerimeter_compl contDiff_gaussianWeight, ← gaussianPerimeter_def,
    gaussianPerimeter_setOf_inner_lt (by simp) s]

/-- `∫_ℝ P_γ((s, ∞)) ds = ∫ φ = 1`. -/
theorem lintegral_gaussianPerimeter_Ioi : ∫⁻ s : ℝ, gaussianPerimeter (Ioi s) = 1 := by
  simp_rw [gaussianPerimeter_Ioi]
  exact lintegral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- **The weighted coarea formula on the Gaussian line**: `V_γ(id; ℝ) = ∫_ℝ P_γ((s, ∞)) ds = 1`. -/
theorem weightedVariation_gaussianWeight_id :
    weightedVariation (gaussianWeight ℝ) ⊤ id = 1 := by
  rw [weightedVariation_eq_lintegral_weightedPerimeter contDiff_gaussianWeight
    (continuous_id.locallyIntegrable.locallyIntegrableOn _), ← lintegral_gaussianPerimeter_Ioi]
  -- The superlevel set `{x | t < id x}` is the half-line `Ioi t`.
  simp_rw [gaussianPerimeter_def, id_eq, ← Set.Ioi_def]

/-! ### The norm on the Gaussian plane -/

/-- The `{‖x‖ = t}` fibre integral of the Gaussian density on `ℝ²` for `t > 0`: the density is
`(2π)^{−1} e^{−t²/2}` on the circle of radius `t`, of length `2πt`. -/
theorem setLIntegral_norm_preimage_gaussianWeight {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) ⁻¹' {t},
        ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x))
      ∂μHE[Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1] =
      ENNReal.ofReal (t * Real.exp (-(t ^ 2 / 2))) := by
  have hpre : (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) ⁻¹' {t} = sphere 0 t := by
    ext x
    simp
  rw [hpre, setLIntegral_congr_fun isClosed_sphere.measurableSet
    (g := fun _ => ENNReal.ofReal ((2 * Real.pi) ^
      (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ) / 2) * Real.exp (-(t ^ 2 / 2))))
    (fun x hx => by rw [exp_neg_gaussianWeight_of_norm_eq (by simpa using hx)]),
    setLIntegral_const, euclideanHausdorffMeasure_sphere_eq_mul_sphere_zero_one _ _ ht,
    euclideanHausdorffMeasure_sphere_zero_one_eq_ofReal]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.add_one_sub_one, pow_one]
  rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num [Real.rpow_neg_one, Real.Gamma_one]
  field_simp

/-- **The right side for `‖x‖` on the Gaussian plane**:
`∫_ℝ ∫_{‖x‖ = t} e^{−W} dμHE[1] dt = ∫_0^∞ (2π)^{−1} e^{−t²/2} 2πt dt = 1`. -/
theorem lintegral_setLIntegral_norm_preimage_gaussianWeight :
    ∫⁻ t, ∫⁻ x in (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) ⁻¹' {t},
        ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x))
      ∂μHE[Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1] = 1 := by
  -- The level sets are empty for `t < 0`, and `t = 0` is a null set of levels. On `t > 0` the
  -- fibre integral is `t e^{−t²/2}`, written in the form of Mathlib's Gamma-function integral.
  have hae : (fun t => ∫⁻ x in (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) ⁻¹' {t},
      ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x))
        ∂μHE[Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1]) =ᵐ[volume]
      (Ioi 0).indicator fun t =>
        ENNReal.ofReal (t ^ (1 : ℝ) * Real.exp (-(1 / 2) * t ^ (2 : ℝ))) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with t ht
    rcases lt_trichotomy t 0 with h | h | h
    · have : (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) ⁻¹' {t} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => by
          simp only [mem_preimage, mem_singleton_iff] at hx
          linarith [norm_nonneg x]
      rw [this, Measure.restrict_empty, lintegral_zero_measure,
        indicator_of_notMem (by simpa using h.le)]
    · exact absurd h ht
    · rw [setLIntegral_norm_preimage_gaussianWeight h, indicator_of_mem (by simpa using h),
        Real.rpow_one, Real.rpow_two]
      ring_nf
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (by norm_num) two_pos
    (b := 1 / 2) (by norm_num)
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal hint,
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by norm_num) (by norm_num)]
  · norm_num [Real.Gamma_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le

/-- **The left side for `‖x‖` on the Gaussian plane**: `∫ ‖∇‖x‖‖ dγ = 1`, since the gradient of
the norm has norm `1` off the origin, a Gaussian-null set. -/
theorem lintegral_enorm_fderiv_norm_gaussianWeight :
    ∫⁻ x, ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) x‖ₑ
      ∂weightedMeasure (gaussianWeight (EuclideanSpace ℝ (Fin 2))) = 1 := by
  -- Off the origin, a `volume`-null set, the gradient of the norm has norm `1`.
  have hae : ∀ᵐ x ∂weightedMeasure (gaussianWeight (EuclideanSpace ℝ (Fin 2))),
      ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖) x‖ₑ = 1 := by
    refine weightedMeasure_absolutelyContinuous.ae_le ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : EuclideanSpace ℝ (Fin 2)))]
      with x hx
    rw [← ofReal_norm, norm_fderiv_norm (differentiableAt_id.norm ℝ hx), ENNReal.ofReal_one]
  rw [lintegral_congr_ae hae, lintegral_one, weightedMeasure_def,
    withDensity_exp_neg_gaussianWeight, measure_univ]

end TauCeti.Examples.WeightedCoarea
