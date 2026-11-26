/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Checks for the coarea formula: the norm on a ball

For `f(x) = ‖x‖` on a finite-dimensional real inner product space `E` of dimension `n ≥ 1` and
`s` the ball of radius `R`, the coarea Jacobian `J f = ‖Df‖` is `1` away from the origin
(`normDet_adjoint_fderiv_norm`), so the coarea formula reads
`∫_ℝ H^{n-1}(B_R ∩ {‖x‖ = y}) dy = |B_R|`
(`lintegral_euclideanHausdorffMeasure_ball_inter_norm_preimage`). The fibre over `0 < y < R` is
the sphere of radius `y` (`ball_inter_norm_preimage_singleton`), so this is
`∫_0^R H^{n-1}(S_r) dr = |B_R|` (`lintegral_Ioo_euclideanHausdorffMeasure_sphere`), the identity
`TauCeti.volume_inter_ball_eq_lintegral_Ioo_euclideanHausdorffMeasure_inter_sphere` of polar
integration with `s` the whole space; with `H^{n-1}(S_r) = n |B_1| r^{n-1}`
(`TauCeti.euclideanHausdorffMeasure_sphere`) both sides are `|B_1| Rⁿ`.

For `n ≥ 2` the derivative `Df(x)` itself, a non-injective map `E → ℝ`, has norm determinant `0`
(`normDet_fderiv_norm`), so a Jacobian without the adjoint would give `0`.
-/

public section

noncomputable section

namespace TauCeti.Examples.CoareaNorm

open MeasureTheory Metric Module Set

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Away from the origin, the coarea Jacobian of the norm is `1`. -/
theorem normDet_adjoint_fderiv_norm {x : E} (hx : x ≠ 0) :
    (fderiv ℝ (‖·‖) x).adjoint.normDet = 1 := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  rw [ContinuousLinearMap.normDet_adjoint_eq_norm,
    norm_fderiv_norm ((contDiffAt_norm ℝ (n := 1) hx).differentiableAt one_ne_zero)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The fibre of the norm over `0 < y < R` inside the ball of radius `R` is the sphere of radius
`y`. -/
theorem ball_inter_norm_preimage_singleton {R y : ℝ} (hy : y < R) :
    ball (0 : E) R ∩ (‖·‖) ⁻¹' {y} = sphere 0 y := by
  ext x
  simp only [mem_inter_iff, mem_ball_zero_iff, mem_preimage, mem_singleton_iff,
    mem_sphere_zero_iff_norm]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h ▸ hy, h⟩

open LipschitzWith in
/-- **The coarea formula for the norm on a ball**: the integral over `y` of the
`(n - 1)`-dimensional measures of the fibres `{‖x‖ = y}` of the ball of radius `R` is its
volume. -/
theorem lintegral_euclideanHausdorffMeasure_ball_inter_norm_preimage [Nontrivial E] (R : ℝ) :
    ∫⁻ y : ℝ, μHE[finrank ℝ E - 1] (ball (0 : E) R ∩ (‖·‖) ⁻¹' {y}) = volume (ball (0 : E) R) := by
  have h := lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    (lipschitzWith_one_norm (E := E)) (measurableSet_ball (x := (0 : E)) (ε := R)).nullMeasurableSet
  rw [finrank_self] at h
  rw [h, ← setLIntegral_one]
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : E))] with x hx _
  rw [normDet_adjoint_fderiv_norm hx, ENNReal.ofReal_one]

/-- **The coarea formula for the norm, in polar form**: `∫_0^R H^{n-1}(S_r) dr = |B_R|`, read off
the coarea formula: the fibres over `y < 0` and `y ≥ R` are empty, and over `0 < y < R` they are
the spheres `S_y`. -/
theorem lintegral_Ioo_euclideanHausdorffMeasure_sphere [Nontrivial E] (R : ℝ) :
    ∫⁻ r in Ioo 0 R, μHE[finrank ℝ E - 1] (sphere (0 : E) r) = volume (ball (0 : E) R) := by
  have hsupp : Function.support (fun y : ℝ =>
      μHE[finrank ℝ E - 1] (ball (0 : E) R ∩ (‖·‖) ⁻¹' {y})) ⊆ Ico 0 R := by
    intro y hy
    by_contra hy'
    refine hy ?_
    have hfib : ball (0 : E) R ∩ (‖·‖) ⁻¹' {y} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_preimage, mem_singleton_iff,
        mem_empty_iff_false, iff_false, not_and]
      rintro hx rfl
      exact hy' ⟨norm_nonneg x, hx⟩
    simp only [hfib, measure_empty]
  calc ∫⁻ r in Ioo 0 R, μHE[finrank ℝ E - 1] (sphere (0 : E) r)
      = ∫⁻ r in Ioo 0 R, μHE[finrank ℝ E - 1] (ball (0 : E) R ∩ (‖·‖) ⁻¹' {r}) :=
        setLIntegral_congr_fun measurableSet_Ioo fun y hy => by
          rw [ball_inter_norm_preimage_singleton hy.2]
    _ = ∫⁻ r in Ico 0 R, μHE[finrank ℝ E - 1] (ball (0 : E) R ∩ (‖·‖) ⁻¹' {r}) :=
        setLIntegral_congr Ioo_ae_eq_Ico
    _ = ∫⁻ r, μHE[finrank ℝ E - 1] (ball (0 : E) R ∩ (‖·‖) ⁻¹' {r}) :=
        setLIntegral_eq_of_support_subset hsupp
    _ = volume (ball (0 : E) R) := lintegral_euclideanHausdorffMeasure_ball_inter_norm_preimage R

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `n ≥ 2` the derivative of the norm, a linear map `E → ℝ`, is not injective, so its norm
determinant is `0`: a coarea Jacobian without the adjoint would make the formula read `0`. -/
theorem normDet_fderiv_norm (hE : 2 ≤ finrank ℝ E) (x : E) :
    ((fderiv ℝ (‖·‖) x : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ).normDet = 0 := by
  rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, Ne, LinearMap.ker_eq_bot]
  intro h
  have := LinearMap.finrank_le_finrank_of_injective h
  rw [finrank_self] at this
  omega

end TauCeti.Examples.CoareaNorm
