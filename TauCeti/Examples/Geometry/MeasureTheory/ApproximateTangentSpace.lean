/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.ApproximateTangentSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Checks for approximate tangent spaces of measures

Examples in the plane `ℝ² = EuclideanSpace ℝ (Fin 2)` for `k = 1` of the approximate tangent spaces
of measures (`MeasureTheory.Measure.HasApproxTangentSpace`), the Checks of Varifolds §2.1.

* *Multiplicity.* `H¹⌞L`, for the `x`-axis `L`, has approximate tangent space `L` with
  multiplicity `1` at every point of `L`, and `2 H¹⌞L` has multiplicity `2`
  (`hasApproxTangentSpace_xAxis`, `hasApproxTangentSpace_two_smul_xAxis`). The normalisation
  matters: `H¹⌞L (x + λ B₁(0)) = 2λ` (`euclideanHausdorffMeasure_xAxis_ball`), so a
  normalisation by `λ⁰` would give blow-up masses `2λ → 0` and one by `λ⁻²` masses `2/λ → ∞`
  (`tendsto_euclideanHausdorffMeasure_xAxis_ball`,
  `tendsto_inv_sq_mul_euclideanHausdorffMeasure_xAxis_ball`).
* *Lebesgue measure.* Lebesgue measure on `ℝ²` has no approximate tangent line at any point
  (`not_hasApproxTangentSpace_volume`): the blow-up masses `λ⁻¹ π λ² = π λ` of the unit disc tend
  to `0`.
* *A point mass.* `δ₀` has no approximate tangent line at `0`
  (`not_hasApproxTangentSpace_dirac`): its blow-up masses `λ⁻¹` tend to `∞`.
* *Chart comparison.* For `φ(y) = 2y`, `φ_*(H¹⌞L) = ½ H¹⌞L` (`map_two_smul_xAxis`), which has
  approximate tangent space `L` with multiplicity `1 / J_L(2 · id) = ½`
  (`hasApproxTangentSpace_map_two_smul_xAxis`).
-/

open MeasureTheory Measure Set Metric Module Filter Topology
open scoped ENNReal NNReal Pointwise

public noncomputable section

namespace TauCeti.Examples.ApproxTangentSpace

/-- The `x`-axis `ℝ e₀` of the plane. -/
def xAxis : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ℝ ∙ EuclideanSpace.single 0 1

/-- The `x`-axis is a line. -/
theorem finrank_xAxis : finrank ℝ xAxis = 1 :=
  finrank_span_singleton (by simp)

/-- `H¹⌞L` has approximate tangent space `L` with multiplicity `1` at every point of the
`x`-axis `L`. -/
theorem hasApproxTangentSpace_xAxis {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ xAxis) :
    (μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2)))).HasApproxTangentSpace x xAxis 1 := by
  have h := xAxis.toAffineSubspace.hasApproxTangentSpace_smul_euclideanHausdorffMeasure_restrict
    (θ := 1) (by simpa using hx) one_ne_zero
  rw [Submodule.toAffineSubspace_direction, finrank_xAxis] at h
  simpa using h

/-- `2 H¹⌞L` has approximate tangent space `L` with multiplicity `2` at every point of the
`x`-axis `L`. -/
theorem hasApproxTangentSpace_two_smul_xAxis {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ xAxis) :
    ((2 : ℝ≥0) • μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2)))).HasApproxTangentSpace
      x xAxis 2 := by
  have h := xAxis.toAffineSubspace.hasApproxTangentSpace_smul_euclideanHausdorffMeasure_restrict
    (θ := 2) (by simpa using hx) two_ne_zero
  rw [Submodule.toAffineSubspace_direction, finrank_xAxis] at h
  simpa using h

/-- The unit ball of `ℝ¹` has length `2`. -/
theorem volume_ball_fin_one (r : ℝ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 1)) r) = ENNReal.ofReal (2 * r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.mpr hr, measure_empty, ENNReal.ofReal_of_nonpos (by linarith)]
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp), finrank_euclideanSpace_fin,
    ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  norm_num [mul_comm]

/-- The `x`-axis meets a disc of radius `λ` about one of its points in a segment of length
`2λ`. -/
theorem euclideanHausdorffMeasure_xAxis_ball {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ xAxis)
    (r : ℝ) :
    μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2))) (ball x r) =
      ENNReal.ofReal (2 * r) := by
  have h := Submodule.euclideanHausdorffMeasure_restrict_apply_ball hx r
  rw [finrank_xAxis] at h
  rw [h, volume_ball_fin_one]

/-- Without normalisation the masses `2λ` of the discs of radius `λ` tend to `0`. -/
theorem tendsto_euclideanHausdorffMeasure_xAxis_ball {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ xAxis) :
    Tendsto (fun r ↦ μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2))) (ball x r))
      (𝓝[>] 0) (𝓝 0) := by
  simp_rw [euclideanHausdorffMeasure_xAxis_ball hx]
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)
    |>.mono_left nhdsWithin_le_nhds)

/-- Normalised by `λ⁻²`, the masses `2/λ` of the discs of radius `λ` tend to `∞`. -/
theorem tendsto_inv_sq_mul_euclideanHausdorffMeasure_xAxis_ball {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ xAxis) :
    Tendsto (fun r ↦ (ENNReal.ofReal r)⁻¹ ^ 2 *
      μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2))) (ball x r)) (𝓝[>] 0) (𝓝 ∞) := by
  have h0 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r) (𝓝[>] 0) (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hinv : Tendsto (fun r : ℝ ↦ (ENNReal.ofReal r)⁻¹) (𝓝[>] 0) (𝓝 ∞) := by
    simpa using tendsto_inv_iff.2 h0
  have h2 := ENNReal.Tendsto.const_mul (a := 2) hinv (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top two_ne_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have ha : ENNReal.ofReal r ≠ 0 := by simpa using hr
  rw [euclideanHausdorffMeasure_xAxis_ball hx, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    sq, show ∀ a : ℝ≥0∞, a⁻¹ * a⁻¹ * (2 * a) = 2 * a⁻¹ * (a⁻¹ * a) from fun a ↦ by ring,
    ENNReal.inv_mul_cancel ha ENNReal.ofReal_ne_top, mul_one]

/-- **Lebesgue measure on `ℝ²` has no approximate tangent line anywhere**: the masses `π λ²` of
the discs of radius `λ`, divided by the lengths `2λ` of the segments, tend to `0`, while along an
approximate tangent line they would tend to the positive multiplicity. -/
theorem not_hasApproxTangentSpace_volume (x : EuclideanSpace ℝ (Fin 2))
    {T : Submodule ℝ (EuclideanSpace ℝ (Fin 2))} (hT : finrank ℝ T = 1) (θ : ℝ≥0) :
    ¬ (volume : Measure (EuclideanSpace ℝ (Fin 2))).HasApproxTangentSpace x T θ := by
  intro h
  have hlim := h.tendsto_measure_ball_div
  rw [hT] at hlim
  have h0 : Tendsto (fun r : ℝ ↦ volume (ball x r) /
      volume (ball (0 : EuclideanSpace ℝ (Fin 1)) r)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (Real.pi * r / 2)) (𝓝[>] 0) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal ((by fun_prop : Continuous fun r : ℝ ↦ Real.pi * r / 2)
        |>.tendsto' 0 0 (by simp) |>.mono_left nhdsWithin_le_nhds)
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [EuclideanSpace.volume_ball_fin_two, volume_ball_fin_one, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  exact h.ne_zero (by exact_mod_cast tendsto_nhds_unique hlim h0)

/-- **A point mass has no approximate tangent line**: the mass `1` of the discs of radius `λ`
about `0`, divided by the lengths `2λ`, tends to `∞`. -/
theorem not_hasApproxTangentSpace_dirac {T : Submodule ℝ (EuclideanSpace ℝ (Fin 2))}
    (hT : finrank ℝ T = 1) (θ : ℝ≥0) :
    ¬ (Measure.dirac (0 : EuclideanSpace ℝ (Fin 2))).HasApproxTangentSpace 0 T θ := by
  intro h
  have hlim := h.tendsto_measure_ball_div
  rw [hT] at hlim
  have hinf : Tendsto (fun r : ℝ ↦ Measure.dirac (0 : EuclideanSpace ℝ (Fin 2)) (ball 0 r) /
      volume (ball (0 : EuclideanSpace ℝ (Fin 1)) r)) (𝓝[>] 0) (𝓝 ∞) := by
    have h0 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (2 * r)) (𝓝[>] 0) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)
        |>.mono_left nhdsWithin_le_nhds)
    have hinv : Tendsto (fun r : ℝ ↦ (ENNReal.ofReal (2 * r))⁻¹) (𝓝[>] 0) (𝓝 ∞) := by
      simpa using tendsto_inv_iff.2 h0
    refine hinv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [volume_ball_fin_one, dirac_apply_of_mem (mem_ball_self hr), one_div]
  exact ENNReal.coe_ne_top (tendsto_nhds_unique hlim hinf)

/-- **Chart comparison**: the push-forward of `H¹⌞L` under `y ↦ 2y` is `½ H¹⌞L`, since the
homothety maps `L` onto itself and multiplies lengths by `2`. -/
theorem map_two_smul_xAxis :
    (μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2)))).map ((2 : ℝ) • ·) =
      (2⁻¹ : ℝ≥0) • μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2))) := by
  ext s hs
  have hpre : ((2 : ℝ) • ·) ⁻¹' s = (2⁻¹ : ℝ) • s := by
    ext v
    rw [mem_preimage, mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero two_ne_zero), inv_inv]
  have hL : (2⁻¹ : ℝ) • (xAxis : Set (EuclideanSpace ℝ (Fin 2))) = xAxis := by
    ext v
    refine ⟨fun ⟨w, hw, hv⟩ ↦ hv ▸ xAxis.smul_mem _ hw, fun hv ↦ ⟨(2 : ℝ) • v,
      xAxis.smul_mem _ hv, by simp [smul_smul]⟩⟩
  rw [map_apply (continuous_const_smul _).measurable hs, Measure.restrict_apply
    ((continuous_const_smul _).measurable hs), hpre, smul_apply, Measure.restrict_apply hs, ← hL,
    ← smul_set_inter₀ (inv_ne_zero two_ne_zero), hL, euclideanHausdorffMeasure_smul₀ 1
    (inv_ne_zero two_ne_zero)]
  simp [ENNReal.smul_def]

/-- The push-forward of `H¹⌞L` under `y ↦ 2y` has approximate tangent space `L` with multiplicity
`1 / J_L(2 · id) = ½` at every point of `L`. -/
theorem hasApproxTangentSpace_map_two_smul_xAxis {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ xAxis) :
    ((μHE[1].restrict (xAxis : Set (EuclideanSpace ℝ (Fin 2)))).map ((2 : ℝ) • ·))
      |>.HasApproxTangentSpace x xAxis 2⁻¹ := by
  rw [map_two_smul_xAxis]
  have h := xAxis.toAffineSubspace.hasApproxTangentSpace_smul_euclideanHausdorffMeasure_restrict
    (θ := 2⁻¹) (by simpa using hx) (inv_ne_zero two_ne_zero)
  rw [Submodule.toAffineSubspace_direction, finrank_xAxis] at h
  simpa using h

end TauCeti.Examples.ApproxTangentSpace
