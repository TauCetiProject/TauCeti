/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Decay
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Puncture
import TauCeti.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Pointwise power bounds at a puncture

Power decay of the energy of a pseudoholomorphic curve gives a power bound on its full
differential. With taming constant `c > 0` and structure bound `M ≥ 0`, the exponent is
`c / (1 + M)² - 1`, which is strictly greater than `-1`. Consequently the speed along
every radial segment is integrable up to the puncture. This supplies the finite radial
length needed to extend the curve continuously; no value or regularity at the puncture
is assumed here.

The target structure may vary with the image point. A compact image in a neighbourhood
where the structure is `C²` supplies the uniform small-energy mean-value inequality.
The energy-decay input is `SymplecticForm.integral_norm_fderiv_one_sq_ball_le_rpow`;
the punctured-disc mean-value input is
`TauCeti.exists_pos_sq_norm_fderiv_one_le_energy`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c M : ℝ} {W K : Set V}

/-- Bound the energy on all smaller discs by a fixed power, using one reference radius. -/
private theorem exists_energy_power_bound
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ A ≥ 0, ∀ r ∈ Ioo 0 (R / 2),
      (∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2) ≤ A * r ^ (2 * c / (1 + M) ^ 2) := by
  -- The Cauchy--Riemann equation bounds the full energy by the directional energy.
  have hfull : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (ball z₀ R) := by
    rw [IntegrableOn, ← Measure.restrict_congr_set (sdiff_null_ae_eq_self
      (s := ball z₀ R) (measure_singleton z₀))]
    refine ((henergy.mono_set sdiff_subset).const_mul ((1 + max M 0) ^ 2)).mono' ?_ ?_
    · exact ((hu.continuousOn_fderiv_of_isOpen (isOpen_ball.sdiff isClosed_singleton)
        (by norm_num)).norm.pow 2).aestronglyMeasurable
          (measurableSet_ball.diff (measurableSet_singleton _))
    · filter_upwards [ae_restrict_mem
        (measurableSet_ball.diff (measurableSet_singleton z₀))] with z hz
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hI : ‖fderiv ℝ u z I‖ ≤ max M 0 * ‖fderiv ℝ u z 1‖ := by
        rw [hCR z hz]
        exact ((J (u z)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((hJ z hz).trans (le_max_left _ _)) (norm_nonneg _))
      have hop : ‖fderiv ℝ u z‖ ≤ (1 + max M 0) * ‖fderiv ℝ u z 1‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
        exact ((fderiv ℝ u z).norm_apply_le_norm_one_add_norm_I w).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg w))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hop 2
  let b := R / 2
  let α := 2 * c / (1 + M) ^ 2
  let E := ∫ z in ball z₀ b, ‖fderiv ℝ u z 1‖ ^ 2
  refine ⟨E / b ^ α, by dsimp [E, b]; positivity, fun r hr ↦ ?_⟩
  have h := ω.integral_norm_fderiv_one_sq_ball_le_rpow hg hc hu hCR htame hJ hfull
    (b := b) hr.1 hr.2.le (by dsimp [b]; linarith)
  rw [Real.div_rpow hr.1.le (half_pos hR).le] at h
  simpa only [b, α, E, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The differential of a finite-energy pseudoholomorphic curve on a punctured disc has a
power bound with exponent strictly greater than `-1`. Both the radius and the bound are
uniform in the direction of approach. The value of the curve at the puncture is unrestricted.
-/
theorem exists_pos_norm_fderiv_le_rpow
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ ε > 0, ε < R ∧ ∃ C > 0, ∀ z ∈ ball z₀ ε \ {z₀},
      ‖fderiv ℝ u z‖ ≤ C * ‖z - z₀‖ ^ (c / (1 + M) ^ 2 - 1) := by
  have hmem : circleMap z₀ (R / 2) 0 ∈ ball z₀ R \ {z₀} := by
    constructor
    · simp only [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos (half_pos hR)]
      linarith
    · exact sub_ne_zero.mp (norm_pos_iff.mp (by
        simpa only [circleMap_sub_center, norm_circleMap_zero,
          abs_of_pos (half_pos hR)] using half_pos hR))
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound _ hmem)
  -- Normalize the energy power bound, then choose a radius below the mean-value threshold.
  let β := c / (1 + M) ^ 2
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨A, hA, hpower⟩ := exists_energy_power_bound hg hc hR
    (hu.of_le (by norm_num)) hCR htame hbound henergy
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_sq_norm_fderiv_one_le_energy hW hJ hK hKW hJsq hu hCR huK henergy
  have hlim : Tendsto (fun r : ℝ ↦ A * (2 * r) ^ (2 * β)) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow (by positivity : 2 * β ≠ 0)] using
      ((Real.continuous_rpow_const (by positivity : 0 ≤ 2 * β)).comp
        (continuous_const.mul continuous_id)).const_mul A |>.tendsto 0
  obtain ⟨η, hη, hηbound⟩ := Metric.eventually_nhds_iff.mp
    (hlim.eventually (gt_mem_nhds hδ))
  let ε := min η (R / 4)
  have hε : 0 < ε := lt_min hη (by positivity)
  have hεR : ε < R := (min_le_right _ _).trans_lt (by linarith)
  let B := 32 * A * (2 : ℝ) ^ (2 * β) / Real.pi
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C := (1 + M) * (Real.sqrt B + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε, hε, hεR, C, hC, fun z hz ↦ ?_⟩
  let d := ‖z - z₀‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hz.2)
  have hdε : d < ε := by simpa only [mem_ball, dist_eq_norm] using hz.1
  have hzR : z ∈ ball z₀ R \ {z₀} := ⟨ball_subset_ball hεR.le hz.1, hz.2⟩
  have hdR : d < R / 4 := hdε.trans_le (min_le_right _ _)
  have hsmall : 2 * d ∈ Ioo 0 (R / 2) := by
    constructor
    · positivity
    · have := hdε.trans_le (min_le_right η (R / 4)); linarith
  have hpow := hpower (2 * d) hsmall
  have hα : 2 * c / (1 + M) ^ 2 = 2 * β := by dsimp [β]; ring
  rw [hα] at hpow
  have hsmallE : A * (2 * d) ^ (2 * β) < δ := hηbound (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hd]
    exact hdε.trans_le (min_le_left _ _))
  -- The estimate on a disc avoiding the puncture converts energy decay into derivative decay.
  have hpoint := hmean z
    ⟨by simpa only [mem_ball, dist_eq_norm] using
      hdR.trans_le (by linarith : R / 4 ≤ R / 2), hz.2⟩
    (hpow.trans_lt hsmallE)
  have hsquare : d ^ 2 * ‖fderiv ℝ u z 1‖ ^ 2 ≤ B * d ^ (2 * β) := by
    have h := hpoint.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    rw [Real.mul_rpow (by positivity) hd.le] at h
    calc
      _ ≤ 32 / Real.pi * (A * (2 ^ (2 * β) * d ^ (2 * β))) := h
      _ = B * d ^ (2 * β) := by dsimp [B]; ring
  have hreal : ‖fderiv ℝ u z 1‖ ≤ Real.sqrt B * d ^ (β - 1) := by
    have hsq : (d * ‖fderiv ℝ u z 1‖) ^ 2 ≤ (Real.sqrt B * d ^ β) ^ 2 := by
      have hp : d ^ (2 * β) = (d ^ β) ^ 2 := by
        simpa only [Nat.cast_ofNat, mul_comm] using Real.rpow_mul_natCast hd.le β 2
      rw [hp] at hsquare
      simpa only [mul_pow, Real.sq_sqrt hB] using hsquare
    have h := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    rw [Real.rpow_sub_one hd.ne', ← mul_div_assoc, le_div_iff₀ hd]
    nlinarith
  -- The Cauchy--Riemann equation controls the full differential by its real-direction part.
  have hI : ‖fderiv ℝ u z I‖ ≤ M * ‖fderiv ℝ u z 1‖ := by
    rw [hCR z hzR]
    exact ((J (u z)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound z hzR) (norm_nonneg _))
  have hop : ‖fderiv ℝ u z‖ ≤ (1 + M) * ‖fderiv ℝ u z 1‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    exact ((fderiv ℝ u z).norm_apply_le_norm_one_add_norm_I w).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg w))
  calc
    ‖fderiv ℝ u z‖ ≤ (1 + M) * (Real.sqrt B * d ^ (β - 1)) := by
      exact hop.trans (mul_le_mul_of_nonneg_left hreal (by positivity))
    _ ≤ C * d ^ (β - 1) := by dsimp [C]; nlinarith [Real.rpow_pos_of_pos hd (β - 1)]

/-- A finite-energy pseudoholomorphic curve has integrable velocity along every radial
segment sufficiently close to the puncture. The radius is uniform over all unit directions;
no continuous extension at the missing endpoint is assumed. -/
theorem exists_pos_integrableOn_deriv_radial
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ ε > 0, ε < R ∧ ∀ v : ℂ, ‖v‖ = 1 →
      IntegrableOn (deriv (fun t : ℝ ↦ u (z₀ + t • v))) (Ioo 0 ε) := by
  obtain ⟨ε, hε, hεR, C, _, hC⟩ := ω.exists_pos_norm_fderiv_le_rpow
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame hbound henergy
  refine ⟨ε, hε, hεR, fun v hv ↦ ?_⟩
  have hnorm (t : ℝ) (ht : 0 < t) : ‖z₀ + t • v - z₀‖ = t := by
    simp [hv, Real.norm_of_nonneg ht.le]
  have hmem (t : ℝ) (ht : t ∈ Ioo 0 ε) : z₀ + t • v ∈ ball z₀ ε \ {z₀} := by
    constructor
    · simpa only [mem_ball, dist_eq_norm, hnorm t ht.1] using ht.2
    · exact sub_ne_zero.mp (norm_pos_iff.mp (by rw [hnorm t ht.1]; exact ht.1))
  have hmemR (t : ℝ) (ht : t ∈ Ioo 0 ε) : z₀ + t • v ∈ ball z₀ R \ {z₀} :=
    ⟨ball_subset_ball hεR.le (hmem t ht).1, (hmem t ht).2⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hbound _ (hmemR (ε / 2) ⟨half_pos hε, by linarith⟩))
  have heq (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      deriv (fun t : ℝ ↦ u (z₀ + t • v)) t = fderiv ℝ u (z₀ + t • v) v := by
    have hd := (hu.contDiffAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds
      (hmemR t ht))).differentiableAt (by norm_num)
    simpa only [Function.comp_def, Pi.add_apply, zero_add, one_smul, id_eq] using
      (hd.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t z₀).add ((hasDerivAt_id t).smul_const v))).deriv
  have hcont : ContinuousOn (fun t : ℝ ↦ fderiv ℝ u (z₀ + t • v) v) (Ioo 0 ε) :=
    ((hu.continuousOn_fderiv_of_isOpen (isOpen_ball.sdiff isClosed_singleton)
      (by norm_num)).comp
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
        hmemR).clm_apply continuousOn_const
  have hmeas : AEStronglyMeasurable (deriv (fun t : ℝ ↦ u (z₀ + t • v)))
      (volume.restrict (Ioo 0 ε)) :=
    (hcont.congr (fun t ht ↦ heq t ht)).aestronglyMeasurable measurableSet_Ioo
  have hpow : IntegrableOn (fun t : ℝ ↦ C * t ^ (c / (1 + M) ^ 2 - 1)) (Ioo 0 ε) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr (by
      have : 0 < c / (1 + M) ^ 2 := by positivity
      linarith)).const_mul C
  refine hpow.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [heq t ht]
  calc
    ‖fderiv ℝ u (z₀ + t • v) v‖ ≤ ‖fderiv ℝ u (z₀ + t • v)‖ := by
      simpa only [hv, mul_one] using (fderiv ℝ u (z₀ + t • v)).le_opNorm v
    _ ≤ C * t ^ (c / (1 + M) ^ 2 - 1) := by
      simpa only [hnorm t ht.1] using hC _ (hmem t ht)

end TauCeti.SymplecticForm
