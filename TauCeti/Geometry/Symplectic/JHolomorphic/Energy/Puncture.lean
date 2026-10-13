/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Calculus.FDeriv.CircleMap

/-!
# Finite-energy `J`-holomorphic curves near a puncture

Let `u` be a `J`-holomorphic curve on a punctured disk `B_R(z₀) \ {z₀}`, that is, a solution of
the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` there, with image in a compact set `K` on a
neighbourhood of which the almost complex structure `J` is `C²`. If `u` has finite energy,
`∫_{B_R(z₀)} ‖∂ₛu‖² < ∞`, then its derivative blows up strictly slower than `1 / |z - z₀|`:

`|z - z₀| ‖du(z)‖ → 0` as `z → z₀`.

Indeed, the disk of radius `|z - z₀| / 2` about `z` misses the puncture and lies in the disk of
radius `2 |z - z₀|` about `z₀`, whose energy tends to zero with `|z - z₀|`. Once that energy is
below the threshold of the mean-value inequality
(`TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`),
it gives `π |z - z₀|² ‖∂ₛu(z)‖² ≤ 32 ∫_{B_{2|z - z₀|}(z₀)} ‖∂ₛu‖²`, and the Cauchy--Riemann
equation bounds the full derivative by `∂ₛu`.

Consequently the loops `θ ↦ u(z₀ + ρ e^{iθ})` have derivative `o(1)`, so the images of the
circles `|z - z₀| = ρ` shrink: their diameter tends to `0` as `ρ → 0`
(`TauCeti.tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto`). This is the first step of
the removal of singularities for finite-energy `J`-holomorphic curves: combined with the
isoperimetric inequality (`TauCeti.SymplecticForm.abs_integral_apply_le`) it yields the decay of
the energy near the puncture, and then the extension of `u` across it.

## Main results

* `TauCeti.tendsto_norm_sub_mul_norm_fderiv_one_nhdsNE`: `|z - z₀| ‖∂ₛu(z)‖ → 0` as `z → z₀`.
* `TauCeti.tendsto_norm_sub_mul_norm_fderiv_nhdsNE`: the same for the full derivative `du(z)`.
* `TauCeti.tendsto_diam_image_sphere_nhdsGT_zero`: the diameter of the image of the circle of
  radius `ρ` about the puncture tends to `0` as `ρ → 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.5 (removal of singularities).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V} {u : ℂ → V} {z₀ : ℂ} {R : ℝ}

/-- **Derivative decay at a puncture.** Let `J` be `C²` on an open set `W` containing a compact
set `K`, with `J(x)² = -1` on `K`. A solution `u` of `∂ₜu = J(u) ∂ₛu` that is `C³` on the punctured
disk `B_R(z₀) \ {z₀}`, maps it into `K` and has finite energy `∫_{B_R(z₀)} ‖∂ₛu‖² < ∞` satisfies
`|z - z₀| ‖∂ₛu(z)‖ → 0` as `z → z₀`. -/
theorem tendsto_norm_sub_mul_norm_fderiv_one_nhdsNE
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hR : 0 < R)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (hE : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderiv ℝ u z 1‖) (𝓝[≠] z₀) (𝓝 0) := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  have hDu : ContinuousOn (fun y ↦ fderiv ℝ u y 1) (ball z₀ R \ {z₀}) :=
    (hu.continuousOn_fderiv_of_isOpen (isOpen_ball.sdiff isClosed_singleton)
      (by norm_num)).clm_apply continuousOn_const
  -- The energy `ε ρ` of `u` in the disk of radius `ρ` about the puncture tends to zero with `ρ`.
  set ε : ℝ → ℝ := fun ρ ↦
    ∫ y in ball z₀ ρ, ‖fderiv ℝ u y 1‖ ^ 2 ∂(volume.restrict (ball z₀ R)) with hεdef
  have hε : Tendsto ε (𝓝 0) (𝓝 0) := by
    refine hE.tendsto_setIntegral_nhds_zero ?_
    have hvol : Tendsto (fun ρ : ℝ ↦ volume (ball z₀ ρ)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun ρ : ℝ ↦ ENNReal.ofReal ρ ^ 2 * (NNReal.pi : ℝ≥0∞) :=
        (ENNReal.continuous_mul_const ENNReal.coe_ne_top).comp
          ((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal)
      simpa using hc.tendsto 0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol
      (fun _ ↦ zero_le) fun _ ↦ Measure.restrict_apply_le _ _
  have hεz : Tendsto (fun z ↦ ε (2 * ‖z - z₀‖)) (𝓝[≠] z₀) (𝓝 0) :=
    hε.comp ((((continuous_id.sub continuous_const).norm.const_mul 2).tendsto' z₀ 0
      (by simp)).mono_left nhdsWithin_le_nhds)
  -- The mean-value inequality on the disk of radius `|z - z₀| / 2` about `z`.
  have hbound : ∀ᶠ z in 𝓝[≠] z₀,
      (‖z - z₀‖ * ‖fderiv ℝ u z 1‖) ^ 2 ≤ 32 / π * ε (2 * ‖z - z₀‖) := by
    have hnear : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ (R / 2) :=
      nhdsWithin_le_nhds (ball_mem_nhds z₀ (half_pos hR))
    filter_upwards [self_mem_nhdsWithin, hεz.eventually (gt_mem_nhds hδ), hnear]
      with z hz hzε hzR
    rw [mem_ball, dist_eq_norm] at hzR
    have hρ : 0 < ‖z - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    -- The closed disk of radius `|z - z₀| / 2` about `z` lies in the punctured disk.
    have hsubc : closedBall z (‖z - z₀‖ / 2) ⊆ ball z₀ R \ {z₀} := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      refine ⟨?_, fun hy₀ ↦ ?_⟩
      · rw [mem_ball, dist_eq_norm]
        linarith [norm_sub_le_norm_sub_add_norm_sub y z z₀]
      · rw [mem_singleton_iff.1 hy₀, norm_sub_rev] at hy
        linarith
    have hsub : ball z (‖z - z₀‖ / 2) ⊆ ball z₀ R \ {z₀} := ball_subset_closedBall.trans hsubc
    -- Its energy is at most the energy of the disk of radius `2 |z - z₀|` about `z₀`.
    have hle : ∫ y in ball z (‖z - z₀‖ / 2), ‖fderiv ℝ u y 1‖ ^ 2 ≤ ε (2 * ‖z - z₀‖) := by
      simp only [hεdef]
      rw [Measure.restrict_restrict measurableSet_ball]
      refine setIntegral_mono_set (hE.mono_set inter_subset_right)
        (Eventually.of_forall fun _ ↦ sq_nonneg _)
        (Eventually.of_forall fun y (hy : y ∈ ball z (‖z - z₀‖ / 2)) ↦ ?_)
      refine ⟨?_, (hsub hy).1⟩
      rw [mem_ball, dist_eq_norm] at hy ⊢
      linarith [norm_sub_le_norm_sub_add_norm_sub y z z₀]
    have h := hmean (by positivity) (hu.mono hsub) (hDu.mono hsubc)
      (fun y hy ↦ hCR y (hsub hy)) (fun y hy ↦ huK (hsub hy)) (hle.trans_lt hzε)
    rw [mul_pow, div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
    nlinarith
  have hlim : Tendsto (fun z ↦ √(32 / π * ε (2 * ‖z - z₀‖))) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using (hεz.const_mul (32 / π)).sqrt
  refine squeeze_zero' (Eventually.of_forall fun z ↦ by positivity) ?_ hlim
  filter_upwards [hbound] with z hz
  exact (le_abs_self _).trans (Real.abs_le_sqrt hz)

/-- **Derivative decay at a puncture, full derivative.** Under the hypotheses of
`TauCeti.tendsto_norm_sub_mul_norm_fderiv_one_nhdsNE`, the full derivative of a finite-energy
solution of `∂ₜu = J(u) ∂ₛu` on the punctured disk `B_R(z₀) \ {z₀}` with image in `K` satisfies
`|z - z₀| ‖du(z)‖ → 0` as `z → z₀`. -/
theorem tendsto_norm_sub_mul_norm_fderiv_nhdsNE
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hR : 0 < R)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (hE : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderiv ℝ u z‖) (𝓝[≠] z₀) (𝓝 0) := by
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  obtain ⟨C, -, hC⟩ := Complex.basisOneI.exists_opNorm_le (F := V)
  have h := (tendsto_norm_sub_mul_norm_fderiv_one_nhdsNE hW hJ hK hKW hJsq hR hu hCR huK
    hE).const_mul (C * (1 + max a 0))
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun z ↦ by positivity) ?_ h
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hR)] with z hz hzR
  have hz' : z ∈ ball z₀ R \ {z₀} := ⟨hzR, hz⟩
  -- The Cauchy--Riemann equation bounds `‖∂ₜu‖ = ‖J(u) ∂ₛu‖` by a multiple of `‖∂ₛu‖`.
  have hI : ‖fderiv ℝ u z I‖ ≤ max a 0 * ‖fderiv ℝ u z 1‖ := by
    rw [hCR z hz']
    exact ((J (u z)).le_opNorm _).trans
      (by gcongr; exact (ha _ (huK hz')).trans (le_max_left _ _))
  have hop : ‖fderiv ℝ u z‖ ≤ C * ((1 + max a 0) * ‖fderiv ℝ u z 1‖) := by
    refine hC (by positivity) fun i ↦ ?_
    have h1 : 0 ≤ max a 0 * ‖fderiv ℝ u z 1‖ := by positivity
    fin_cases i <;> simp [Complex.coe_basisOneI] <;> linarith [norm_nonneg (fderiv ℝ u z 1)]
  calc ‖z - z₀‖ * ‖fderiv ℝ u z‖ ≤ ‖z - z₀‖ * (C * ((1 + max a 0) * ‖fderiv ℝ u z 1‖)) := by
        gcongr
    _ = C * (1 + max a 0) * (‖z - z₀‖ * ‖fderiv ℝ u z 1‖) := by ring

/-- **Circles about a puncture have shrinking images.** Under the hypotheses of
`TauCeti.tendsto_norm_sub_mul_norm_fderiv_one_nhdsNE`, the image under a finite-energy solution
`u` of `∂ₜu = J(u) ∂ₛu` of the circle of radius `ρ` about the puncture has diameter tending to
`0` as `ρ → 0`. -/
theorem tendsto_diam_image_sphere_nhdsGT_zero
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hR : 0 < R)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (hE : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    Tendsto (fun ρ ↦ diam (u '' sphere z₀ ρ)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto ?_
    (tendsto_norm_sub_mul_norm_fderiv_nhdsNE hW hJ hK hKW hJsq hR hu hCR huK hE)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hR)] with z hz hzR
  exact (hu.contDiffAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hzR, hz⟩)).differentiableAt
    (by norm_num)

end TauCeti
