/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import TauCeti.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Energy quantization and energy concentration for `J`-holomorphic curves

Let `J` be a `C²` almost complex structure, written as a matrix-valued function
`J : V → (V →L[ℝ] V)` on an open set `W` of a real inner product space, and let `K ⊆ W` be compact.
Curves are solutions `u : ℂ → V` of the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu`, and their
energy is the real-direction energy `∫ ‖∂ₛu‖²`, as in
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue`. The mean-value inequality there
provides a threshold `δ > 0` such that a curve with energy less than `δ` on a disk of radius `r`
satisfies `π r² ‖∂ₛu(z₀)‖² ≤ 8 ∫_{B_r(z₀)} ‖∂ₛu‖²` at the centre. This file draws the two
consequences of this estimate that control bubbling in Gromov compactness.

* **Energy quantization.** A `J`-holomorphic plane with image in `K` and energy less than `δ` is
  constant: applying the mean-value inequality on disks of every radius `r` about a point bounds
  `‖∂ₛu‖²` there by `8 δ / (π r²)`, which tends to zero. Equivalently, every nonconstant plane
  has energy at least `δ`. A `J`-holomorphic sphere restricts to a plane with the same energy, so
  the same threshold bounds the energy of nonconstant spheres from below.
* **Energy concentration.** If the derivatives of a family of curves on a disk `B_r(z₀)` blow up
  at points converging to `z₀`, then eventually every disk `B_ε(z₀)`, `0 < ε ≤ r`, carries energy
  at least `δ`. Otherwise the mean-value inequality on the disk of radius `ε / 2` about the
  blow-up point would bound the derivative there.

In the bubbling analysis the second statement bounds by `E / δ` the number of points at which a
sequence of curves with energy at most `E` blows up, and the first gives every bubble energy at
least `δ`. Neither the counting argument nor the rescaling that produces bubbles is carried out
here.

## Main results

* `TauCeti.exists_pos_forall_le_integral_norm_fderiv_one_sq_of_ne`: a nonconstant
  `J`-holomorphic plane with image in `K` has energy at least `δ`.
* `TauCeti.exists_pos_forall_eventually_le_setIntegral_norm_fderiv_one_sq_ball`: energy at least
  `δ` concentrates near every point at which the derivatives of a family of `J`-holomorphic
  curves blow up.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.1 (the lower bound for the energy of
  nonconstant spheres), Section 4.2 (bubbling) and Section 4.6 (the points at which the
  derivatives blow up).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V}

/-- **Energy quantization for `J`-holomorphic planes.** Let `J` be `C²` on an open set `W`
containing a compact set `K`, with `J(x)² = -1` on `K`. There is a threshold `δ > 0` such that
every nonconstant `C³` solution `u : ℂ → V` of `∂ₜu = J(u) ∂ₛu` with image in `K` and integrable
energy density has energy `∫ ‖∂ₛu‖² ≥ δ`. -/
theorem exists_pos_forall_le_integral_norm_fderiv_one_sq_of_ne
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄, ContDiff ℝ 3 u →
      (∀ z, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) → range u ⊆ K →
      Integrable (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) → ∀ ⦃z w : ℂ⦄, u z ≠ u w →
      δ ≤ ∫ y, ‖fderiv ℝ u y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun u hu hCR huK hInt z w hzw ↦ ?_⟩
  by_contra! hE
  set E := ∫ y, ‖fderiv ℝ u y 1‖ ^ 2
  have hE0 : 0 ≤ E := integral_nonneg fun _ ↦ sq_nonneg _
  have hDu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  -- The mean-value inequality on the disk of radius `r` about `x` bounds `π r² ‖∂ₛu(x)‖²` by
  -- `8 E`, uniformly in `r`, so `∂ₛu(x) = 0`.
  have hzero : ∀ x, fderiv ℝ u x 1 = 0 := by
    intro x
    have hbound : ∀ r, 0 < r → Real.pi * r ^ 2 * ‖fderiv ℝ u x 1‖ ^ 2 ≤ 8 * E := by
      intro r hr
      have hball : ∫ y in ball x r, ‖fderiv ℝ u y 1‖ ^ 2 ≤ E :=
        setIntegral_le_integral hInt (Eventually.of_forall fun _ ↦ sq_nonneg _)
      exact (hmean hr.le hu.contDiffOn (hDu.clm_apply continuous_const).continuousOn
        (fun y _ ↦ hCR y) (fun y _ ↦ huK (mem_range_self y)) (hball.trans_lt hE)).trans
        (by gcongr)
    by_contra! hx
    have hx2 : 0 < ‖fderiv ℝ u x 1‖ ^ 2 := by positivity
    -- Take `r` with `π r² ‖∂ₛu(x)‖² = 8 E + 1`.
    set r := √((8 * E + 1) / (Real.pi * ‖fderiv ℝ u x 1‖ ^ 2))
    have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
    have hr2 : r ^ 2 = (8 * E + 1) / (Real.pi * ‖fderiv ℝ u x 1‖ ^ 2) :=
      Real.sq_sqrt (by positivity)
    have hr3 : Real.pi * r ^ 2 * ‖fderiv ℝ u x 1‖ ^ 2 = 8 * E + 1 := by
      rw [hr2]
      field_simp
    linarith [hbound r hr]
  -- By the Cauchy--Riemann equation the whole differential vanishes, so `u` is constant.
  have hfderiv : ∀ x, fderiv ℝ u x = 0 := by
    intro x
    refine norm_le_zero_iff.mp (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v ↦ ?_)
    simpa [hzero x, hCR x] using (fderiv ℝ u x).norm_apply_le_norm_one_add_norm_I v
  exact hzw (is_const_of_fderiv_eq_zero (hu.differentiable (by norm_num)) hfderiv z w)

/-- **Energy concentration at blow-up points.** Let `J` be `C²` on an open set `W` containing a
compact set `K`, with `J(x)² = -1` on `K`. There is a threshold `δ > 0` with the following
property. Let `uᵢ` be a family of `C³` solutions of `∂ₜu = J(u) ∂ₛu` on a disk `B_r(z₀)`, with
image in `K` and integrable energy density, and let `zᵢ → z₀` be points at which the differentials
blow up, `‖duᵢ(zᵢ)‖ → ∞`. Then for every `0 < ε ≤ r`, eventually `∫_{B_ε(z₀)} ‖∂ₛuᵢ‖² ≥ δ`. -/
theorem exists_pos_forall_eventually_le_setIntegral_norm_fderiv_one_sq_ball
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃ι : Type*⦄ ⦃l : Filter ι⦄ ⦃u : ι → ℂ → V⦄ ⦃z : ι → ℂ⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄,
      (∀ i, ContDiffOn ℝ 3 (u i) (ball z₀ r)) →
      (∀ i, ∀ y ∈ ball z₀ r, fderiv ℝ (u i) y I = J (u i y) (fderiv ℝ (u i) y 1)) →
      (∀ i, MapsTo (u i) (ball z₀ r) K) →
      (∀ i, IntegrableOn (fun y ↦ ‖fderiv ℝ (u i) y 1‖ ^ 2) (ball z₀ r)) →
      Tendsto z l (𝓝 z₀) → Tendsto (fun i ↦ ‖fderiv ℝ (u i) (z i)‖) l atTop →
      ∀ ε, 0 < ε → ε ≤ r → ∀ᶠ i in l, δ ≤ ∫ y in ball z₀ ε, ‖fderiv ℝ (u i) y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  refine ⟨δ, hδ, fun ι l u z z₀ r hu hCR huK hInt hz hblow ε hε hεr ↦ ?_⟩
  -- A small-energy disk of radius `ε / 2` bounds `‖∂ₛu‖` at its centre by `B`, and then the
  -- Cauchy--Riemann equation bounds `‖du‖` there by `(1 + max a 0) * B`.
  set B := 1 + 8 * δ / (Real.pi * (ε / 2) ^ 2)
  filter_upwards [hz.eventually (ball_mem_nhds z₀ (half_pos hε)),
    hblow.eventually_gt_atTop ((1 + max a 0) * B)] with i hzi hbig
  by_contra! hE
  have hsub : closedBall (z i) (ε / 2) ⊆ ball z₀ ε :=
    closedBall_subset_ball' (by linarith [mem_ball.mp hzi])
  have hsub' : ball (z i) (ε / 2) ⊆ ball z₀ ε := ball_subset_closedBall.trans hsub
  have hεr' : ball z₀ ε ⊆ ball z₀ r := ball_subset_ball hεr
  have hzr : z i ∈ ball z₀ r := hεr' (hsub (mem_closedBall_self (half_pos hε).le))
  have hDu : ContinuousOn (fderiv ℝ (u i)) (ball z₀ r) :=
    ((hu i).fderiv_of_isOpen isOpen_ball (m := 2) (by norm_num)).continuousOn
  have hmono : ∫ y in ball (z i) (ε / 2), ‖fderiv ℝ (u i) y 1‖ ^ 2 ≤
      ∫ y in ball z₀ ε, ‖fderiv ℝ (u i) y 1‖ ^ 2 :=
    setIntegral_mono_set ((hInt i).mono_set hεr')
      (Eventually.of_forall fun _ ↦ sq_nonneg _) (Eventually.of_forall hsub')
  have h := hmean (half_pos hε).le ((hu i).mono (hsub'.trans hεr'))
    ((hDu.mono (hsub.trans hεr')).clm_apply continuousOn_const)
    (fun y hy ↦ hCR i y (hεr' (hsub' hy))) (fun y hy ↦ huK i (hεr' (hsub' hy)))
    (hmono.trans_lt hE)
  have hp : 0 < Real.pi * (ε / 2) ^ 2 := by positivity
  have hsq : ‖fderiv ℝ (u i) (z i) 1‖ ^ 2 ≤ 8 * δ / (Real.pi * (ε / 2) ^ 2) := by
    rw [le_div_iff₀ hp]
    nlinarith
  have hreal : ‖fderiv ℝ (u i) (z i) 1‖ ≤ B := by
    nlinarith [sq_nonneg (‖fderiv ℝ (u i) (z i) 1‖ - 1)]
  have himag : ‖fderiv ℝ (u i) (z i) I‖ ≤ max a 0 * B := by
    rw [hCR i (z i) hzr]
    exact ((J (u i (z i))).le_opNorm _).trans
      (by gcongr; exact (ha _ (huK i hzr)).trans (le_max_left _ _))
  have hop : ‖fderiv ℝ (u i) (z i)‖ ≤ (1 + max a 0) * B := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
    calc ‖fderiv ℝ (u i) (z i) v‖
        ≤ (‖fderiv ℝ (u i) (z i) 1‖ + ‖fderiv ℝ (u i) (z i) I‖) * ‖v‖ :=
          (fderiv ℝ (u i) (z i)).norm_apply_le_norm_one_add_norm_I v
      _ ≤ (B + max a 0 * B) * ‖v‖ := by gcongr
      _ = (1 + max a 0) * B * ‖v‖ := by ring
  linarith

end TauCeti
