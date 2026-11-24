/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Boundary.MeanValue
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Analysis.Calculus.FDeriv.CircleMap
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.RCLike.OperatorNorm

/-!
# Finite-energy `J`-holomorphic half-discs near a boundary puncture

Let `x₀` be a point of the real axis and let `u` be a `J`-holomorphic curve on the punctured
half-disc `{0 ≤ im z} ∩ B_R(x₀) \ {x₀}`, regular up to its straight edge and mapping the edge
into a closed subspace `L`. Derivatives are taken within the closed upper half-plane. Suppose that
`u` has image in a compact set `K`, on a neighbourhood `W` of which `J` is `C²` with `J² = -1`, and
that `J(p)` maps `L` into its orthogonal complement for `p ∈ L ∩ W`, so that the boundary
mean-value inequality applies. If `u` has finite energy, `∫_{{0 ≤ im z} ∩ B_R(x₀)} ‖∂ₛu‖² < ∞`,
then its derivative blows up strictly slower than `1 / |z - x₀|`:

`|z - x₀| ‖du(z)‖ → 0` as `z → x₀` in the closed upper half-plane.

This is the boundary counterpart of `TauCeti.tendsto_norm_sub_mul_norm_fderiv_one_nhdsNE`. At a
point `z` at distance `d` from the puncture the energy on `{0 ≤ im y} ∩ B_{2d}(x₀)` controls
`d² ‖∂ₛu(z)‖²`, once it is below the thresholds of the two mean-value inequalities:

* if `z` lies at height at least `d / 4` above the axis, the interior mean-value inequality
  (`TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`)
  applies on the disc of radius `d / 8` about `z`, which lies above the axis;
* otherwise the foot `x` of `z` on the axis is at distance more than `3d / 4` from `x₀`, and the
  boundary mean-value inequality on the half-disc of radius `3d / 4` about `x`
  (`exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball`)
  bounds `∂ₛu` at `z`, whose disc of radius `d / 2` it contains.

Both discs avoid the puncture and lie in `B_{2d}(x₀)`, whose energy tends to zero with `d`.

Consequently the arcs `θ ↦ u(x₀ + ρ e^{iθ})`, `0 ≤ θ ≤ π`, have derivative `o(1)`, so the images
of the half-circles `{0 ≤ im z, |z - x₀| = ρ}` shrink: their diameter tends to `0` as `ρ → 0`
(`TauCeti.tendsto_diam_image_inter_sphere_nhdsGT_zero`). This is the first step of the removal
of boundary punctures of finite-energy holomorphic curves with totally real boundary conditions:
it puts the half-circles about the puncture into small neighbourhoods of `L`, where a primitive of
the symplectic form vanishing on `L` turns the isoperimetric argument into decay of the energy.

## Main results

* `TauCeti.exists_pos_sq_norm_fderivWithin_one_le_energy`: small energy near the puncture bounds
  `|z - x₀|² ‖∂ₛu(z)‖²`.
* `TauCeti.tendsto_norm_sub_mul_norm_fderivWithin_one_nhdsWithin`: `|z - x₀| ‖∂ₛu(z)‖ → 0` as
  `z → x₀` in the closed upper half-plane.
* `TauCeti.tendsto_norm_sub_mul_norm_fderivWithin_nhdsWithin`: the same for the full derivative
  `du(z)`.
* `TauCeti.tendsto_diam_image_inter_sphere_nhdsGT_zero`: the diameter of the image of the
  half-circle of radius `ρ` about the puncture tends to `0` as `ρ → 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.3 (the boundary mean-value inequality) and
  4.5 (removal of singularities, including boundary punctures with totally real boundary
  conditions).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V} {L : Submodule ℝ V} {u : ℂ → V} {x₀ : ℂ} {R : ℝ}

/-- Near a boundary puncture, at points at height at least a quarter of their distance `d` to the
puncture, sufficiently small energy on the half-disc of radius `2d` controls the squared
directional derivative: the interior mean-value inequality applies on the disc of radius `d / 8`,
which lies above the real axis. -/
private theorem exists_pos_sq_norm_fderivWithin_one_le_energy_of_le_im
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ δ > 0, ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ (R / 2) \ {x₀}), ‖z - x₀‖ / 4 ≤ z.im →
      (∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ (2 * ‖z - x₀‖),
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2) < δ →
      ‖z - x₀‖ ^ 2 * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2 ≤
        512 / π * ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ (2 * ‖z - x₀‖),
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  obtain ⟨δ, hδ, hint⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  refine ⟨δ, hδ, fun z hz hfar hE ↦ ?_⟩
  set d := ‖z - x₀‖
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hz.2.2)
  have hdR : d < R / 2 := by simpa [mem_ball, dist_eq_norm] using hz.2.1
  have hzx₀ : dist z x₀ = d := dist_eq_norm z x₀
  -- The closed disc of radius `d / 8` about `z` lies above the axis and in `B_R(x₀) \ {x₀}`.
  set U := {y : ℂ | 0 < y.im} ∩ (ball x₀ R \ {x₀})
  have hsub : closedBall z (d / 8) ⊆ U := fun y hy ↦ by
    have hyz : dist y z ≤ d / 8 := mem_closedBall.1 hy
    have him : |z.im - y.im| ≤ dist z y := by
      simpa [dist_eq_norm] using abs_im_le_norm (z - y)
    rw [dist_comm] at him
    refine ⟨mem_ofPred.2 (by linarith [abs_le.1 him]), ?_, fun hyx₀ ↦ ?_⟩
    · rw [mem_ball]
      linarith [dist_triangle y z x₀]
    · rw [mem_singleton_iff.1 hyx₀, dist_comm, hzx₀] at hyz
      linarith
  have hball : ball z (d / 8) ⊆ U := ball_subset_closedBall.trans hsub
  have hUH : U ⊆ H ∩ (ball x₀ R \ {x₀}) := fun y hy ↦
    ⟨mem_ofPred.2 (mem_ofPred.1 hy.1).le, hy.2⟩
  -- Above the axis the derivatives within the half-plane are ordinary derivatives.
  have hfdU : ∀ y ∈ U, fderivWithin ℝ u H y = fderiv ℝ u y := fun y hy ↦
    fderivWithin_of_mem_nhds (mem_of_superset
      ((isOpen_lt continuous_const continuous_im).mem_nhds hy.1) fun w hw ↦ le_of_lt hw)
  have huU : ContDiffOn ℝ 3 u U := hu.mono hUH
  have hballE : ∫ y in ball z (d / 8), ‖fderiv ℝ u y 1‖ ^ 2 ≤
      ∫ y in H ∩ ball x₀ (2 * d), ‖fderivWithin ℝ u H y 1‖ ^ 2 := by
    have hcongr : ∫ y in ball z (d / 8), ‖fderiv ℝ u y 1‖ ^ 2 =
        ∫ y in ball z (d / 8), ‖fderivWithin ℝ u H y 1‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_ball fun y hy ↦ by simp only [hfdU y (hball hy)]
    rw [hcongr]
    refine setIntegral_mono_set
      (henergy.mono_set (inter_subset_inter_right _ (ball_subset_ball (by linarith))))
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall fun y hy ↦ ⟨(hUH (hball hy)).1, ?_⟩)
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y z x₀]
  have hp := hint (by positivity) (huU.mono hball)
    (((huU.continuousOn_fderiv_of_isOpen
      ((isOpen_lt continuous_const continuous_im).inter (isOpen_ball.sdiff isClosed_singleton))
      (by norm_num)).clm_apply (continuousOn_const (c := (1 : ℂ)))).mono hsub)
    (fun y hy ↦ by simpa only [hfdU y (hball hy)] using hCR y (hUH (hball hy)))
    (fun y hy ↦ huK (hUH (hball hy))) (hballE.trans_lt hE)
  rw [← hfdU z (hsub (mem_closedBall_self (by positivity)))] at hp
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  linarith

/-- A point `z` of the closed upper half-plane at height less than a quarter of its distance to a
point `x₀` of the real axis has its foot `re z` on the axis at distance more than three quarters of
that distance from `x₀`. -/
private theorem three_mul_norm_sub_div_four_lt_dist_ofReal_re {z : ℂ} (hx₀ : x₀.im = 0)
    (hz : 0 ≤ z.im) (hnear : z.im < ‖z - x₀‖ / 4) :
    3 * ‖z - x₀‖ / 4 < dist (z.re : ℂ) x₀ := by
  rw [dist_of_im_eq (by simp [hx₀]), Real.dist_eq, ofReal_re]
  have hsq : ‖z - x₀‖ ^ 2 = (z.re - x₀.re) ^ 2 + z.im ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp only [sub_re, sub_im, hx₀, sub_zero]
    ring
  by_contra h
  have h2 : (z.re - x₀.re) ^ 2 ≤ (3 * ‖z - x₀‖ / 4) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.1 h) 2
  nlinarith [mul_self_lt_mul_self hz hnear]

/-- Near a boundary puncture, at points at height less than a quarter of their distance `d` to
the puncture, sufficiently small energy on the half-disc of radius `2d` controls the squared
directional derivative: the boundary mean-value inequality applies on the half-disc of radius
`3d / 4` about the foot of the point on the real axis, which misses the puncture. -/
private theorem exists_pos_sq_norm_fderivWithin_one_le_energy_of_im_lt
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ δ > 0, ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ (R / 2) \ {x₀}), z.im < ‖z - x₀‖ / 4 →
      (∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ (2 * ‖z - x₀‖),
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2) < δ →
      ‖z - x₀‖ ^ 2 * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2 ≤
        64 / π * ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ (2 * ‖z - x₀‖),
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  set O := ball x₀ R \ {x₀}
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  -- Inside `O`, `∂ₛu` is continuous up to the edge.
  have hcont : ContinuousOn (fun y ↦ fderivWithin ℝ u H y 1) (H ∩ O) :=
    (hu.continuousOn_fderivWithin_of_inter (uniqueDiffOn_setOfPred_le_im _) hO
      (by norm_num)).clm_apply continuousOn_const
  obtain ⟨δ, hδ, hbdry⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball
      hW hJ hK hKW hJsq hL hJL
  refine ⟨δ, hδ, fun z hz hnear hE ↦ ?_⟩
  set d := ‖z - x₀‖
  have hdR : d < R / 2 := by simpa [mem_ball, dist_eq_norm] using hz.2.1
  -- The foot `x` of `z` on the axis: `z` is at height `im z < d / 4` above it.
  set x : ℂ := (z.re : ℂ)
  have hzx : dist z x = z.im := by
    rw [dist_of_re_eq (by simp [x]), Real.dist_eq, ofReal_im, sub_zero, abs_of_nonneg hz.1]
  have hfoot_le : dist x x₀ ≤ d := by
    rw [dist_of_im_eq (by simp [x, hx₀]), Real.dist_eq, ofReal_re]
    simpa using abs_re_le_norm (z - x₀)
  have hfoot_gt := three_mul_norm_sub_div_four_lt_dist_ofReal_re hx₀ hz.1 hnear
  -- The closed disc of radius `3d / 4` about `x` lies in `B_R(x₀)` and misses `x₀`.
  have hcO : closedBall x (3 * d / 4) ⊆ O := fun y hy ↦ by
    have hyx : dist y x ≤ 3 * d / 4 := mem_closedBall.1 hy
    refine ⟨?_, fun hyx₀ ↦ ?_⟩
    · rw [mem_ball]
      linarith [dist_triangle y x x₀]
    · rw [mem_singleton_iff.1 hyx₀, dist_comm] at hyx
      linarith
  have hbO : ball x (3 * d / 4) ⊆ O := ball_subset_closedBall.trans hcO
  have hhalfE : ∫ y in H ∩ ball x (3 * d / 4), ‖fderivWithin ℝ u H y 1‖ ^ 2 ≤
      ∫ y in H ∩ ball x₀ (2 * d), ‖fderivWithin ℝ u H y 1‖ ^ 2 := by
    refine setIntegral_mono_set
      (henergy.mono_set (inter_subset_inter_right _ (ball_subset_ball (by linarith))))
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall fun y hy ↦ ⟨hy.1, ?_⟩)
    have hy2 : dist y x < 3 * d / 4 := mem_ball.1 hy.2
    rw [mem_ball]
    linarith [dist_triangle y x x₀]
  have hp := hbdry (r := 3 * d / 4) (ρ := d / 2) (by simp [x]) hz.1 (by positivity)
    (fun y hy ↦ by
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle y z x])
    (hu.mono (inter_subset_inter_right _ hbO)) (hcont.mono (inter_subset_inter_right _ hcO))
    (fun y hy ↦ hCR y ⟨hy.1, hbO hy.2⟩) (fun y hy hy0 ↦ huL y (hbO hy) hy0)
    (fun y hy ↦ huK ⟨hy.1, hbO hy.2⟩) (hhalfE.trans_lt hE)
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  linarith

/-- Near a boundary puncture, sufficiently small energy on the outer half-disc controls the
squared directional derivative, uniformly in the direction of approach: a point `z` at distance
`d` from the puncture satisfies `d² ‖∂ₛu(z)‖² ≤ (512 / π) ∫_{{0 ≤ im y} ∩ B_{2d}(x₀)} ‖∂ₛu‖²`
once that energy is small. -/
theorem exists_pos_sq_norm_fderivWithin_one_le_energy
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ δ > 0, ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ (R / 2) \ {x₀}),
      (∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ (2 * ‖z - x₀‖),
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2) < δ →
      ‖z - x₀‖ ^ 2 * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2 ≤
        512 / π * ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ (2 * ‖z - x₀‖),
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  obtain ⟨δ₁, hδ₁, hfar⟩ :=
    exists_pos_sq_norm_fderivWithin_one_le_energy_of_le_im hW hJ hK hKW hJsq hu hCR huK henergy
  obtain ⟨δ₂, hδ₂, hnear⟩ := exists_pos_sq_norm_fderivWithin_one_le_energy_of_im_lt hW hJ hK hKW
    hJsq hL hJL hx₀ hu hCR huL huK henergy
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz hE ↦ ?_⟩
  rcases le_or_gt (‖z - x₀‖ / 4) z.im with h | h
  · exact hfar z hz h (hE.trans_le (min_le_left _ _))
  · refine (hnear z hz h (hE.trans_le (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right (by gcongr; norm_num) ?_)
    exact setIntegral_nonneg
      ((measurableSet_le measurable_const continuous_im.measurable).inter measurableSet_ball)
      fun _ _ ↦ sq_nonneg _

/-- **Derivative decay at a boundary puncture.** Let `x₀` lie on the real axis, let `J` be `C²` on
an open set `W` containing a compact set `K`, with `J(x)² = -1` on `K`, and let `L` be a closed
subspace such that `J(p)` maps `L` into `Lᗮ` for every `p ∈ L ∩ W`. A solution `u` of
`∂ₜu = J(u) ∂ₛu` that is `C³` up to the straight edge on the punctured half-disc
`{0 ≤ im z} ∩ B_R(x₀) \ {x₀}`, maps the edge into `L` and the punctured half-disc into `K`, and has
finite energy `∫_{{0 ≤ im y} ∩ B_R(x₀)} ‖∂ₛu‖² < ∞` satisfies `|z - x₀| ‖∂ₛu(z)‖ → 0` as `z → x₀`
in the closed upper half-plane. Derivatives are taken within the closed upper half-plane. -/
theorem tendsto_norm_sub_mul_norm_fderivWithin_one_nhdsWithin
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0) (hx₀ : x₀.im = 0)
    (hR : 0 < R) (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (hE : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    Tendsto (fun z ↦ ‖z - x₀‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖)
      (𝓝[{z | 0 ≤ z.im} \ {x₀}] x₀) (𝓝 0) := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_sq_norm_fderivWithin_one_le_energy hW hJ hK hKW hJsq hL hJL hx₀ hu hCR huL huK hE
  -- The energy `ε ρ` of `u` in the half-disc of radius `ρ` about the puncture tends to zero.
  set ε : ℝ → ℝ := fun ρ ↦
    ∫ y in ball x₀ ρ, ‖fderivWithin ℝ u H y 1‖ ^ 2 ∂(volume.restrict (H ∩ ball x₀ R)) with hεdef
  have hε : Tendsto ε (𝓝 0) (𝓝 0) := hE.tendsto_setIntegral_ball_nhds_zero x₀
  have hεz : Tendsto (fun z ↦ ε (2 * ‖z - x₀‖)) (𝓝[H \ {x₀}] x₀) (𝓝 0) :=
    hε.comp ((((continuous_id.sub continuous_const).norm.const_mul 2).tendsto' x₀ 0
      (by simp)).mono_left nhdsWithin_le_nhds)
  -- The bound of `TauCeti.exists_pos_sq_norm_fderivWithin_one_le_energy` near the puncture.
  have hbound : ∀ᶠ z in 𝓝[H \ {x₀}] x₀,
      (‖z - x₀‖ * ‖fderivWithin ℝ u H z 1‖) ^ 2 ≤ 512 / π * ε (2 * ‖z - x₀‖) := by
    have hnear : ∀ᶠ z in 𝓝[H \ {x₀}] x₀, z ∈ ball x₀ (R / 2) :=
      nhdsWithin_le_nhds (ball_mem_nhds x₀ (half_pos hR))
    filter_upwards [self_mem_nhdsWithin, hεz.eventually (gt_mem_nhds hδ), hnear]
      with z hz hzε hzR
    have hzR' : ‖z - x₀‖ < R / 2 := by simpa only [mem_ball, dist_eq_norm] using hzR
    have houter : ball x₀ (2 * ‖z - x₀‖) ⊆ ball x₀ R := ball_subset_ball (by linarith)
    have hεeq : ε (2 * ‖z - x₀‖) =
        ∫ y in H ∩ ball x₀ (2 * ‖z - x₀‖), ‖fderivWithin ℝ u H y 1‖ ^ 2 := by
      simp only [hεdef, Measure.restrict_restrict measurableSet_ball]
      rw [inter_left_comm, inter_eq_left.mpr houter]
    rw [hεeq] at hzε ⊢
    simpa only [mul_pow] using hmean z ⟨hz.1, hzR, hz.2⟩ hzε
  have hlim : Tendsto (fun z ↦ √(512 / π * ε (2 * ‖z - x₀‖))) (𝓝[H \ {x₀}] x₀) (𝓝 0) := by
    simpa using (hεz.const_mul (512 / π)).sqrt
  refine squeeze_zero' (Eventually.of_forall fun z ↦ by positivity) ?_ hlim
  filter_upwards [hbound] with z hz
  exact (le_abs_self _).trans (Real.abs_le_sqrt hz)

/-- **Derivative decay at a boundary puncture, full derivative.** Under the hypotheses of
`TauCeti.tendsto_norm_sub_mul_norm_fderivWithin_one_nhdsWithin`, the full derivative of a
finite-energy solution of `∂ₜu = J(u) ∂ₛu` on the punctured half-disc
`{0 ≤ im z} ∩ B_R(x₀) \ {x₀}` with image in `K` and boundary values in `L` satisfies
`|z - x₀| ‖du(z)‖ → 0` as `z → x₀` in the closed upper half-plane. -/
theorem tendsto_norm_sub_mul_norm_fderivWithin_nhdsWithin
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0) (hx₀ : x₀.im = 0)
    (hR : 0 < R) (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (hE : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    Tendsto (fun z ↦ ‖z - x₀‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖)
      (𝓝[{z | 0 ≤ z.im} \ {x₀}] x₀) (𝓝 0) := by
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  have h := (tendsto_norm_sub_mul_norm_fderivWithin_one_nhdsWithin hW hJ hK hKW hJsq hL hJL hx₀
    hR hu hCR huL huK hE).const_mul (1 + max a 0)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun z ↦ by positivity) ?_ h
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x₀ hR)] with z hz hzR
  have hz' : z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}) := ⟨hz.1, hzR, hz.2⟩
  -- The Cauchy--Riemann equation bounds `‖∂ₜu‖ = ‖J(u) ∂ₛu‖` by a multiple of `‖∂ₛu‖`.
  have hop : ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖ ≤
      (1 + max a 0) * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ :=
    (fderivWithin ℝ u {z | 0 ≤ z.im} z).norm_le_of_apply_I_eq (hCR z hz')
      ((ha _ (huK hz')).trans (le_max_left _ _)) le_rfl
  calc ‖z - x₀‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖
      ≤ ‖z - x₀‖ * ((1 + max a 0) * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖) := by gcongr
    _ = (1 + max a 0) * (‖z - x₀‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖) := by ring

/-- **Half-circles about a boundary puncture have shrinking images.** Under the hypotheses of
`TauCeti.tendsto_norm_sub_mul_norm_fderivWithin_one_nhdsWithin`, the image under a finite-energy
solution `u` of `∂ₜu = J(u) ∂ₛu` of the half-circle `{0 ≤ im z, |z - x₀| = ρ}` about the
puncture has diameter tending to `0` as `ρ → 0`. -/
theorem tendsto_diam_image_inter_sphere_nhdsGT_zero
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0) (hx₀ : x₀.im = 0)
    (hR : 0 < R) (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (hE : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    Tendsto (fun ρ ↦ diam (u '' ({z : ℂ | 0 ≤ z.im} ∩ sphere x₀ ρ))) (𝓝[>] 0) (𝓝 0) := by
  have hO : IsOpen (ball x₀ R \ {x₀}) := isOpen_ball.sdiff isClosed_singleton
  refine tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto hx₀ ?_
    (tendsto_norm_sub_mul_norm_fderivWithin_nhdsWithin hW hJ hK hKW hJsq hL hJL hx₀ hR hu hCR huL
      huK hE)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x₀ hR)] with z hz hzR
  exact (differentiableWithinAt_inter (hO.mem_nhds ⟨hzR, hz.2⟩)).1
    ((hu.differentiableOn (by norm_num)) z ⟨hz.1, hzR, hz.2⟩)

end TauCeti
