/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Boundary.MeanValue
public import TauCeti.MeasureTheory.Integral.EnergyConcentration
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.RCLike.OperatorNorm

/-!
# Energy quantization and bubbling up to the boundary for `J`-holomorphic half-discs

Let `J` be a `C²` almost complex structure, written as a matrix-valued function
`J : V → (V →L[ℝ] V)` on an open set `W` of a real inner product space, let `K ⊆ W` be compact,
and let `L ⊆ V` be a closed subspace such that `J(p)` maps `L` into `Lᗮ` for `p ∈ L ∩ W`.
Curves are solutions `u : ℂ → V` of the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` on (parts of)
the closed upper half-plane `{0 ≤ im z}`, regular up to the real axis, with boundary condition
`u(s) ∈ L` on the axis. Derivatives are taken within the closed upper half-plane, and the energy
is the real-direction energy `∫ ‖∂ₛu‖²`.

The boundary mean-value inequality
`exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball`
provides a threshold `δ > 0` such that a curve with energy less than `δ` on
`{0 ≤ im z} ∩ ball x₀ r`, for any `x₀` in the closed upper half-plane, satisfies
`π r² ‖∂ₛu(x₀)‖² ≤ 16 ∫ ‖∂ₛu‖²`. This file draws the consequences of this estimate that control
bubbling at the boundary in Gromov compactness for strips and discs with totally real boundary
conditions. They are the boundary counterparts of
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Quantization` and
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Bubbling`.

* **Energy quantization for half-planes.** A `J`-holomorphic half-plane with boundary on `L`,
  image in `K` and energy less than `δ` is constant: the mean-value inequality on
  `{0 ≤ im z} ∩ ball x r` for every radius `r` bounds `‖∂ₛu(x)‖²` by `16 δ / (π r²)`. So every
  nonconstant half-plane has energy at least `δ`. Rescaling at a boundary point produces disc
  bubbles as half-planes of this kind, so this is the lower bound for their energy.
* **Small-energy Lipschitz bound up to the boundary.** A curve with energy less than `δ` on
  `{0 ≤ im z} ∩ ball z₀ r` is Lipschitz on `{0 ≤ im z} ∩ closedBall z₀ (r / 2)`, with a constant
  depending only on `r`: the mean-value inequality on the sets `{0 ≤ im z} ∩ ball z (r / 4)` bounds
  the derivative there.
* **Energy concentration up to the boundary.** If the derivatives of a family of curves blow up
  at points of the closed upper half-plane converging to `z₀`, possibly on the real axis, then
  eventually every `{0 ≤ im z} ∩ ball z₀ ε` carries energy at least `δ`.
* **Finitely many bubbling points up to the boundary.** A sequence of curves on
  `{0 ≤ im z} ∩ U`, `U` open, with energy at most `E` has a subsequence whose derivatives are
  uniformly bounded on compact subsets of `{0 ≤ im z} ∩ U` off a finite set of at most `E / δ`
  points, which may lie on the real axis, at each of which energy at least `δ` concentrates.

The rescaling that produces sphere and disc bubbles at these points, and the convergence of
subsequences away from them, are not carried out here.

## Main results

* `TauCeti.exists_pos_forall_le_setIntegral_norm_fderivWithin_one_sq_of_ne`: a nonconstant
  `J`-holomorphic half-plane with boundary on `L` and image in `K` has energy at least `δ`.
* `TauCeti.exists_pos_forall_lipschitzOnWith_setOfPred_le_im_inter_of_small_energy`: curves of
  small energy on `{0 ≤ im z} ∩ ball z₀ r` share a Lipschitz bound up to the real axis.
* `TauCeti.exists_pos_forall_eventually_le_setIntegral_norm_fderivWithin_one_sq_inter_ball`:
  energy at least `δ` concentrates near every point of the closed upper half-plane at which the
  derivatives of a family of `J`-holomorphic half-discs blow up.
* `TauCeti.exists_pos_forall_exists_strictMono_finset_norm_fderivWithin_le`: finitely many
  bubbling points, at most `E / δ`, for curves with energy at most `E` on `{0 ≤ im z} ∩ U`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.1 (the lower bound for the energy of
  nonconstant spheres and discs), Section 4.3 (the boundary mean-value inequality) and
  Section 4.6 (the points at which the derivatives blow up).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {J : V → V →L[ℝ] V} {W K : Set V} {L : Submodule ℝ V}

/-- **Energy quantization for `J`-holomorphic half-planes.** Let `J` be `C²` on an open set `W`
containing a compact set `K`, with `J(x)² = -1` on `K`, and let `L` be a closed subspace such that
`J(p)` maps `L` into `Lᗮ` for every `p ∈ L ∩ W`. There is a threshold `δ > 0` such that every
solution `u` of `∂ₜu = J(u) ∂ₛu` on the closed upper half-plane, `C³` up to the real axis, mapping
the axis into `L` and the closed upper half-plane into `K`, with integrable energy density and
nonconstant on the closed upper half-plane, has energy `∫_{0 ≤ im z} ‖∂ₛu‖² ≥ δ`. Derivatives are
taken within the closed upper half-plane. -/
theorem exists_pos_forall_le_setIntegral_norm_fderivWithin_one_sq_of_ne
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, inner ℝ v (J p w) = 0) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄, ContDiffOn ℝ 3 u {z | 0 ≤ z.im} →
      (∀ y ∈ {z : ℂ | 0 ≤ z.im},
        fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1)) →
      (∀ y : ℂ, y.im = 0 → u y ∈ L) → MapsTo u {z | 0 ≤ z.im} K →
      IntegrableOn (fun y ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2) {z | 0 ≤ z.im} →
      ∀ ⦃z w : ℂ⦄, 0 ≤ z.im → 0 ≤ w.im → u z ≠ u w →
      δ ≤ ∫ y in {z : ℂ | 0 ≤ z.im}, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball
      hW hJ hK hKW hJsq hL hJL
  refine ⟨δ, hδ, fun u hu hCR huL huK hInt z w hz hw hzw ↦ ?_⟩
  by_contra! hE
  set H : Set ℂ := {z | 0 ≤ z.im}
  set E := ∫ y in H, ‖fderivWithin ℝ u H y 1‖ ^ 2
  have hDu : ContinuousOn (fderivWithin ℝ u H) H :=
    hu.continuousOn_fderivWithin (uniqueDiffOn_setOfPred_le_im 0) (by norm_num)
  -- The mean-value inequality on `H ∩ ball x r` bounds `π r² ‖∂ₛu(x)‖²` by `16 E`, uniformly in
  -- `r`, so `∂ₛu(x) = 0`.
  have hzero : ∀ x ∈ H, fderivWithin ℝ u H x 1 = 0 := by
    intro x hx
    have hbound : ∀ r, 0 < r → Real.pi * r ^ 2 * ‖fderivWithin ℝ u H x 1‖ ^ 2 ≤ 16 * E := by
      intro r hr
      have hball : ∫ y in H ∩ ball x r, ‖fderivWithin ℝ u H y 1‖ ^ 2 ≤ E :=
        setIntegral_mono_set hInt (ae_restrict_of_forall_mem (measurableSet_le measurable_const
          continuous_im.measurable) fun _ _ ↦ sq_nonneg _) (Eventually.of_forall inter_subset_left)
      exact (hmean hx hx hr.le subset_rfl (hu.mono inter_subset_left)
        ((hDu.clm_apply continuousOn_const).mono inter_subset_left)
        (fun y hy ↦ hCR y hy.1) (fun y _ hy0 ↦ huL y hy0) (fun y hy ↦ huK hy.1)
        (hball.trans_lt hE)).trans (by gcongr)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      ((nonpos_of_forall_pos_mul_sq_mul_le Real.pi_pos hbound).antisymm (sq_nonneg _)))
  -- By the Cauchy--Riemann equation the whole differential vanishes, so `u` is constant on the
  -- convex set `H`.
  have hfderiv : ∀ x ∈ H, fderivWithin ℝ u H x = 0 := by
    intro x hx
    refine norm_le_zero_iff.mp (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v ↦ ?_)
    simpa [hzero x hx, hCR x hx] using (fderivWithin ℝ u H x).norm_apply_le_norm_one_add_norm_I v
  exact hzw ((convex_halfSpace_im_ge 0).is_const_of_fderivWithin_eq_zero
    (hu.differentiableOn (by norm_num)) hfderiv hz hw)

/-- The pointwise small-energy bound behind the Lipschitz and concentration theorems. Let `δ`
be a threshold for the boundary mean-value inequality `hmean` and `a` a bound for `‖J‖` on `K`. A
curve with energy less than `δ` on `{0 ≤ im z} ∩ ball z₀ R` has `‖du(z)‖ ≤ (1 + max a 0) * B`,
with `B = 1 + 16 δ / (π ρ²)`, at every `z` of the closed upper half-plane with
`closedBall z ρ ⊆ ball z₀ R`: the mean-value inequality on `{0 ≤ im z} ∩ ball z ρ` bounds
`‖∂ₛu(z)‖` by `B`, and then the Cauchy--Riemann equation bounds `‖du(z)‖`. -/
private theorem norm_fderivWithin_le_of_small_energy {δ a ρ R : ℝ} {z₀ z : ℂ} {u : ℂ → V}
    (hmean : ∀ ⦃u : ℂ → V⦄ ⦃x₀ z : ℂ⦄ ⦃r ρ : ℝ⦄, 0 ≤ x₀.im → 0 ≤ z.im → 0 ≤ ρ →
      ball z ρ ⊆ ball x₀ r →
      ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ ball x₀ r) →
      ContinuousOn (fun y ↦ fderivWithin ℝ u {z | 0 ≤ z.im} y 1)
        ({z | 0 ≤ z.im} ∩ closedBall x₀ r) →
      (∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
        fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1)) →
      (∀ y ∈ ball x₀ r, y.im = 0 → u y ∈ L) →
      (∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, u y ∈ K) →
      ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 < δ →
      Real.pi * ρ ^ 2 * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2 ≤
        16 * ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2)
    (ha : ∀ x ∈ K, ‖J x‖ ≤ a) (hz : 0 ≤ z.im) (hρ : 0 < ρ) (hsub : closedBall z ρ ⊆ ball z₀ R)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ ball z₀ R))
    (hCR : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball z₀ R,
      fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1))
    (huL : ∀ y ∈ ball z₀ R, y.im = 0 → u y ∈ L) (huK : MapsTo u ({z | 0 ≤ z.im} ∩ ball z₀ R) K)
    (hInt : IntegrableOn (fun y ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball z₀ R))
    (hE : ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball z₀ R, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 < δ) :
    ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖ ≤
      (1 + max a 0) * (1 + 16 * δ / (Real.pi * ρ ^ 2)) := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hsub' : ball z ρ ⊆ ball z₀ R := ball_subset_closedBall.trans hsub
  have hDu : ContinuousOn (fderivWithin ℝ u H) (H ∩ ball z₀ R) :=
    continuousOn_fderivWithin_setOfPred_le_im_inter isOpen_ball hu (by norm_num)
  have hmono : ∫ y in H ∩ ball z ρ, ‖fderivWithin ℝ u H y 1‖ ^ 2 ≤
      ∫ y in H ∩ ball z₀ R, ‖fderivWithin ℝ u H y 1‖ ^ 2 :=
    setIntegral_mono_set hInt
      (ae_restrict_of_forall_mem ((measurableSet_le measurable_const
        continuous_im.measurable).inter measurableSet_ball) fun _ _ ↦ sq_nonneg _)
      (Eventually.of_forall (inter_subset_inter_right _ hsub'))
  have h := hmean hz hz hρ.le subset_rfl (hu.mono (inter_subset_inter_right _ hsub'))
    ((hDu.clm_apply continuousOn_const).mono (inter_subset_inter_right _ hsub))
    (fun y hy ↦ hCR y ⟨hy.1, hsub' hy.2⟩) (fun y hy hy0 ↦ huL y (hsub' hy) hy0)
    (fun y hy ↦ huK ⟨hy.1, hsub' hy.2⟩) (hmono.trans_lt hE)
  have hp : 0 < Real.pi * ρ ^ 2 := by positivity
  have hsq : ‖fderivWithin ℝ u H z 1‖ ^ 2 ≤ 16 * δ / (Real.pi * ρ ^ 2) := by
    rw [le_div_iff₀ hp]
    nlinarith
  have hzr : z ∈ H ∩ ball z₀ R := ⟨hz, hsub (mem_closedBall_self hρ.le)⟩
  exact (fderivWithin ℝ u H z).norm_le_of_apply_I_eq (hCR z hzr)
    ((ha _ (huK hzr)).trans (le_max_left _ _))
    (by nlinarith [sq_nonneg (‖fderivWithin ℝ u H z 1‖ - 1)])

/-- **Small-energy Lipschitz bound up to the boundary.** Let `J` be `C²` on an open set `W`
containing a compact set `K`, with `J(x)² = -1` on `K`, and let `L` be a closed subspace such that
`J(p)` maps `L` into `Lᗮ` for every `p ∈ L ∩ W`. There is a threshold `δ > 0` such that for every
radius `r > 0` there is a constant `C` with the following property. Every solution `u` of
`∂ₜu = J(u) ∂ₛu` on `{0 ≤ im z} ∩ ball z₀ r`, `C³` up to the real axis, mapping the axis into
`L` and `{0 ≤ im z} ∩ ball z₀ r` into `K`, with integrable energy density and energy less than `δ`
there, is `C`-Lipschitz on `{0 ≤ im z} ∩ closedBall z₀ (r / 2)`. The constant `C` does not
depend on `z₀` or `u`. Derivatives are taken within the closed upper half-plane. -/
theorem exists_pos_forall_lipschitzOnWith_setOfPred_le_im_inter_of_small_energy
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, inner ℝ v (J p w) = 0) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → ∃ C : ℝ≥0, ∀ ⦃z₀ : ℂ⦄ ⦃u : ℂ → V⦄,
      ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ ball z₀ r) →
      (∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball z₀ r,
        fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1)) →
      (∀ y ∈ ball z₀ r, y.im = 0 → u y ∈ L) → MapsTo u ({z | 0 ≤ z.im} ∩ ball z₀ r) K →
      IntegrableOn (fun y ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2)
        ({z | 0 ≤ z.im} ∩ ball z₀ r) →
      ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball z₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 < δ →
      LipschitzOnWith C u ({z | 0 ≤ z.im} ∩ closedBall z₀ (r / 2)) := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball
      hW hJ hK hKW hJsq hL hJL
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  refine ⟨δ, hδ, fun r hr ↦ ?_⟩
  set B := 1 + 16 * δ / (Real.pi * (r / 4) ^ 2)
  refine ⟨⟨(1 + max a 0) * B, by positivity⟩, fun z₀ u hu hCR huL huK hInt hE ↦ ?_⟩
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hinner : closedBall z₀ (r / 2) ⊆ ball z₀ r := closedBall_subset_ball (by linarith)
  -- The mean-value inequality on `H ∩ ball z (r / 4)` bounds `‖∂ₛu‖` by `B` on the smaller set,
  -- and then the Cauchy--Riemann equation bounds `‖du‖` there by `(1 + max a 0) * B`.
  have hop : ∀ z ∈ H ∩ closedBall z₀ (r / 2), ‖fderivWithin ℝ u H z‖ ≤ (1 + max a 0) * B :=
    fun z hz ↦ norm_fderivWithin_le_of_small_energy hmean ha hz.1 (by positivity)
      (closedBall_subset_ball' (by linarith [mem_closedBall.mp hz.2])) hu hCR huL huK hInt hE
  have hconv : Convex ℝ (H ∩ closedBall z₀ (r / 2)) :=
    (convex_halfSpace_im_ge 0).inter (convex_closedBall z₀ (r / 2))
  refine hconv.lipschitzOnWith_of_nnNorm_hasFDerivWithin_le (fun z hz ↦ ?_)
    (fun z hz ↦ by exact_mod_cast hop z hz)
  -- On `H ∩ ball z₀ r` the derivative within `H` is a derivative within `H ∩ ball z₀ r`.
  have hzr : z ∈ H ∩ ball z₀ r := ⟨hz.1, hinner hz.2⟩
  rw [← fderivWithin_inter (isOpen_ball.mem_nhds hzr.2)]
  exact (((hu.differentiableOn (by norm_num)) z hzr).hasFDerivWithinAt).mono
    (inter_subset_inter_right _ hinner)

/-- **Energy concentration at blow-up points, up to the boundary.** Let `J` be `C²` on an open
set `W` containing a compact set `K`, with `J(x)² = -1` on `K`, and let `L` be a closed subspace
such that `J(p)` maps `L` into `Lᗮ` for every `p ∈ L ∩ W`. There is a threshold `δ > 0` with the
following property. Let `uᵢ` be a family of solutions of `∂ₜu = J(u) ∂ₛu` on
`{0 ≤ im z} ∩ ball z₀ r`, `C³` up to the real axis, mapping the axis into `L` and
`{0 ≤ im z} ∩ ball z₀ r` into `K`, with integrable energy density, and let `zᵢ → z₀` be points of
the closed upper half-plane at which the differentials blow up, `‖duᵢ(zᵢ)‖ → ∞`. Then for every
`0 < ε ≤ r`, eventually `∫_{{0 ≤ im z} ∩ ball z₀ ε} ‖∂ₛuᵢ‖² ≥ δ`. Derivatives are taken within the
closed upper half-plane. -/
theorem exists_pos_forall_eventually_le_setIntegral_norm_fderivWithin_one_sq_inter_ball
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, inner ℝ v (J p w) = 0) :
    ∃ δ > 0, ∀ ⦃ι : Type*⦄ ⦃l : Filter ι⦄ ⦃u : ι → ℂ → V⦄ ⦃z : ι → ℂ⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄,
      (∀ i, ContDiffOn ℝ 3 (u i) ({z | 0 ≤ z.im} ∩ ball z₀ r)) →
      (∀ i, ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball z₀ r, fderivWithin ℝ (u i) {z | 0 ≤ z.im} y I =
        J (u i y) (fderivWithin ℝ (u i) {z | 0 ≤ z.im} y 1)) →
      (∀ i, ∀ y ∈ ball z₀ r, y.im = 0 → u i y ∈ L) →
      (∀ i, MapsTo (u i) ({z | 0 ≤ z.im} ∩ ball z₀ r) K) →
      (∀ i, IntegrableOn (fun y ↦ ‖fderivWithin ℝ (u i) {z | 0 ≤ z.im} y 1‖ ^ 2)
        ({z | 0 ≤ z.im} ∩ ball z₀ r)) →
      (∀ i, 0 ≤ (z i).im) → Tendsto z l (𝓝 z₀) →
      Tendsto (fun i ↦ ‖fderivWithin ℝ (u i) {z | 0 ≤ z.im} (z i)‖) l atTop →
      ∀ ε, 0 < ε → ε ≤ r → ∀ᶠ i in l, δ ≤
        ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball z₀ ε, ‖fderivWithin ℝ (u i) {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball
      hW hJ hK hKW hJsq hL hJL
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  refine ⟨δ, hδ, fun ι l u z z₀ r hu hCR huL huK hInt hzH hz hblow ε hε hεr ↦ ?_⟩
  set H : Set ℂ := {z | 0 ≤ z.im}
  -- A small-energy half-disc of radius `ε / 2` about `zᵢ` bounds `‖∂ₛu‖` at `zᵢ` by `B`, and then
  -- the Cauchy--Riemann equation bounds `‖du‖` there by `(1 + max a 0) * B`.
  set B := 1 + 16 * δ / (Real.pi * (ε / 2) ^ 2)
  filter_upwards [hz.eventually (ball_mem_nhds z₀ (half_pos hε)),
    hblow.eventually_gt_atTop ((1 + max a 0) * B)] with i hzi hbig
  by_contra! hE
  have hεr' : H ∩ ball z₀ ε ⊆ H ∩ ball z₀ r := inter_subset_inter_right _ (ball_subset_ball hεr)
  have hop : ‖fderivWithin ℝ (u i) H (z i)‖ ≤ (1 + max a 0) * B :=
    norm_fderivWithin_le_of_small_energy hmean ha (hzH i) (half_pos hε)
      (closedBall_subset_ball' (by linarith [mem_ball.mp hzi])) ((hu i).mono hεr')
      (fun y hy ↦ hCR i y (hεr' hy)) (fun y hy hy0 ↦ huL i y (ball_subset_ball hεr hy) hy0)
      ((huK i).mono_left hεr') ((hInt i).mono_set hεr') hE
  linarith

/-- **Finitely many bubbling points, up to the boundary.** Let `J` be `C²` on an open set `W`
containing a compact set `K`, with `J(x)² = -1` on `K`, and let `L` be a closed subspace such that
`J(p)` maps `L` into `Lᗮ` for every `p ∈ L ∩ W`. There is a threshold `δ > 0` with the following
property. Let `U ⊆ ℂ` be open and let `uₖ` be solutions of `∂ₜu = J(u) ∂ₛu` on `{0 ≤ im z} ∩ U`,
`C³` up to the real axis, mapping the axis into `L` and `{0 ≤ im z} ∩ U` into `K`, with integrable
energy density and energy `∫ ‖∂ₛuₖ‖² ≤ E` over `{0 ≤ im z} ∩ U`. Then there are a subsequence `φ`
and a finite set `Z ⊆ {0 ≤ im z} ∩ U`, possibly meeting the real axis, with `#Z * δ ≤ E` such
that, along `φ`, every disc about a point of `Z` eventually carries energy at least `δ` in
`{0 ≤ im z} ∩ U`, and the differentials `du_{φ n}` are uniformly bounded on every compact subset
of `({0 ≤ im z} ∩ U) \ Z`. Derivatives are taken within the closed upper half-plane. -/
theorem exists_pos_forall_exists_strictMono_finset_norm_fderivWithin_le
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, inner ℝ v (J p w) = 0) :
    ∃ δ > 0, ∀ ⦃U : Set ℂ⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen U →
      (∀ k, ContDiffOn ℝ 3 (u k) ({z | 0 ≤ z.im} ∩ U)) →
      (∀ k, ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ U, fderivWithin ℝ (u k) {z | 0 ≤ z.im} y I =
        J (u k y) (fderivWithin ℝ (u k) {z | 0 ≤ z.im} y 1)) →
      (∀ k, ∀ y ∈ U, y.im = 0 → u k y ∈ L) →
      (∀ k, MapsTo (u k) ({z | 0 ≤ z.im} ∩ U) K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderivWithin ℝ (u k) {z | 0 ≤ z.im} y 1‖ ^ 2)
        ({z | 0 ≤ z.im} ∩ U)) →
      (∀ k, ∫ y in {z : ℂ | 0 ≤ z.im} ∩ U, ‖fderivWithin ℝ (u k) {z | 0 ≤ z.im} y 1‖ ^ 2 ≤ E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset ℂ, ↑Z ⊆ {z : ℂ | 0 ≤ z.im} ∩ U ∧
        Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ ({z : ℂ | 0 ≤ z.im} ∩ U),
          ‖fderivWithin ℝ (u (φ n)) {z | 0 ≤ z.im} y 1‖ ^ 2) ∧
        ∀ C, IsCompact C → C ⊆ ({z : ℂ | 0 ≤ z.im} ∩ U) \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderivWithin ℝ (u (φ n)) {z | 0 ≤ z.im} y‖ ≤ M := by
  obtain ⟨δ, hδ, hconc⟩ :=
    exists_pos_forall_eventually_le_setIntegral_norm_fderivWithin_one_sq_inter_ball
      hW hJ hK hKW hJsq hL hJL
  refine ⟨δ, hδ, fun U u E hU hu hCR huL huK hint hE ↦ ?_⟩
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hHm : MeasurableSet H := measurableSet_le measurable_const continuous_im.measurable
  refine exists_strictMono_finset_forall_le_of_concentration (hHm.inter hU.measurableSet) hδ
    (fun k ↦ (continuousOn_fderivWithin_setOfPred_le_im_inter hU (hu k) (by norm_num)).norm)
    (fun k y _ ↦ sq_nonneg _) hint hE ?_
  -- A blow-up point `z₀` is the centre of a disc `B_r(z₀) ⊆ U`, on which the energy
  -- concentration theorem applies; the energy of `H ∩ B_{min ε r}(z₀)` bounds that of
  -- `B_ε(z₀) ∩ (H ∩ U)`.
  intro φ _ z z₀ hzΩ hz₀ hz hblow ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀.2
  have hrΩ : H ∩ ball z₀ r ⊆ H ∩ U := inter_subset_inter_right _ hrU
  filter_upwards [hconc (u := fun n ↦ u (φ n)) (fun n ↦ (hu (φ n)).mono hrΩ)
    (fun n y hy ↦ hCR (φ n) y (hrΩ hy)) (fun n y hy ↦ huL (φ n) y (hrU hy))
    (fun n ↦ (huK (φ n)).mono_left hrΩ) (fun n ↦ (hint (φ n)).mono_set hrΩ)
    (fun n ↦ (hzΩ n).1) hz hblow (min ε r) (lt_min hε hr) (min_le_right _ _)] with n hn
  have hsub : H ∩ ball z₀ (min ε r) ⊆ ball z₀ ε ∩ (H ∩ U) := fun y hy ↦
    ⟨ball_subset_ball (min_le_left _ _) hy.2,
      hrΩ ⟨hy.1, ball_subset_ball (min_le_right _ _) hy.2⟩⟩
  exact hn.trans (setIntegral_mono_set ((hint (φ n)).mono_set inter_subset_right)
    (ae_restrict_of_forall_mem (measurableSet_ball.inter (hHm.inter hU.measurableSet))
      fun _ _ ↦ sq_nonneg _) (Eventually.of_forall hsub))

end TauCeti
