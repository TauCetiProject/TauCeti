/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
import Mathlib.Analysis.Analytic.Constructions
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.IteratedFDeriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Taylor

/-!
# The exterior multipole expansion of the planar Newtonian kernel

The planar Newtonian kernel `G(z) = -(2π)⁻¹ log ‖z‖` on `ℂ` is real analytic away from its pole,
and its power series at a point `a ≠ 0` converges on a ball whose radius is a fixed multiple
`c ‖a‖`, with `0 < c < 1`, so that the ball excludes the pole
(`TauCeti.exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel`). Because `G(y) = G(a) +
G(a⁻¹ y)` for all `y ≠ 0`, multiplication by `a⁻¹` sends `a` to `1` and rescales the radius of
convergence at `1` by `‖a‖`.

Expanding `y ↦ G(x - y)` about the origin gives the **exterior multipole expansion**: for `‖y‖`
below a fixed multiple of `‖x‖`,

`G(x - y) = ∑ₖ Pₖ(y)`,

where each homogeneous term `Pₖ(y) = pₖ (y, …, y)` is harmonic on all of `ℂ`
(`TauCeti.exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel_sub`), as a Taylor term of a
harmonic function (`HasFPowerSeriesAt.harmonicAt_apply`). Consequently, on a closed ball of radius
a fixed multiple of `‖x‖`, the kernel with pole `x` is the limit of the partial sums of this
expansion, which are harmonic everywhere, uniformly together with all iterated derivatives
(`TauCeti.exists_harmonicAt_tendstoUniformlyOn_iteratedFDeriv_planarNewtonianKernel_sub`).

## Main declarations

* `TauCeti.exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel`: the planar kernel has a
  power series at each `a ≠ 0` converging on a ball of radius `c ‖a‖`, where `0 < c < 1`.
* `TauCeti.exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel_sub`: the exterior multipole
  expansion `G(x - y) = ∑ₖ Pₖ(y)` with harmonic homogeneous terms.
* `TauCeti.exists_harmonicAt_tendstoUniformlyOn_iteratedFDeriv_planarNewtonianKernel_sub`:
  approximation of the planar kernel with a distant pole by globally harmonic functions, uniformly
  with all iterated derivatives.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapters 5 and 10.
* O. D. Kellogg, *Foundations of Potential Theory*, Chapter V.
-/

public section

open Filter InnerProductSpace Metric Set Topology
open scoped NNReal ENNReal

namespace TauCeti

/-- **The planar Newtonian kernel has power series on balls proportional to the distance to the
pole.** There is a constant `0 < c < 1` such that at every point `a ≠ 0` the kernel
`planarNewtonianKernel` has a power series converging on the ball of radius `c ‖a‖` about `a`. -/
theorem exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel :
    ∃ c : ℝ≥0, 0 < c ∧ c < 1 ∧ ∀ a : ℂ, a ≠ 0 →
      ∃ p : FormalMultilinearSeries ℝ ℂ ℝ,
        HasFPowerSeriesOnBall planarNewtonianKernel p a (c * ‖a‖₊) := by
  obtain ⟨p, r, hpr⟩ := (harmonicAt_planarNewtonianKernel (z := (1 : ℂ)) one_ne_zero).analyticAt
  obtain ⟨c, hc0, hcr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hpr.r_pos one_pos)
  have hc1 : (c : ℝ) < 1 := mod_cast (lt_min_iff.1 hcr).2
  refine ⟨c, mod_cast hc0, mod_cast (lt_min_iff.1 hcr).2, fun a ha ↦ ?_⟩
  -- Multiplication by `a⁻¹` sends `a` to `1` and has operator norm `‖a‖⁻¹`.
  set u : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ a⁻¹
  have hua : u a = 1 := inv_mul_cancel₀ ha
  have hu : ‖u‖₊ ≤ ‖a‖₊⁻¹ := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_inv, coe_nnNorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
    simp [u]
  have ha' : (‖a‖₊ : ℝ≥0∞) ≠ 0 := by simpa using ha
  have hrad_pos : (0 : ℝ≥0∞) < (c : ℝ≥0∞) * ‖a‖₊ :=
    ENNReal.mul_pos (ENNReal.coe_ne_zero.2 (by simpa using hc0.ne')) ha'
  have hrad_le : (c : ℝ≥0∞) * ‖a‖₊ ≤ r / ‖u‖ₑ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inr hpr.r_pos.ne') (Or.inl eNorm_ne_top)]
    calc (c : ℝ≥0∞) * ‖a‖₊ * ‖u‖ₑ ≤ c * ‖a‖₊ * (‖a‖₊ : ℝ≥0∞)⁻¹ := by
          gcongr
          rw [← ofReal_norm, ← coe_nnNorm, ENNReal.ofReal_coe_nnreal,
            ← ENNReal.coe_inv (by simpa using ha)]
          exact ENNReal.coe_le_coe.2 hu
      _ = c := by rw [mul_assoc, ENNReal.mul_inv_cancel ha' ENNReal.coe_ne_top, mul_one]
      _ ≤ r := (lt_min_iff.1 hcr).1.le
  have hcomp := ((hua ▸ hpr).compContinuousLinearMap).mono hrad_pos hrad_le
  have hconst :=
    (hasFPowerSeriesOnBall_const (𝕜 := ℝ) (c := planarNewtonianKernel a) (e := a)).mono
      hrad_pos le_top
  refine ⟨_, (hconst.add hcomp).congr fun y hy ↦ ?_⟩
  -- Since `c < 1`, the ball `eball a (c * ‖a‖)` avoids the pole `0`, so `G(y) = G(a) + G(a⁻¹ y)`.
  have hy_ball : y ∈ ball a ((c : ℝ) * ‖a‖) := by
    rwa [← ENNReal.coe_mul, Metric.eball_coe, NNReal.coe_mul, coe_nnNorm] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mem_ball, dist_zero_left] at hy_ball
    have ha_pos : 0 < ‖a‖ := norm_pos_iff.2 ha
    nlinarith
  have huy : u y ≠ 0 := mul_ne_zero (inv_ne_zero ha) hy0
  calc planarNewtonianKernel a + planarNewtonianKernel (u y)
      = planarNewtonianKernel (a * u y) := (planarNewtonianKernel_mul ha huy).symm
    _ = planarNewtonianKernel y := by simp [u, mul_inv_cancel_left₀ ha]

/-- **The exterior multipole expansion of the planar Newtonian kernel.** There is a constant
`0 < c < 1` such that for every pole `x ≠ 0` the function `y ↦ G(x - y)` has a power series
`∑ₖ Pₖ` at the origin converging on the ball of radius `c ‖x‖`, whose homogeneous terms
`Pₖ(y) = pₖ (y, …, y)` are harmonic on all of `ℂ`. -/
theorem exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel_sub :
    ∃ c : ℝ≥0, 0 < c ∧ c < 1 ∧ ∀ x : ℂ, x ≠ 0 →
      ∃ p : FormalMultilinearSeries ℝ ℂ ℝ,
        HasFPowerSeriesOnBall (fun y ↦ planarNewtonianKernel (x - y)) p 0 (c * ‖x‖₊) ∧
          ∀ k z, HarmonicAt (fun y ↦ p k fun _ ↦ y) z := by
  obtain ⟨c, hc, hc1, hser⟩ := exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel
  refine ⟨c, hc, hc1, fun x hx ↦ ?_⟩
  obtain ⟨p, hp⟩ := hser (-x) (neg_ne_zero.2 hx)
  have hfun : (fun y ↦ planarNewtonianKernel (y - x)) = fun y ↦ planarNewtonianKernel (x - y) := by
    funext y
    exact planarNewtonianKernel_sub_comm y x
  have hp0 : HasFPowerSeriesOnBall (fun y ↦ planarNewtonianKernel (x - y)) p 0 (c * ‖x‖₊) := by
    simpa [hfun] using hp.comp_sub x
  refine ⟨p, hp0, fun k z ↦ hp0.hasFPowerSeriesAt.harmonicAt_apply ?_ k z⟩
  simpa [hfun] using harmonicAt_planarNewtonianKernel_sub (Ne.symm hx : (0 : ℂ) ≠ x)

/-- **Harmonic approximation of the planar Newtonian kernel with a distant pole.** There is a
constant `0 < c < 1` such that for every pole `x ≠ 0` there is a sequence of globally harmonic
functions `P N : ℂ → ℝ` whose iterated derivatives of every order `k` converge uniformly on the
closed ball of radius `c ‖x‖` about the origin to the `k`-th iterated derivative of
`y ↦ G(x - y)`. -/
theorem exists_harmonicAt_tendstoUniformlyOn_iteratedFDeriv_planarNewtonianKernel_sub :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : ℂ, x ≠ 0 →
      ∃ P : ℕ → ℂ → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ planarNewtonianKernel (x - y)) atTop
          (closedBall 0 (c * ‖x‖)) := by
  obtain ⟨c, hc, hc1, hser⟩ := exists_forall_hasFPowerSeriesOnBall_planarNewtonianKernel_sub
  have hc1' : (c : ℝ) < 1 := mod_cast hc1
  refine ⟨c / 2, by positivity, by linarith, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, hharm⟩ := hser x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hP (N : ℕ) : HarmonicOnNhd (p.partialSum N) univ :=
    fun z _ ↦ HarmonicAt.sum fun k _ ↦ hharm k z
  -- The kernel is harmonic on the ball of convergence, which excludes the pole since `c < 1`.
  have hG : HarmonicOnNhd (fun y ↦ planarNewtonianKernel (x - y)) (ball 0 (c * ‖x‖)) := by
    intro y hy
    have hyx : y ≠ x := by
      rintro rfl
      rw [mem_ball_zero_iff] at hy
      nlinarith
    have hfun :
        (fun z ↦ planarNewtonianKernel (z - x)) = fun z ↦ planarNewtonianKernel (x - z) := by
      funext z
      exact planarNewtonianKernel_sub_comm z x
    simpa [hfun] using harmonicAt_planarNewtonianKernel_sub hyx
  refine ⟨p.partialSum, fun N z ↦ hP N z (mem_univ z), fun k ↦ ?_⟩
  have hlim := hp.tendstoLocallyUniformlyOn
  rw [← ENNReal.coe_mul, Metric.eball_coe, NNReal.coe_mul, coe_nnNorm] at hlim
  simp only [zero_add] at hlim
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1
    (hlim.iteratedFDeriv_of_harmonicOnNhd (.of_forall fun N ↦ (hP N).mono (subset_univ _))
      hG isOpen_ball k) _ (closedBall_subset_ball ?_) (isCompact_closedBall 0 _)
  have : (0 : ℝ) < c * ‖x‖ := mul_pos (mod_cast hc) hx'
  linarith

end TauCeti
