/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.IteratedFDeriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Taylor

/-!
# The exterior multipole expansion of the Newtonian kernel

The Newtonian kernel `Gₙ(y) = (n (n - 2) ωₙ)⁻¹ ‖y‖²⁻ⁿ` is real analytic away from its pole, and
its power series at a point `a ≠ 0` converges on a ball whose radius is a fixed multiple `c ‖a‖`,
with `0 < c < 1`, so that the ball excludes the pole
(`TauCeti.exists_forall_hasFPowerSeriesOnBall_newtonianKernel`). The constant depends only on
the dimension: `Gₙ` is invariant under orthogonal maps and homogeneous under dilations, so every
point `a ≠ 0` is carried to a fixed unit vector by a dilation composed with a reflection, which
rescales the radius of convergence by `‖a‖`. The statements hold in every dimension; in dimension
two the totalized kernel `TauCeti.newtonianKernel 2` is zero, and the logarithmic kernel of the
plane is not treated here.

Expanding `y ↦ Gₙ(x - y)` about the origin gives the **exterior multipole expansion**: for
`‖y‖` below a fixed multiple of `‖x‖`,

`Gₙ(x - y) = ∑ₖ Pₖ(y)`,

where `Pₖ` is a homogeneous polynomial function of degree `k` which is harmonic on the whole space
(`TauCeti.exists_forall_hasFPowerSeriesOnBall_newtonianKernel_sub`). Its terms are harmonic
because they are the Taylor terms of a harmonic function
(`HasFPowerSeriesAt.harmonicAt_apply`). Consequently, on a ball of radius a fixed multiple of
`‖x‖`, the kernel with pole `x` is the limit of the partial sums of this expansion, polynomial
functions of degree at most `N` harmonic everywhere, uniformly together with all derivatives
(`exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub`).
The convergence of the derivatives comes from the interior derivative estimates for harmonic
functions (`TendstoLocallyUniformlyOn.iteratedFDeriv_of_harmonicOnNhd`). Hence a functional on
functions on the closed ball of the approximation theorem, continuous for uniform convergence of the
derivatives up to some finite order, which annihilates the polynomial functions harmonic
everywhere, also annihilates `y ↦ Gₙ(x - y)`; this is the step at infinity in the duality proof of
harmonic Runge approximation.

## Main declarations

* `TauCeti.exists_forall_hasFPowerSeriesOnBall_newtonianKernel`: the kernel has a power series
  at each `a ≠ 0` converging on a ball of radius `c ‖a‖`, where `0 < c < 1`.
* `TauCeti.exists_forall_hasFPowerSeriesOnBall_newtonianKernel_sub`: the exterior multipole
  expansion `Gₙ(x - y) = ∑ₖ Pₖ(y)` with harmonic homogeneous terms.
* `exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub`:
  approximation of the kernel with a distant pole by polynomial functions harmonic everywhere,
  uniformly with all derivatives.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapters 5 and 10.
* O. D. Kellogg, *Foundations of Potential Theory*, Chapter V.
-/

public section

open Filter InnerProductSpace Metric Set Topology
open scoped NNReal ENNReal

namespace TauCeti

/-- **The Newtonian kernel has power series on balls proportional to the distance to the pole.**
There is a constant `0 < c < 1`, depending only on the dimension, such that at every point
`a ≠ 0` the kernel `Gₙ` has a power series converging on the ball of radius `c ‖a‖` about `a`. -/
theorem exists_forall_hasFPowerSeriesOnBall_newtonianKernel (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ c < 1 ∧ ∀ a : EuclideanSpace ℝ (Fin n), a ≠ 0 →
      ∃ p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ,
        HasFPowerSeriesOnBall (newtonianKernel n) p a (c * ‖a‖₊) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1 / 2, by norm_num, by norm_num, fun a ha ↦ absurd (Subsingleton.elim a 0) ha⟩
  -- A power series at a fixed unit vector `e`.
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; exact one_ne_zero)
  obtain ⟨p, r, hpr⟩ := (harmonicAt_newtonianKernel n he0).analyticAt
  obtain ⟨c, hc0, hcr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hpr.r_pos one_pos)
  refine ⟨c, mod_cast hc0, mod_cast (lt_min_iff.1 hcr).2, fun a ha ↦ ?_⟩
  -- The map `u = ‖a‖⁻¹ • Q`, with `Q` the reflection exchanging `e` and `a / ‖a‖`, sends `a` to
  -- `e`, and `Gₙ = ‖a‖ ^ (2 - n) • (Gₙ ∘ u)`.
  set s : ℝ := ‖a‖
  have hs : 0 < s := norm_pos_iff.2 ha
  set Q := (ℝ ∙ (e - s⁻¹ • a))ᗮ.reflection
  have hQ : Q e = s⁻¹ • a := Submodule.reflection_sub (by rw [he, norm_smul, norm_inv,
    norm_norm, inv_mul_cancel₀ hs.ne'])
  set u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    s⁻¹ • Q.toLinearIsometry.toContinuousLinearMap
  have hu_apply (y : EuclideanSpace ℝ (Fin n)) : u y = Q (s⁻¹ • y) := by
    simp [u, map_smul]
  have hua : u a = e := by
    rw [hu_apply, ← hQ, Submodule.reflection_reflection]
  have hG : s ^ (2 - (n : ℝ)) • (newtonianKernel n ∘ u) = newtonianKernel n := by
    funext y
    rw [Pi.smul_apply, Function.comp_apply, hu_apply, newtonianKernel_map_linearIsometryEquiv,
      newtonianKernel_smul, norm_inv, Real.norm_of_nonneg hs.le, Real.inv_rpow hs.le,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs _).ne', one_mul]
  have hu : ‖u‖₊ ≤ ‖a‖₊⁻¹ := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_inv, coe_nnNorm]
    refine (norm_smul_le s⁻¹ Q.toLinearIsometry.toContinuousLinearMap).trans ?_
    rw [norm_inv, norm_norm]
    exact mul_le_of_le_one_right (by positivity) (LinearIsometry.norm_toContinuousLinearMap_le _)
  have hser := ((hua ▸ hpr).compContinuousLinearMap).const_smul (c := s ^ (2 - (n : ℝ)))
  rw [hG] at hser
  have ha' : (‖a‖₊ : ℝ≥0∞) ≠ 0 := by simpa using ha
  refine ⟨_, hser.mono (ENNReal.mul_pos (ENNReal.coe_ne_zero.2 (by simpa using hc0.ne')) ha') ?_⟩
  -- The radius `r / ‖u‖ₑ` is at least `c ‖a‖`, as `‖u‖ ≤ ‖a‖⁻¹`.
  rw [ENNReal.le_div_iff_mul_le (Or.inr hpr.r_pos.ne') (Or.inl eNorm_ne_top)]
  calc (c : ℝ≥0∞) * ‖a‖₊ * ‖u‖ₑ ≤ c * ‖a‖₊ * (‖a‖₊ : ℝ≥0∞)⁻¹ := by
        gcongr
        rw [← ofReal_norm, ← coe_nnNorm, ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_inv
          (by simpa using ha)]
        exact ENNReal.coe_le_coe.2 hu
    _ = c := by rw [mul_assoc, ENNReal.mul_inv_cancel ha' ENNReal.coe_ne_top, mul_one]
    _ ≤ r := (lt_min_iff.1 hcr).1.le

/-- **The exterior multipole expansion of the Newtonian kernel.** There is a constant
`0 < c < 1`, depending only on the dimension, such that for every pole `x ≠ 0` the function
`y ↦ Gₙ(x - y)` has a power series `∑ₖ Pₖ` at the origin converging on the ball of radius
`c ‖x‖`, whose homogeneous terms `Pₖ(y) = pₖ (y, …, y)` are harmonic on the whole space. -/
theorem exists_forall_hasFPowerSeriesOnBall_newtonianKernel_sub (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ c < 1 ∧ ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      ∃ p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ,
        HasFPowerSeriesOnBall (fun y ↦ newtonianKernel n (x - y)) p 0 (c * ‖x‖₊) ∧
          ∀ k z, HarmonicAt (fun y ↦ p k fun _ ↦ y) z := by
  obtain ⟨c, hc, hc1, hser⟩ := exists_forall_hasFPowerSeriesOnBall_newtonianKernel n
  refine ⟨c, hc, hc1, fun x hx ↦ ?_⟩
  obtain ⟨p, hp⟩ := hser (-x) (neg_ne_zero.2 hx)
  have hfun : (fun y ↦ newtonianKernel n (y - x)) = fun y ↦ newtonianKernel n (x - y) := by
    funext y
    exact newtonianKernel_sub_comm n y x
  have hp0 : HasFPowerSeriesOnBall (fun y ↦ newtonianKernel n (x - y)) p 0 (c * ‖x‖₊) := by
    simpa [hfun] using hp.comp_sub x
  refine ⟨p, hp0, fun k z ↦ hp0.hasFPowerSeriesAt.harmonicAt_apply ?_ k z⟩
  simpa [hfun] using harmonicAt_newtonianKernel_sub n (Ne.symm hx : (0 : _) ≠ x)

/-- **Harmonic polynomial approximation of the Newtonian kernel with a distant pole.** There is a
constant `0 < c < 1`, depending only on the dimension, such that for every pole `x ≠ 0` there are
functions `P N`, harmonic on the whole space and polynomial of degree at most `N`, whose iterated
derivatives of every order `k` converge uniformly on the closed ball of radius `c ‖x‖` about the
origin to the `k`-th iterated derivative of `y ↦ Gₙ(x - y)`. -/
theorem
    exists_harmonicAt_mem_polynomialsDegLE_tendstoUniformlyOn_iteratedFDeriv_newtonianKernel_sub
    (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      ∃ P : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, (∀ N z, HarmonicAt (P N) z) ∧
        (∀ N, P N ∈ polynomialsDegLE (Fin n) N) ∧
        ∀ k : ℕ, TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (P N))
          (iteratedFDeriv ℝ k fun y ↦ newtonianKernel n (x - y)) atTop
          (closedBall 0 (c * ‖x‖)) := by
  obtain ⟨c, hc, hc1, hser⟩ := exists_forall_hasFPowerSeriesOnBall_newtonianKernel_sub n
  have hc1' : (c : ℝ) < 1 := mod_cast hc1
  refine ⟨c / 2, by positivity, by linarith, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, hharm⟩ := hser x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hP (N : ℕ) : HarmonicOnNhd (p.partialSum N) univ :=
    fun z _ ↦ HarmonicAt.sum fun k _ ↦ hharm k z
  -- The kernel is harmonic on the ball of convergence, which excludes the pole since `c < 1`.
  have hG : HarmonicOnNhd (fun y ↦ newtonianKernel n (x - y)) (ball 0 (c * ‖x‖)) := by
    intro y hy
    have hyx : y ≠ x := by
      rintro rfl
      rw [mem_ball_zero_iff] at hy
      nlinarith
    have hfun : (fun z ↦ newtonianKernel n (z - x)) = fun z ↦ newtonianKernel n (x - z) := by
      funext z
      exact newtonianKernel_sub_comm n z x
    simpa [hfun] using harmonicAt_newtonianKernel_sub n hyx
  refine ⟨p.partialSum, fun N z ↦ hP N z (mem_univ z), fun N ↦ ?_, fun k ↦ ?_⟩
  · have hsum : p.partialSum N = ∑ k ∈ Finset.range N, fun y ↦ p k fun _ ↦ y := by
      ext y
      simp [FormalMultilinearSeries.partialSum]
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk ↦
      polynomialsDegLE_mono (Fin n) (Finset.mem_range.1 hk).le ?_
    simpa using (p k).toMultilinearMap.apply_const_mem_polynomialsDegLE
  · have hlim := hp.tendstoLocallyUniformlyOn
    rw [← ENNReal.coe_mul, Metric.eball_coe, NNReal.coe_mul, coe_nnNorm] at hlim
    simp only [zero_add] at hlim
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1
      (hlim.iteratedFDeriv_of_harmonicOnNhd (.of_forall fun N ↦ (hP N).mono (subset_univ _))
        hG isOpen_ball k) _ (closedBall_subset_ball ?_) (isCompact_closedBall 0 _)
    have : (0 : ℝ) < c * ‖x‖ := mul_pos (mod_cast hc) hx'
    linarith

end TauCeti
