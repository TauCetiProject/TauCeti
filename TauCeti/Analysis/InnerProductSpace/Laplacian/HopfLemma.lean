/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple
import TauCeti.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Hopf's boundary-point lemma

The weak maximum principles of `TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple`
and `TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple` bound a subsolution
on a compact set by its frontier values; with a zeroth-order term `c ≥ 0`, by a nonnegative upper
bound of its frontier values.  This file proves the complementary *local* statement at a
point where such a bound is attained: **Hopf's boundary-point lemma**, for the operator
`-Δ - b·∇ + c` with bounded drift `b` and bounded nonnegative zeroth-order coefficient `c`, and in
particular for the Laplacian.

Let `B = ball y R` be a ball, let `e` be a unit vector, and let `x₀ = y + R • e` be the point
where the outward ray in direction `e` meets the sphere `∂B`.  If `u` is continuous on
`closedBall y R`, twice continuously differentiable on `B`, and differentiable at `x₀`, satisfies
`c u ≤ Δ u + ⟪b, ∇u⟫` on `B` with `‖b‖ ≤ β` and `0 ≤ c ≤ γ`, is nonnegative at `x₀`, and stays
strictly below the value `u x₀` inside `B` while staying weakly below it on `∂B`, then `u` leaves
`x₀` in the direction `e` at a strictly positive rate `0 < fderiv ℝ u x₀ e`.  The sign condition
`0 ≤ u x₀` is the usual one for a zeroth-order term; for the Laplacian (`b = 0`, `c = 0`) it is
removed by subtracting a constant, and the classical form of the lemma, in which `u x₀` is a strict
maximum over the whole closed ball, follows as a corollary.

The strict inequality inside the ball is what the lemma consumes: the sphere touching at `x₀`
forces a one-sided bound on the derivative.  The proof is the classical barrier argument.  On the
closed annulus `R / 2 ≤ ‖x - y‖ ≤ R` one perturbs `u` by a positive multiple of the radial
barrier `w x = ‖x - y‖ ^ p - R ^ p` with `p < 0`, which vanishes on the outer sphere — so the
perturbation still respects the maximum bound there — and is bounded above on the inner sphere,
where the strict inequality of the hypothesis leaves a margin.  With `r = ‖x - y‖`,

`Δ w + ⟪b, ∇w⟫ = p r ^ (p - 2) (p + dim E - 2 + ⟪x - y, b⟫)`,

so the choice `p = -(dim E + β R + γ R²)` makes `w` a subsolution, `c w ≤ Δ w + ⟪b, ∇w⟫`, on the
annulus, and the weak maximum principle for `-Δ - b·∇ + c` applies to the perturbation.  Letting
the inward ray parameter tend to zero and differentiating the resulting one-sided bound at `x₀`
gives the claim.

## Main declarations

* `TauCeti.fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere`: **Hopf's
  boundary-point lemma** for `-Δ - b·∇ + c`.
* `TauCeti.fderiv_neg_of_laplacian_add_fderiv_le_mul_of_gt_ball_of_ge_sphere`: its minimum form,
  for supersolutions.
* `TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere`: Hopf's lemma for subharmonic
  functions, with a strict bound in the ball and a weak bound on the sphere.
* `TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_closedBall`: the classical form of the lemma, in
  which the value at the boundary point is a strict maximum over the closed ball.
* `TauCeti.fderiv_neg_of_laplacian_nonpos_of_gt_ball_of_ge_sphere`: the minimum form with a weak
  inequality on the sphere.
* `TauCeti.fderiv_neg_of_laplacian_nonpos_of_gt_closedBall`: the superharmonic mirror image, for
  a strict minimum.
* `TauCeti.fderiv_pos_of_harmonicOnNhd_of_lt_closedBall`: the harmonic case of the lemma.
* `TauCeti.fderiv_neg_of_harmonicOnNhd_of_gt_closedBall`: the harmonic minimum form.

## References

L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.4.2 (Hopf's lemma);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Lemma 3.4.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian Metric Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **Hopf barrier** through the sphere of radius `R` about `y`, with exponent `p`: the radial
function `x ↦ ‖x - y‖ ^ p - R ^ p`, which vanishes on that sphere.  It is the comparison function
of the Hopf boundary-point lemma: when `R > 0` and `p < 0`, it is positive at points satisfying
`0 < ‖x - y‖ < R`.  Its Laplacian is
`p (p + dim E - 2) ‖x - y‖ ^ (p - 2)`, which is nonnegative off the pole once `p ≤ 2 - dim E`.
-/
private def hopfBarrier (y : E) (R p : ℝ) : E → ℝ := fun x ↦ ‖x - y‖ ^ p - R ^ p

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The barrier vanishes on its defining sphere. -/
private theorem hopfBarrier_eq_zero_of_mem_sphere {y : E} {R p : ℝ} {x : E}
    (hx : x ∈ sphere y R) : hopfBarrier y R p x = 0 := by
  simp only [hopfBarrier, mem_sphere_iff_norm.mp hx, sub_self]

/-- The Laplacian of the barrier away from its pole: the radial formula
`TauCeti.laplacian_norm_rpow_of_ne`, transported to the translated pole `y` by the translation
invariance `TauCeti.laplacian_comp_add_right`. -/
private theorem laplacian_hopfBarrier (y : E) (R p : ℝ) {x : E} (hx : x ≠ y) :
    Δ (hopfBarrier y R p) x =
      p * (p + (Module.finrank ℝ E : ℝ) - 2) * ‖x - y‖ ^ (p - 2) := by
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hx
  have hpow : ContDiffAt ℝ 2 (fun z : E ↦ ‖z - y‖ ^ p) x :=
    (contDiffAt_norm ℝ (x := x - y) hne).comp x (by fun_prop) |>.rpow_const_of_ne
      (by simpa only [Function.comp_apply, norm_ne_zero_iff] using hne)
  have htrans : Δ (fun z : E ↦ ‖z - y‖ ^ p) x = Δ (fun z : E ↦ ‖z‖ ^ p) (x - y) := by
    have h := congrFun (laplacian_comp_add_right (fun z : E ↦ ‖z‖ ^ p) (-y)) x
    simpa only [Pi.sub_apply, add_neg_cancel_right, sub_eq_add_neg] using h
  have hBarrier : hopfBarrier y R p = (fun z : E ↦ ‖z - y‖ ^ p) - fun _ : E ↦ R ^ p := rfl
  rw [hBarrier]
  rw [hpow.laplacian_sub contDiffAt_const, laplacian_const, Pi.zero_apply, sub_zero, htrans,
    laplacian_norm_rpow_of_ne p hne]

omit [FiniteDimensional ℝ E] in
/-- The barrier is twice continuously differentiable away from its pole. -/
private theorem contDiffAt_hopfBarrier {y : E} {R p : ℝ} {x : E} (hx : x ≠ y) :
    ContDiffAt ℝ 2 (hopfBarrier y R p) x := by
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hx
  have h : ContDiffAt ℝ 2 (fun z : E ↦ ‖z - y‖ ^ p - R ^ p) x :=
    (((contDiffAt_norm ℝ (x := x - y) hne).comp x (by fun_prop)).rpow_const_of_ne
      (by simpa only [Function.comp_apply, norm_ne_zero_iff] using hne)).sub contDiffAt_const
  exact h

omit [FiniteDimensional ℝ E] in
/-- The derivative of the barrier away from its pole: `p ‖x - y‖ ^ (p - 2) ⟪x - y, ·⟫`. -/
private theorem hasFDerivAt_hopfBarrier (y : E) (R p : ℝ) {x : E} (hx : x ≠ y) :
    HasFDerivAt (hopfBarrier y R p) ((p * ‖x - y‖ ^ (p - 2)) • innerSL ℝ (x - y)) x := by
  have h := (hasFDerivAt_norm_rpow_of_ne p (sub_ne_zero.mpr hx)).comp x
    ((hasFDerivAt_id x).sub_const y)
  exact (h.sub_const (R ^ p)).congr_fderiv (ContinuousLinearMap.comp_id _)

/-- Inside the closed ball, away from the pole, the barrier is a subsolution of `-Δ - b·∇ + c`
once its exponent is negative enough: if `‖v‖ ≤ β`, `0 ≤ c ≤ γ` and
`p ≤ -(dim E + β R + γ R²)`, then `c w ≤ Δ w + ⟪∇w, v⟫` at `x`. -/
private theorem mul_hopfBarrier_le_laplacian_add_fderiv [Nontrivial E] {y x v : E}
    {R p β γ c : ℝ} (hx : x ≠ y) (hxR : ‖x - y‖ ≤ R) (hv : ‖v‖ ≤ β) (hc : 0 ≤ c) (hcγ : c ≤ γ)
    (hp : p ≤ -((Module.finrank ℝ E : ℝ) + β * R + γ * R ^ 2)) :
    c * hopfBarrier y R p x ≤
      Δ (hopfBarrier y R p) x + fderiv ℝ (hopfBarrier y R p) x v := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hR : 0 < R := hr.trans_le hxR
  have hn : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have hγ : 0 ≤ γ := hc.trans hcγ
  have hβ : 0 ≤ β := (norm_nonneg v).trans hv
  rw [laplacian_hopfBarrier y R p hx, (hasFDerivAt_hopfBarrier y R p hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  set A := ‖x - y‖ ^ (p - 2) with hAdef
  have hA : 0 < A := Real.rpow_pos_of_pos hr _
  -- The zeroth-order term is at most `γ R² A`, because `w ≤ ‖x - y‖ ^ p = ‖x - y‖ ^ 2 * A`.
  have hrp : ‖x - y‖ ^ p = ‖x - y‖ ^ 2 * A := by
    rw [hAdef, ← Real.rpow_two, ← Real.rpow_add hr]
    ring_nf
  have hw : hopfBarrier y R p x ≤ ‖x - y‖ ^ 2 * A := by
    rw [hopfBarrier, ← hrp]
    linarith [Real.rpow_pos_of_pos hR p]
  have hr2 : ‖x - y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr.le hxR 2
  have hlhs : c * hopfBarrier y R p x ≤ γ * R ^ 2 * A := by
    calc c * hopfBarrier y R p x ≤ c * (‖x - y‖ ^ 2 * A) := mul_le_mul_of_nonneg_left hw hc
      _ ≤ γ * (R ^ 2 * A) :=
        mul_le_mul hcγ (mul_le_mul_of_nonneg_right hr2 hA.le) (by positivity) hγ
      _ = γ * R ^ 2 * A := by ring
  -- The drift term is at least `p A R β`, by Cauchy–Schwarz.
  have hinner : ⟪x - y, v⟫_ℝ ≤ R * β :=
    (real_inner_le_norm _ _).trans (mul_le_mul hxR hv (norm_nonneg _) hR.le)
  -- With `q = -p ≥ 1`, the operator value is `A q (q - dim E + 2 - ⟪x - y, v⟫) ≥ A (γ R² + 2)`.
  have hq : 1 ≤ -p := by nlinarith [mul_nonneg hβ hR.le, mul_nonneg hγ (sq_nonneg R)]
  have hbracket : γ * R ^ 2 + 2 ≤ -p - Module.finrank ℝ E + 2 - ⟪x - y, v⟫_ℝ := by linarith
  have hprod : γ * R ^ 2 + 2 ≤ -p * (-p - Module.finrank ℝ E + 2 - ⟪x - y, v⟫_ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by positivity : (0 : ℝ) ≤ γ * R ^ 2 + 2)]
  have hrhs : A * (γ * R ^ 2 + 2) ≤
      p * (p + Module.finrank ℝ E - 2) * A + p * A * ⟪x - y, v⟫_ℝ := by
    have h := mul_le_mul_of_nonneg_left hprod hA.le
    linarith
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- The derivative step of Hopf's lemma: if a positive multiple of the barrier with negative
exponent can be added to `u` without exceeding `u x₀` along the inward ray from
`x₀ = y + R • e`, then the outward derivative of `u` at `x₀` is positive. -/
private theorem fderiv_pos_of_add_mul_hopfBarrier_le {u : E → ℝ} {y e : E} {R p ε δ : ℝ}
    (hR : 0 < R) (he : ‖e‖ = 1) (hp : p < 0) (hε : 0 < ε) (hδ : 0 < δ)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hray : ∀ h ∈ Set.Ioc (0 : ℝ) δ,
      u (y + R • e - h • e) + ε * hopfBarrier y R p (y + R • e - h • e) ≤ u (y + R • e)) :
    0 < fderiv ℝ u (y + R • e) e := by
  set x₀ : E := y + R • e with hx₀def
  have hnorm_sub : ∀ {h : ℝ}, h < R → ‖(x₀ - h • e) - y‖ = R - h := by
    intro h hh
    have hsub : (x₀ - h • e) - y = (R - h) • e := by
      rw [hx₀def, sub_smul]
      abel
    rw [hsub, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (by linarith)]
  set F : ℝ → ℝ := fun h ↦ u x₀ - u (x₀ - h • e) - ε * hopfBarrier y R p (x₀ - h • e)
    with hFdef
  have hF0 : F 0 = 0 := by
    have hz : hopfBarrier y R p x₀ = 0 := by
      have h := hnorm_sub (h := 0) hR
      rw [zero_smul, sub_zero, sub_zero] at h
      exact hopfBarrier_eq_zero_of_mem_sphere (mem_sphere_iff_norm.mpr h)
    simp only [hFdef, zero_smul, sub_zero, hz, mul_zero, sub_self]
  -- The derivative of `u` along the inward ray at `x₀`.
  have hline : HasDerivAt (fun h : ℝ ↦ x₀ - h • e) (-e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub x₀
  have h1 : HasDerivAt (fun h : ℝ ↦ u (x₀ - h • e)) (-(fderiv ℝ u x₀ e)) 0 := by
    have h := hderiv.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline (by simp)
    rwa [map_neg] at h
  -- The derivative of the barrier along the inward ray at `x₀`.
  have h2 : HasDerivAt (fun h : ℝ ↦ hopfBarrier y R p (x₀ - h • e)) (-p * R ^ (p - 1)) 0 := by
    have hs : HasDerivAt (fun h : ℝ ↦ R - h) (-1) 0 := by
      simpa using HasDerivAt.const_sub R (hasDerivAt_id (0 : ℝ))
    have hbase : HasDerivAt (fun h : ℝ ↦ (R - h) ^ p - R ^ p) (p * R ^ (p - 1) * (-1)) 0 := by
      have hcomp := (Real.hasDerivAt_rpow_const (x := R) (p := p) (Or.inl hR.ne')).comp_of_eq
        (h := fun h : ℝ ↦ R - h) (x := 0) hs (by simp)
      simpa only [Function.comp_apply] using hcomp.sub_const (R ^ p)
    have hev : (fun h : ℝ ↦ hopfBarrier y R p (x₀ - h • e)) =ᶠ[𝓝 0]
        (fun h : ℝ ↦ (R - h) ^ p - R ^ p) := by
      filter_upwards [eventually_lt_nhds hR] with h hh
      rw [hopfBarrier, hnorm_sub hh]
    simpa only [mul_neg, mul_one, neg_mul] using hbase.congr_of_eventuallyEq hev
  have hFderiv : HasDerivAt F (fderiv ℝ u x₀ e - ε * (-p * R ^ (p - 1))) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (u x₀)).sub h1).sub (h2.const_mul ε)
    rw [sub_neg_eq_add, zero_add] at h
    exact h.congr_of_eventuallyEq (.of_forall fun _ ↦ rfl)
  -- `F ≥ 0` to the right of `0`, so its right derivative at `0` is nonnegative.
  have hslope : Tendsto (fun h : ℝ ↦ h⁻¹ * F h) (𝓝[>] (0 : ℝ))
      (𝓝 (fderiv ℝ u x₀ e - ε * (-p * R ^ (p - 1)))) := by
    simpa only [zero_add, hF0, sub_zero, smul_eq_mul] using hFderiv.tendsto_slope_zero_right
  have hslope_nonneg : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ h⁻¹ * F h := by
    filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    have := hray h hh
    exact mul_nonneg (inv_nonneg.mpr hh.1.le) (by simp only [hFdef]; linarith)
  have hkey : 0 ≤ fderiv ℝ u x₀ e - ε * (-p * R ^ (p - 1)) := ge_of_tendsto hslope hslope_nonneg
  have hεpos' : 0 < ε * (-p * R ^ (p - 1)) :=
    mul_pos hε (mul_pos (by linarith) (Real.rpow_pos_of_pos hR _))
  linarith

/-- **Hopf's boundary-point lemma for `-Δ - b·∇ + c`.** Let `B = ball y R` be a ball in a
finite-dimensional real inner product space, let `e` be a unit vector, and let `x₀ = y + R • e` be
the point where the outward ray in direction `e` meets the sphere `∂B`. Let the drift satisfy
`‖b‖ ≤ β` and the zeroth-order coefficient `0 ≤ c ≤ γ` on `B`. If `u` is continuous on
`closedBall y R`, twice continuously differentiable on `B`, and differentiable at `x₀`, is a
subsolution `c u ≤ Δ u + ⟪b, ∇u⟫` on `B`, is nonnegative at `x₀`, and stays strictly below the
value `u x₀` inside `B` and weakly below it on the sphere `∂B`, then `u` leaves `x₀` in the
direction `e` at a strictly positive rate: `0 < fderiv ℝ u x₀ e`.

The sign condition `0 ≤ u x₀` is needed only because of `c`; for `c = 0` it can be arranged by
subtracting the constant `u x₀`, as in
`TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere`. -/
theorem fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere {u c : E → ℝ}
    {b : E → E} {y e : E} {R β γ : ℝ} (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ Δ u x + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u (y + R • e))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e))
    (hle : ∀ x ∈ sphere y R, u x ≤ u (y + R • e)) :
    0 < fderiv ℝ u (y + R • e) e := by
  -- The outward normal is a nonzero vector, so `E` is nontrivial and has positive dimension.
  have he0 : e ≠ 0 := by
    rintro rfl
    norm_num at he
  let _ : Nontrivial E := ⟨e, 0, he0⟩
  have hdim : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hb y (mem_ball_self hR))
  have hγ : 0 ≤ γ := (hc y (mem_ball_self hR)).trans (hcγ y (mem_ball_self hR))
  set x₀ : E := y + R • e with hx₀def
  -- The barrier exponent, negative enough for `mul_hopfBarrier_le_laplacian_add_fderiv`.
  set p : ℝ := -((Module.finrank ℝ E : ℝ) + β * R + γ * R ^ 2) with hpdef
  have hpneg : p < 0 := by
    rw [hpdef]
    nlinarith [mul_nonneg hβ hR.le, mul_nonneg hγ (sq_nonneg R)]
  have hhalfpos : (0 : ℝ) < R / 2 := by linarith
  -- The inner sphere carries a uniform positive margin below the maximum `u x₀`.
  obtain ⟨z, hzball, hzmax⟩ := (isCompact_closedBall y (R / 2)).exists_isMaxOn
    (nonempty_closedBall.mpr hhalfpos.le)
    (hucont.mono (closedBall_subset_closedBall (by linarith)))
  have hzlt : u z < u x₀ := hlt z (closedBall_subset_ball (by linarith) hzball)
  set δ : ℝ := u x₀ - u z with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith
  have hsphere_le : ∀ w ∈ sphere y (R / 2), u w ≤ u x₀ - δ := by
    intro w hw
    have hwz : u w ≤ u z := hzmax (sphere_subset_closedBall hw)
    rw [hδdef]
    linarith
  -- The closed annulus on which the barrier is controlled.
  set K : Set E := closedBall y R \ ball y (R / 2) with hKdef
  have hKsub : K ⊆ closedBall y R := sdiff_subset
  have hKcompact : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closedBall.sdiff isOpen_ball, isBounded_closedBall.subset hKsub⟩
  have hKnorm : ∀ w ∈ K, R / 2 ≤ ‖w - y‖ ∧ ‖w - y‖ ≤ R := by
    intro w hw
    simp only [hKdef, Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm] at hw
    exact ⟨not_lt.mp hw.2, hw.1⟩
  have hKne : ∀ w ∈ K, w ≠ y := by
    intro w hw h
    have h1 := (hKnorm w hw).1
    rw [h, sub_self, norm_zero] at h1
    linarith
  have hKball : ∀ w ∈ interior K, w ∈ ball y R := by
    intro w hw
    have h1 : w ∈ interior (closedBall y R) := interior_mono hKsub hw
    rwa [interior_closedBall y hR.ne'] at h1
  -- `K` has the open annulus as interior, so a frontier point is either on the outer sphere or
  -- on the inner sphere.
  have hannulus_int : ball y R \ closedBall y (R / 2) ⊆ interior K :=
    interior_maximal (fun w hw ↦ by
      rw [hKdef, Set.mem_sdiff]
      exact ⟨ball_subset_closedBall hw.1, fun h ↦ hw.2 (ball_subset_closedBall h)⟩)
      (isOpen_ball.inter isClosed_closedBall.isOpen_compl)
  -- The perturbation coefficient: small enough that the barrier dominates the margin.
  set ε : ℝ := δ / (2 * (R / 2) ^ p) with hεdef
  have hhalfpow : 0 < (R / 2) ^ p := Real.rpow_pos_of_pos hhalfpos p
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact div_pos hδpos (by positivity)
  have hεbound : ε * (R / 2) ^ p = δ / 2 := by
    rw [hεdef]
    field_simp
  set v : E → ℝ := fun w ↦ u w + ε * hopfBarrier y R p w with hvdef
  have hvcont : ContinuousOn v K := by
    intro w hw
    simp only [hvdef]
    exact (hucont w (hKsub hw)).mono hKsub |>.add
      ((contDiffAt_hopfBarrier (hKne w hw)).continuousAt.continuousWithinAt.const_mul ε)
  have hvcd : ∀ ⦃w⦄, w ∈ interior K → ContDiffAt ℝ 2 v w := fun w hw ↦
    (huinterior w (hKball w hw)).add
      ((contDiffAt_hopfBarrier (hKne w (interior_subset hw))).const_smul ε)
  -- The perturbation is still a subsolution on the open annulus.
  have hvsub : ∀ ⦃w⦄, w ∈ interior K → c w * v w ≤ Δ v w + fderiv ℝ v w (b w) := by
    intro w hw
    have hwK : w ∈ K := interior_subset hw
    have hne : w ≠ y := hKne w hwK
    have hwball : w ∈ ball y R := hKball w hw
    have hcd : ContDiffAt ℝ 2 (fun z : E ↦ ε * hopfBarrier y R p z) w :=
      (contDiffAt_hopfBarrier (y := y) (R := R) (p := p) hne).const_smul ε
    have hlapv : Δ v w = Δ u w + ε * Δ (hopfBarrier y R p) w := by
      have hfun : (fun z : E ↦ ε * hopfBarrier y R p z) = ε • hopfBarrier y R p := by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
      have h1 : Δ (fun z : E ↦ u z + ε * hopfBarrier y R p z) w =
          Δ u w + Δ (fun z : E ↦ ε * hopfBarrier y R p z) w :=
        (huinterior w hwball).laplacian_add hcd
      rw [hvdef, h1, hfun,
        laplacian_smul ε (contDiffAt_hopfBarrier (y := y) (R := R) (p := p) hne), smul_eq_mul]
    have hderv : fderiv ℝ v w (b w) =
        fderiv ℝ u w (b w) + ε * fderiv ℝ (hopfBarrier y R p) w (b w) := by
      have hw' := hasFDerivAt_hopfBarrier y R p hne
      have h : HasFDerivAt (fun z : E ↦ u z + ε * hopfBarrier y R p z)
          (fderiv ℝ u w + ε • (p * ‖w - y‖ ^ (p - 2)) • innerSL ℝ (w - y)) w :=
        ((huinterior w hwball).differentiableAt (by norm_num)).hasFDerivAt.add (hw'.const_mul ε)
      rw [hvdef, h.fderiv, hw'.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul]
    have hbar := mul_hopfBarrier_le_laplacian_add_fderiv (v := b w) hne (hKnorm w hwK).2
      (hb w hwball) (hc w hwball) (hcγ w hwball) le_rfl
    have hbar' := mul_le_mul_of_nonneg_left hbar hεpos.le
    rw [hlapv, hderv]
    simp only [hvdef]
    nlinarith [hsub w hwball]
  have hvbdry : ∀ ⦃w⦄, w ∈ frontier K → v w ≤ u x₀ := by
    intro w hwfr
    have hwK : w ∈ K := hKcompact.isClosed.frontier_subset hwfr
    have hnrm := hKnorm w hwK
    rcases eq_or_lt_of_le hnrm.2 with houter | hinner
    · simp only [hvdef]
      rw [hopfBarrier_eq_zero_of_mem_sphere (mem_sphere_iff_norm.mpr houter), mul_zero,
        add_zero]
      exact hle w (mem_sphere_iff_norm.mpr houter)
    · have hinner' : ‖w - y‖ = R / 2 := by
        by_contra hne'
        have hlt : R / 2 < ‖w - y‖ := lt_of_le_of_ne hnrm.1 (Ne.symm hne')
        refine (mem_frontier_iff_notMem_interior hwK).mp hwfr (hannulus_int ⟨?_, ?_⟩)
        · rw [mem_ball, dist_eq_norm]
          exact hinner
        · rw [mem_closedBall, dist_eq_norm]
          exact not_le.mpr hlt
      have h1 : u w ≤ u x₀ - δ := hsphere_le w (mem_sphere_iff_norm.mpr hinner')
      have h2 : hopfBarrier y R p w ≤ (R / 2) ^ p := by
        rw [hopfBarrier, hinner']
        have := (Real.rpow_pos_of_pos hR p).le
        linarith
      have h3 : ε * hopfBarrier y R p w ≤ ε * (R / 2) ^ p :=
        mul_le_mul_of_nonneg_left h2 hεpos.le
      simp only [hvdef]
      linarith [h1, h3, hεbound]
  -- The weak maximum principle bounds the perturbation on the whole annulus, in particular
  -- along the inward ray from `x₀`.
  have hKmax : ∀ ⦃w⦄, w ∈ K → v w ≤ u x₀ :=
    le_of_mul_le_laplacian_add_fderiv_le_frontier hKcompact hnonneg hvcont hvcd
      (fun w hw ↦ hc w (hKball w hw)) (fun w hw ↦ hb w (hKball w hw)) hvsub hvbdry
  refine fderiv_pos_of_add_mul_hopfBarrier_le hR he hpneg hεpos hhalfpos hderiv fun h hh ↦
    hKmax ?_
  have hnorm : ‖(x₀ - h • e) - y‖ = R - h := by
    have hsub : (x₀ - h • e) - y = (R - h) • e := by
      rw [hx₀def, sub_smul]
      abel
    rw [hsub, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (by linarith [hh.2])]
  rw [hKdef, Set.mem_sdiff]
  simp only [mem_closedBall, mem_ball, dist_eq_norm, ← hx₀def, hnorm]
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

/-- **Hopf's boundary-point lemma for `-Δ - b·∇ + c`, minimum form.** The mirror image of
`TauCeti.fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere` for supersolutions
`Δ u + ⟪b, ∇u⟫ ≤ c u` that are nonpositive at `x₀ = y + R • e`, strictly above `u x₀` in the ball
and weakly above it on the sphere: the outward derivative at `x₀` is negative. -/
theorem fderiv_neg_of_laplacian_add_fderiv_le_mul_of_gt_ball_of_ge_sphere {u c : E → ℝ}
    {b : E → E} {y e : E} {R β γ : ℝ} (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hsuper : ∀ x ∈ ball y R, Δ u x + fderiv ℝ u x (b x) ≤ c x * u x)
    (hnonpos : u (y + R • e) ≤ 0)
    (hgt : ∀ x ∈ ball y R, u (y + R • e) < u x)
    (hge : ∀ x ∈ sphere y R, u (y + R • e) ≤ u x) :
    fderiv ℝ u (y + R • e) e < 0 := by
  have h := fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere (u := -u) hR he
    hucont.neg (fun x hx ↦ (huinterior x hx).neg) hderiv.neg hc hcγ hb
    (fun x hx ↦ by
      rw [congrFun laplacian_neg x, fderiv_neg]
      simp only [Pi.neg_apply, neg_apply, mul_neg]
      linarith [hsuper x hx])
    (neg_nonneg.mpr hnonpos) (fun x hx ↦ neg_lt_neg (hgt x hx)) (fun x hx ↦ neg_le_neg (hge x hx))
  rw [fderiv_neg] at h
  exact neg_pos.mp h

/-- **Hopf's boundary-point lemma.** Let `B = ball y R` be a ball in a finite-dimensional real
inner product space, let `e` be a unit vector, and let `x₀ = y + R • e` be the point where the
outward ray in direction `e` meets the sphere `∂B`. If `u` is continuous on `closedBall y R`, twice
continuously differentiable on `B`, and differentiable at `x₀`, is subharmonic on `B` (`0 ≤ Δ u`),
stays strictly below the value `u x₀`
inside `B` and weakly below it on the sphere `∂B`, then `u` leaves `x₀` in the direction `e` at a
strictly positive rate: `0 < fderiv ℝ u x₀ e`.

The strict inequality is needed only inside the ball, so the theorem applies directly when the
boundary sphere has merely a weak bound. The classical form, with a strict maximum over the whole
closed ball, is `TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_closedBall`. -/
theorem fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere {u : E → ℝ} {y : E} {R : ℝ}
    {e : E} (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hlap : ∀ x ∈ ball y R, 0 ≤ Δ u x)
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e))
    (hle : ∀ x ∈ sphere y R, u x ≤ u (y + R • e)) :
    0 < fderiv ℝ u (y + R • e) e := by
  -- Apply the general lemma, with `b = 0` and `c = 0`, to `u - u x₀`, which vanishes at `x₀`.
  have h := fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere
    (u := fun x ↦ u x - u (y + R • e)) (c := 0) (b := 0) (β := 0) (γ := 0) hR he
    (hucont.sub continuousOn_const) (fun x hx ↦ (huinterior x hx).sub contDiffAt_const)
    (hderiv.sub_const _) (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) (fun _ _ ↦ by simp)
    (fun x hx ↦ by
      have h1 : Δ (fun z ↦ u z - u (y + R • e)) x = Δ u x - Δ (fun _ : E ↦ u (y + R • e)) x :=
        (huinterior x hx).laplacian_sub contDiffAt_const
      simpa [h1] using hlap x hx)
    (by simp) (fun x hx ↦ sub_lt_sub_right (hlt x hx) _) (fun x hx ↦ sub_le_sub_right (hle x hx) _)
  rwa [fderiv_sub_const] at h

/-- **Hopf's boundary-point lemma, classical form.** The statement usually quoted, in which `u`
stays strictly below `u x₀` at every other point of the closed ball.  It is the specialization of
the ball-and-sphere form in which the strict inequality on the ball follows from the strict
closed-ball maximum and the sphere has the corresponding weak inequality. -/
theorem fderiv_pos_of_laplacian_nonneg_of_lt_closedBall {u : E → ℝ} {y : E} {R : ℝ} {e : E}
    (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hlap : ∀ x ∈ ball y R, 0 ≤ Δ u x)
    (hmax : ∀ x ∈ closedBall y R, x ≠ y + R • e → u x < u (y + R • e)) :
    0 < fderiv ℝ u (y + R • e) e := by
  refine fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere hR he hucont huinterior hderiv hlap
    (fun x hx ↦ hmax x (ball_subset_closedBall hx) ?_) fun x hx ↦ ?_
  · rintro rfl
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_pos hR] at hx
    exact absurd hx (lt_irrefl R)
  · by_cases h : x = y + R • e
    · rw [h]
    · exact (hmax x (sphere_subset_closedBall hx) h).le

/-- **Hopf's boundary-point lemma, minimum form.** If `u` is continuous on `closedBall y R`,
twice continuously differentiable on `ball y R`, and differentiable at `x₀`, satisfies
`Δ u ≤ 0` on the ball, has a strict minimum at `x₀` in the ball, and has a weak minimum on the
sphere, then its derivative in the outward normal direction is negative. -/
theorem fderiv_neg_of_laplacian_nonpos_of_gt_ball_of_ge_sphere {u : E → ℝ} {y : E} {R : ℝ}
    {e : E} (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hlap : ∀ x ∈ ball y R, Δ u x ≤ 0)
    (hgt : ∀ x ∈ ball y R, u (y + R • e) < u x)
    (hge : ∀ x ∈ sphere y R, u (y + R • e) ≤ u x) :
    fderiv ℝ u (y + R • e) e < 0 := by
  have h := fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere (u := -u) hR he
    hucont.neg (fun x hx ↦ (huinterior x hx).neg) hderiv.neg
    (fun x hx ↦ by
      rw [congrFun laplacian_neg x, Pi.neg_apply]
      exact neg_nonneg.mpr (hlap x hx))
    (fun x hx ↦ neg_lt_neg (hgt x hx))
    (fun x hx ↦ neg_le_neg (hge x hx))
  rw [fderiv_neg] at h
  exact neg_pos.mp h

/-- **Hopf's boundary-point lemma, minimum form.** The mirror image of
`TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_closedBall` for superharmonic functions, with a
strict minimum at `x₀ = y + R • e` over the closed ball. -/
theorem fderiv_neg_of_laplacian_nonpos_of_gt_closedBall {u : E → ℝ} {y : E} {R : ℝ} {e : E}
    (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hlap : ∀ x ∈ ball y R, Δ u x ≤ 0)
    (hmin : ∀ x ∈ closedBall y R, x ≠ y + R • e → u (y + R • e) < u x) :
    fderiv ℝ u (y + R • e) e < 0 := by
  refine fderiv_neg_of_laplacian_nonpos_of_gt_ball_of_ge_sphere hR he hucont huinterior hderiv hlap
    (fun x hx ↦ hmin x (ball_subset_closedBall hx) ?_) (fun x hx ↦ ?_)
  · rintro rfl
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_pos hR] at hx
    exact absurd hx (lt_irrefl R)
  · by_cases h : x = y + R • e
    · rw [h]
    · exact (hmin x (sphere_subset_closedBall hx) h).le

/-- **Hopf's boundary-point lemma for harmonic functions.** A harmonic function on the ball whose
value at the boundary point `x₀ = y + R • e` is a strict maximum over `closedBall y R` has
strictly positive outgoing derivative there. This is the form of the lemma used to prove the
strong maximum principle and boundary-point regularity. -/
theorem fderiv_pos_of_harmonicOnNhd_of_lt_closedBall {u : E → ℝ} {y : E} {R : ℝ} {e : E}
    (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hharm : HarmonicOnNhd u (ball y R))
    (hmax : ∀ x ∈ closedBall y R, x ≠ y + R • e → u x < u (y + R • e)) :
    0 < fderiv ℝ u (y + R • e) e :=
  fderiv_pos_of_laplacian_nonneg_of_lt_closedBall hR he hucont
    (fun x hx ↦ (hharm x hx).1) hderiv
    (fun x hx ↦ le_of_eq ((hharm x hx).2.eq_of_nhds).symm) hmax

/-- **Hopf's boundary-point lemma for harmonic functions, minimum form.** A harmonic function on
the ball whose value at the boundary point `x₀ = y + R • e` is a strict minimum on `closedBall y R`
has a strictly negative outgoing derivative there. -/
theorem fderiv_neg_of_harmonicOnNhd_of_gt_closedBall {u : E → ℝ} {y : E} {R : ℝ} {e : E}
    (hR : 0 < R) (he : ‖e‖ = 1)
    (hucont : ContinuousOn u (closedBall y R))
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hharm : HarmonicOnNhd u (ball y R))
    (hmin : ∀ x ∈ closedBall y R, x ≠ y + R • e → u (y + R • e) < u x) :
    fderiv ℝ u (y + R • e) e < 0 :=
  fderiv_neg_of_laplacian_nonpos_of_gt_closedBall hR he hucont
    (fun x hx ↦ (hharm x hx).1) hderiv
    (fun x hx ↦ le_of_eq (hharm x hx).2.eq_of_nhds) hmin

end TauCeti

end

end
