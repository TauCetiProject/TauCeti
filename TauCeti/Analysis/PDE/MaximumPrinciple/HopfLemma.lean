/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Convex.StrictConvexSpace

/-!
# Hopf's boundary-point lemma for elliptic operators in non-divergence form

Let `ℝⁿ = EuclideanSpace ℝ ι` and consider the operator in non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`

with a variable coefficient matrix `a`, elliptic with constant `λ > 0` in the sense that
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ`, with trace bounded above, `tr a(x) ≤ Λ`, and with a drift bounded by `β`.
As in `TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence`, the zeroth-order term is written on
the left: a subsolution satisfies `c u ≤ L u`, so Gilbarg and Trudinger's operator `L + c'` is the
case `c = -c'`, and their sign condition `c' ≤ 0` reads `0 ≤ c` here.

This file proves **Hopf's boundary-point lemma** (Gilbarg–Trudinger, Lemma 3.4) for this operator.
Let `B = ball y R` and let `x₀` be a point of its sphere, with outer unit normal
`ν = R⁻¹ • (x₀ - y)`. Let `u` be `C²` in `B` and continuous at `x₀` relative to `B`, with
`c u ≤ L u` in `B` for a zeroth-order coefficient bounded above by `γ`, and suppose `u x < u x₀`
for every `x ∈ B`. If `c = 0`, or `c ≥ 0` and `u x₀ ≥ 0`, or `u x₀ = 0` with no sign condition on
`c`, then the inward difference quotients of `u` at `x₀` are bounded below by a positive constant:

`ε t ≤ u x₀ - u (x₀ - t ν)` for all `0 < t < δ`.

Consequently the outer normal derivative of `u` at `x₀`, whenever it exists as a one-sided
derivative, is strictly positive. Nothing is assumed of the coefficients beyond the pointwise
bounds: no continuity, no measurability and no symmetry of `a`. The lower ellipticity bound and
the upper trace bound are the only properties of `a` used; for a field with
`TauCeti.PDE.UniformlyEllipticOn (ball y R) a λ Λ` each diagonal entry is at most `Λ`, so the
trace is at most `card ι * Λ`. The lemma applies to a domain `Ω` satisfying an interior sphere
condition at a boundary point `x₀`: take `B ⊆ Ω` with `x₀` on its sphere, and restrict the
hypotheses on `Ω` to `B`.

For `a = 1`, with `u` continuous on the closed ball and differentiable at `x₀`, the derivative
form is `TauCeti.fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere`.

## The argument

Let `z` be the midpoint of `y` and `x₀`, so that `x₀` lies on the sphere of `ball z (R / 2)` and
every other point of `closedBall z (R / 2)` lies in `B`; on this closed ball `u` is continuous.
On the annulus `R / 4 ≤ ‖x - z‖ ≤ R / 2` the Gaussian barrier
`v x = exp (-α ‖x - z‖²) - exp (-α (R / 2)²)` satisfies

`L v = (4 α² (x - z)ᵀ a (x - z) - 2 α tr a - 2 α ⟪x - z, b⟫) exp (-α ‖x - z‖²)`,

which dominates `c v` once `α` is large in terms of `λ`, `Λ`, `β`, `γ` and `R`. The function
`u - u x₀ + m v`, with `m` the margin by which `u` stays below `u x₀` on `closedBall z (R / 4)`, is
then a subsolution on the annulus that is nonpositive on its frontier, so by the weak maximum
principle `TauCeti.PDE.le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier` it is
nonpositive along the inward radius from `x₀`. The convexity of `exp` turns `m v (x₀ - t ν)` into
a linear lower bound in `t`. The three sign cases reduce to the second by replacing `c` with
its positive part `max c 0`.

## Main declarations

* `TauCeti.PDE.exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`:
  **Hopf's boundary-point lemma**, in difference-quotient form.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`:
  the outer normal derivative, when it exists, is positive.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.2, Lemma 3.4.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter Matrix Metric RealInnerProductSpace Set Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On the annulus `ρ ≤ ‖x - z‖ ≤ r`, the shifted Gaussian `exp (-α ‖· - z‖²) - C` with `C ≥ 0`
is a subsolution of `-∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ - ∂_v + c` for `0 ≤ c ≤ γ`, once
`γ + 2 α (Λ + r β) ≤ 4 α² λ ρ²`. -/
private theorem mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sq_sub
    {A : Matrix ι ι ℝ} {z x v : EuclideanSpace ℝ ι} {lam Lam β γ c ρ r α C : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (htr : A.trace ≤ Lam)
    (hv : ‖v‖ ≤ β) (hc : 0 ≤ c) (hcγ : c ≤ γ) (hρ : 0 ≤ ρ) (hxρ : ρ ≤ ‖x - z‖)
    (hxr : ‖x - z‖ ≤ r) (hα : 0 ≤ α) (hαbig : γ + 2 * α * (Lam + r * β) ≤ 4 * α ^ 2 * lam * ρ ^ 2)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C) :
    c * (Real.exp (-α * ‖x - z‖ ^ 2) - C) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y ↦ Real.exp (-α * ‖y - z‖ ^ 2) - C) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun y ↦ Real.exp (-α * ‖y - z‖ ^ 2) - C) x v := by
  rw [sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sq_sub]
  set g := Real.exp (-α * ‖x - z‖ ^ 2)
  have hg : 0 < g := Real.exp_pos _
  have hQ : lam * ρ ^ 2 ≤ A.toQuadraticForm' (x - z) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hxρ 2) hlam).trans (hA _)
  have hinner : ⟪x - z, v⟫ ≤ r * β :=
    (real_inner_le_norm _ _).trans (mul_le_mul hxr hv (norm_nonneg _) (hρ.trans (hxρ.trans hxr)))
  -- The coefficient of `g` is at least `γ`.
  have hcoef : γ ≤ 4 * α ^ 2 * A.toQuadraticForm' (x - z) - 2 * α * A.trace -
      2 * α * ⟪x - z, v⟫ := by
    nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * α ^ 2),
      mul_le_mul_of_nonneg_left htr (by positivity : (0 : ℝ) ≤ 2 * α),
      mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ 2 * α)]
  calc c * (g - C) ≤ c * g := mul_le_mul_of_nonneg_left (by linarith) hc
    _ ≤ γ * g := mul_le_mul_of_nonneg_right hcγ hg.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hg.le

/-- **Hopf's boundary-point lemma, core case.** The difference-quotient bound for a function `u`
satisfying `c (u - u x₀) ≤ L u` in the ball with `0 ≤ c ≤ γ`; the three sign cases of the
public statement reduce to this one. -/
private theorem exists_mul_le_sub_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Lam) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * (u x - u x₀) ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hlt : ∀ x ∈ ball y R, u x < u x₀) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  -- The space is nontrivial, since `x₀ ≠ y`.
  have hx₀y : x₀ - y ≠ 0 := by
    intro h
    rw [mem_sphere, dist_eq_norm, h, norm_zero] at hx₀
    exact hR.ne hx₀
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    exact hx₀y (Subsingleton.elim _ _)
  -- The outer unit normal `ν`, the half radius `r` and the midpoint `z` of `y` and `x₀`.
  set ν : EuclideanSpace ℝ ι := R⁻¹ • (x₀ - y) with hνdef
  set r : ℝ := R / 2 with hrdef
  have hr : 0 < r := by positivity
  set z : EuclideanSpace ℝ ι := y + (2⁻¹ : ℝ) • (x₀ - y) with hzdef
  have hν : ‖ν‖ = 1 := by
    rw [hνdef, norm_smul, ← dist_eq_norm, mem_sphere.mp hx₀, norm_inv, Real.norm_eq_abs,
      abs_of_pos hR, inv_mul_cancel₀ hR.ne']
  have hx₀z : x₀ - z = r • ν := by
    rw [hzdef, hνdef, smul_smul, hrdef, div_mul_eq_mul_div, mul_inv_cancel₀ hR.ne', one_div]
    module
  have hmem : ∀ x, ‖x - z‖ ≤ r → x ≠ x₀ → x ∈ ball y R := fun x hx hne ↦ by
    have hzmid : z = midpoint ℝ y x₀ := by
      rw [hzdef, midpoint_eq_smul_add, invOf_eq_inv]
      module
    refine mem_ball_of_mem_closedBall_midpoint hx₀ ?_ hne
    rwa [← hzmid, mem_closedBall, dist_eq_norm]
  have hballz : ball z r ⊆ ball y R := fun x hx ↦ by
    rw [mem_ball, dist_eq_norm] at hx
    refine hmem x hx.le fun h ↦ ?_
    rw [h, hx₀z, norm_smul, hν, Real.norm_eq_abs, abs_of_pos hr, mul_one] at hx
    exact lt_irrefl r hx
  -- `u` stays a margin `m` below `u x₀` on the closed ball of radius `r / 2` about `z`.
  have hinner_sub : closedBall z (r / 2) ⊆ ball y R := fun x hx ↦
    hballz (closedBall_subset_ball (by linarith) hx)
  obtain ⟨p, hp, hpmax⟩ := (isCompact_closedBall z (r / 2)).exists_isMaxOn
    (nonempty_closedBall.mpr (by positivity))
    (fun x hx ↦ (hu x (hinner_sub hx)).continuousAt.continuousWithinAt)
  set m := u x₀ - u p with hmdef
  have hm : 0 < m := sub_pos.mpr (hlt p (hinner_sub hp))
  have hmle : ∀ x ∈ closedBall z (r / 2), u x - u x₀ ≤ -m := fun x hx ↦ by
    have := isMaxOn_iff.mp hpmax x hx
    linarith
  -- The barrier exponent.
  set M := Lam + r * β
  set κ := 4 * lam * (r / 2) ^ 2
  have hκ : 0 < κ := by positivity
  set α : ℝ := (2 * |M| + |γ| + 1) / κ + 1 with hαdef
  have hα1 : 1 ≤ α := by
    have : 0 ≤ (2 * |M| + |γ| + 1) / κ := by positivity
    linarith
  have hαbig : γ + 2 * α * M ≤ 4 * α ^ 2 * lam * (r / 2) ^ 2 := by
    have hκα : κ * α = 2 * |M| + |γ| + 1 + κ := by
      rw [hαdef, mul_add, mul_div_cancel₀ _ hκ.ne', mul_one]
    have h4 : 4 * α ^ 2 * lam * (r / 2) ^ 2 = α * (κ * α) := by ring
    rw [h4, hκα]
    nlinarith [le_abs_self M, le_abs_self γ, abs_nonneg γ, abs_nonneg M]
  -- The Gaussian barrier, vanishing on `sphere z r` and at most `1` everywhere.
  set C := Real.exp (-α * r ^ 2) with hCdef
  have hC : 0 < C := Real.exp_pos _
  set v : EuclideanSpace ℝ ι → ℝ := fun x ↦ Real.exp (-α * ‖x - z‖ ^ 2) - C with hvdef
  have hvcd : ContDiff ℝ 2 v := by
    have : ContDiff ℝ 2 fun x : EuclideanSpace ℝ ι ↦ ‖x - z‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact (this.const_smul (-α)).exp.sub contDiff_const
  have hvle : ∀ x, v x ≤ 1 := fun x ↦ by
    have : Real.exp (-α * ‖x - z‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
    simp only [hvdef]
    linarith
  -- The perturbation `w = u - u x₀ + m v` and the closed annulus `K`.
  set f : EuclideanSpace ℝ ι → ℝ := fun x ↦ u x - u x₀ with hfdef
  set w : EuclideanSpace ℝ ι → ℝ := f + m • v with hwdef
  set K : Set (EuclideanSpace ℝ ι) := closedBall z r \ ball z (r / 2) with hKdef
  have hK : IsCompact K := (isCompact_closedBall z r).diff isOpen_ball
  have hKnorm : ∀ x ∈ K, r / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ r := fun x hx ↦ by
    simp only [hKdef, Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, not_lt] at hx
    exact ⟨hx.2, hx.1⟩
  have hKint : ∀ x ∈ interior K, x ∈ ball y R := fun x hx ↦
    hballz (by simpa only [interior_closedBall z hr.ne'] using interior_mono sdiff_subset hx)
  have hfcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 f x := fun x hx ↦ (hu x hx).sub contDiffAt_const
  -- `w` is continuous on `K`: away from `x₀` this is the smoothness of `u` in the ball.
  have hwcont : ContinuousOn w K := by
    refine ContinuousOn.add (fun x hx ↦ ?_) (hvcd.continuous.continuousOn.const_smul m)
    by_cases hxx₀ : x = x₀
    · subst hxx₀
      refine ((continuousWithinAt_insert_self.mpr hcont).mono fun x' hx' ↦ ?_).sub
        continuousWithinAt_const
      by_cases h : x' = x
      · exact h ▸ mem_insert _ _
      · exact mem_insert_of_mem _ (hmem x' (hKnorm x' hx').2 h)
    · exact (hfcd x (hmem x (hKnorm x hx).2 hxx₀)).continuousAt.continuousWithinAt
  have hwcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 w x := fun x hx ↦
    (hfcd x (hKint x hx)).add (hvcd.contDiffAt.const_smul m)
  -- `w` is a subsolution in the open annulus.
  have hwsub : ∀ ⦃x⦄, x ∈ interior K → c x * w x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ w x (b x) := fun x hx ↦ by
    have hxB := hKint x hx
    have hxK := hKnorm x (interior_subset hx)
    rw [hwdef, sum_mul_fderiv_fderiv_add_fderiv_add_smul (hfcd x hxB) hvcd.contDiffAt]
    have hfu : fderiv ℝ f = fderiv ℝ u := funext fun _ ↦ fderiv_sub_const _
    have hbar := mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sq_sub (ha x hxB)
      (htr x hxB) (hb x hxB) (hc x hxB) (hcγ x hxB) (by positivity) hxK.1 hxK.2 (by positivity)
      hαbig hlam.le hC.le
    simp only [hfu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hsub x hxB, mul_le_mul_of_nonneg_left hbar hm.le]
  -- `w ≤ 0` on the frontier of `K`.
  have hwbdry : ∀ ⦃x⦄, x ∈ frontier K → w x ≤ 0 := fun x hx ↦ by
    have hxK : x ∈ K := hK.isClosed.frontier_subset hx
    obtain ⟨h1, h2⟩ := hKnorm x hxK
    simp only [hwdef, hfdef, hvdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases h2.lt_or_eq with h2 | h2
    · -- Inner sphere: `u - u x₀ ≤ -m` and `v ≤ 1`.
      have h1' : ‖x - z‖ = r / 2 := by
        refine le_antisymm (not_lt.mp fun hlt' ↦ ?_) h1
        have hopen : ball z r \ closedBall z (r / 2) ⊆ interior K :=
          interior_maximal (sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall)
            (isOpen_ball.sdiff isClosed_closedBall)
        exact (mem_frontier_iff_notMem_interior hxK).mp hx
          (hopen ⟨by rwa [mem_ball, dist_eq_norm], by
            rw [mem_closedBall, dist_eq_norm]; exact not_le.mpr hlt'⟩)
      have hux := hmle x (by rw [mem_closedBall, dist_eq_norm]; exact h1'.le)
      nlinarith [hvle x, mul_le_mul_of_nonneg_left (hvle x) hm.le]
    · -- Outer sphere: the barrier vanishes and `u ≤ u x₀`.
      rw [h2, sub_self, mul_zero, add_zero, sub_nonpos]
      by_cases hxx₀ : x = x₀
      · rw [hxx₀]
      · exact (hlt x (hmem x h2.le hxx₀)).le
  have hwK := le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hK hlam
    (fun x hx ↦ ha x (hKint x hx)) (fun x hx ↦ hb x (hKint x hx)) (fun x hx ↦ hc x (hKint x hx))
    le_rfl hwcont hwcd hwsub hwbdry
  -- Along the inward radius, `w ≤ 0` and the convexity of `exp` give the linear bound.
  refine ⟨m * C * α * r, by positivity, r / 2, by positivity, fun t ht ↦ ?_⟩
  have hpz : x₀ - t • ν - z = (r - t) • ν := by
    rw [sub_right_comm, hx₀z, sub_smul]
  have hpnorm : ‖x₀ - t • ν - z‖ = r - t := by
    rw [hpz, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
  have hpK : x₀ - t • ν ∈ K := by
    simp only [hKdef, Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, hpnorm, not_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hwp := hwK hpK
  simp only [hwdef, hfdef, hvdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpnorm] at hwp
  -- `exp (-α (r - t)²) ≥ C (1 + α (r² - (r - t)²)) ≥ C (1 + α r t)`.
  have hexp : C * (α * r * t) ≤ Real.exp (-α * (r - t) ^ 2) - C := by
    have h := Real.add_one_le_exp (α * (r ^ 2 - (r - t) ^ 2))
    have hsplit : Real.exp (-α * (r - t) ^ 2) = C * Real.exp (α * (r ^ 2 - (r - t) ^ 2)) := by
      rw [hCdef, ← Real.exp_add]
      ring_nf
    have hrt : r * t ≤ r ^ 2 - (r - t) ^ 2 := by nlinarith [ht.1, ht.2]
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hrt (by positivity : (0 : ℝ) ≤ α),
      mul_le_mul_of_nonneg_left h hC.le]
  nlinarith [mul_le_mul_of_nonneg_left hexp hm.le]

/-- **Hopf's boundary-point lemma for elliptic operators in non-divergence form.** Let
`x₀ ∈ sphere y R`, with outer unit normal `ν = R⁻¹ • (x₀ - y)`, and on `ball y R` let `a` satisfy
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ` with `0 < λ` and `tr a(x) ≤ Λ`, let `‖b‖ ≤ β` and `c ≤ γ`. Let `u` be `C²` in
the ball and continuous at `x₀` relative to it, with
`c u ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` in the ball and `u x < u x₀` for every `x` in the ball. If `c = 0`,
or `c ≥ 0` and `u x₀ ≥ 0`, or `u x₀ = 0`, then for some `ε, δ > 0` the inward difference quotients
satisfy `ε t ≤ u x₀ - u (x₀ - t ν)` for `0 < t < δ`.

In Gilbarg and Trudinger's convention, with zeroth-order coefficient `c' = -c` on the right, the
three cases read `c' = 0`, `c' ≤ 0` with `u x₀ ≥ 0`, and `u x₀ = 0` with no sign on `c'`; the
bound `c ≤ γ` is their lower bound on `c'`. -/
theorem exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Lam) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hlt : ∀ x ∈ ball y R, u x < u x₀)
    (hsign : (∀ x ∈ ball y R, c x = 0) ∨ ((∀ x ∈ ball y R, 0 ≤ c x) ∧ 0 ≤ u x₀) ∨ u x₀ = 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  -- Replace `c` by its positive part, which satisfies `c⁺ (u - u x₀) ≤ L u` in every case.
  refine exists_mul_le_sub_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    (c := fun x ↦ max (c x) 0) (γ := max γ 0) hlam ha htr hb (fun _ _ ↦ le_max_right _ _)
    (fun x hx ↦ max_le_max_right 0 (hcγ x hx)) hu (fun x hx ↦ ?_) hR hx₀ hcont hlt
  refine le_trans ?_ (hsub x hx)
  rcases hsign with h0 | ⟨hc0, hu0⟩ | hu0
  · simp [h0 x hx]
  · rw [max_eq_left (hc0 x hx)]
    nlinarith [hc0 x hx]
  · -- Here `u x < 0`, so `max (c x) 0 * u x ≤ c x * u x`.
    rw [hu0, sub_zero]
    exact mul_le_mul_of_nonpos_right (le_max_left _ _) (hu0 ▸ hlt x hx).le

/-- **Hopf's boundary-point lemma, derivative form.** Under the hypotheses of
`TauCeti.PDE.exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`, if the
outer normal derivative of `u` at `x₀` exists, as the one-sided derivative `d` of
`t ↦ u (x₀ + t ν)` at `0` from the side `t ≤ 0` of the ball, then `0 < d`. -/
theorem pos_of_hasDerivWithinAt_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R d : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Lam) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hlt : ∀ x ∈ ball y R, u x < u x₀)
    (hsign : (∀ x ∈ ball y R, c x = 0) ∨ ((∀ x ∈ ball y R, 0 ≤ c x) ∧ 0 ≤ u x₀) ∨ u x₀ = 0)
    (hd : HasDerivWithinAt (fun t : ℝ ↦ u (x₀ + t • (R⁻¹ • (x₀ - y)))) d (Iic 0) 0) :
    0 < d := by
  obtain ⟨ε, hε, δ, hδ, hq⟩ :=
    exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball hlam ha htr hb hcγ hu
      hsub hR hx₀ hcont hlt hsign
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Iic_sdiff_right] at hslope
  -- On `(-δ, 0)` the slopes are at least `ε`.
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), ε ≤ slope (fun t : ℝ ↦ u (x₀ + t • (R⁻¹ • (x₀ - y)))) 0 t := by
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hδ)] with t ht
    have h := hq (-t) ⟨neg_pos.mpr ht.2, neg_lt.mp ht.1⟩
    rw [neg_smul, sub_neg_eq_add] at h
    rw [slope_def_field, zero_smul, add_zero, sub_zero, le_div_iff_of_neg ht.2]
    linarith
  linarith [ge_of_tendsto hslope hev]

end PDE

end TauCeti
