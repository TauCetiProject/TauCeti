/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Hopf's boundary-point lemma and the strong maximum principle in non-divergence form

Let `B = ball y R` be a ball in `ℝⁿ = EuclideanSpace ℝ ι` and let `x₀` lie on its bounding
sphere. This file proves **Hopf's boundary-point lemma** for the second-order operator in
non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`

with a zeroth-order coefficient `c`, and deduces the **strong maximum principle**. On `B` the
coefficient matrix `a` is elliptic, `λ ‖ξ‖² ≤ ξᵀ a ξ` with `λ > 0`, and has trace at most `Λ`,
the drift is bounded, `‖b‖ ≤ β`, and `c ≤ γ`. Let `u` be `C²` in `B`, continuous at `x₀` relative
to `B`, a subsolution `c u ≤ L u` in `B`, and strictly below `u x₀` there. If `c = 0`, or `c ≥ 0`
and `u x₀ ≥ 0`, or `u x₀ = 0`, then `u` leaves `x₀` along the outer normal `ν = (x₀ - y) / R` at
a positive linear rate: `ε t ≤ u x₀ - u (x₀ - t ν)` for some `ε > 0` and all small `t > 0`. In
particular a left derivative of `t ↦ u (x₀ + t ν)` at `0`, if it exists, is positive.

The coefficients need no regularity, not even measurability, `a` need not be symmetric, and
nothing is assumed outside `B`. A coefficient field with
`TauCeti.PDE.UniformlyEllipticOn (ball y R) a λ Λ` supplies the hypotheses on `a` through
`UniformlyEllipticOn.lower_bound` and `UniformlyEllipticOn.trace_le`. The sign conditions are
Gilbarg–Trudinger's: with the subsolution condition written `c u ≤ L u`, their `c ≤ 0` reads
`c ≥ 0` here.

The proof is the classical one. On the ball `B'` of radius `R / 2` about the midpoint of `y` and
`x₀`, which lies in `B` except for the point `x₀`, the Gaussian barrier
`v = exp (-α ‖· - y'‖²) - exp (-α (R / 2)²)` vanishes on `∂B'` and satisfies

`L v = (4 α² ⟪x - y', a (x - y')⟫ - 2 α tr a - 2 α ⟪x - y', b⟫) exp (-α ‖x - y'‖²)`,

so it is a subsolution on the annulus `R / 4 ≤ ‖x - y'‖ ≤ R / 2` once `α` is large. Since `u`
stays a positive margin below `u x₀` on the inner sphere, the weak maximum principle
`TauCeti.PDE.le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier` bounds `u + m v` by
`u x₀` on the annulus for a small `m > 0`, and `v` grows linearly along the inward normal.

The strong maximum principle follows as for the Laplacian in
`TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple`: if a subsolution attained
its maximum at a point near which it is not constant, a ball in the region where it is smaller
would touch the level set of the maximum at an interior local maximum, where Hopf's lemma makes
the derivative along the normal positive.

## Main declarations

* `TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq`: `L` applied to the
  Gaussian `exp (-α ‖· - y‖²)`.
* `TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`: **Hopf's
  boundary-point lemma**, the inward difference quotients are bounded below by a positive
  constant.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`: the
  derivative form, the outer normal derivative is positive where it exists.
* `TauCeti.PDE.eventually_eq_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isLocalMax`: a
  subsolution with a nonnegative local maximum is constant near it.
* `TauCeti.PDE.eqOn_const_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isMaxOn`: **the strong
  maximum principle** for `c ≥ 0` on a preconnected open set.
* `TauCeti.PDE.eqOn_const_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_isMaxOn`: the strong
  maximum principle for `c = 0`, with no sign condition on the maximum.
* `TauCeti.PDE.eqOn_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_of_eq`: the strong
  comparison principle, with no sign condition on `c`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.2 (Lemma 3.4 and Theorem 3.5).
* E. Hopf, *A remark on linear elliptic differential equations of second order*, Proc. Amer.
  Math. Soc. 3 (1952), 791–793.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter Function Matrix Metric Set RealInnerProductSpace Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Gaussian barrier.** The operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v` applied to
`g = exp (-α ‖· - y‖²)` is `(4 α² (x - y)ᵀ A (x - y) - 2 α tr A - 2 α ⟪x - y, v⟫) g`. The matrix
need not be symmetric. -/
theorem sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq (A : Matrix ι ι ℝ)
    (α : ℝ) (y x v : EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x v =
    (4 * α ^ 2 * A.toQuadraticForm' (x - y) - 2 * α * A.trace - 2 * α * ⟪x - y, v⟫) *
      Real.exp (-α * ‖x - y‖ ^ 2) := by
  set g := Real.exp (-α * ‖x - y‖ ^ 2)
  have hD2 (i j : ι) : fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      4 * α ^ 2 * g * ((x - y) i * (x - y) j) - 2 * α * g * (if i = j then 1 else 0) := by
    rw [fderiv_fderiv_exp_neg_mul_norm_sub_sq_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp [g, EuclideanSpace.inner_single_right]
      ring
    · simp [g, EuclideanSpace.inner_single_right, hij, hij.symm]
      ring
  have hD1 : fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x v = -2 * α * g * ⟪x - y, v⟫ := by
    rw [(hasFDerivAt_exp_neg_mul_norm_sub_sq α y x).fderiv, _root_.smul_apply,
      innerSL_apply_apply, smul_eq_mul]
  have hsum : ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      4 * α ^ 2 * g * A.toQuadraticForm' (x - y) - 2 * α * g * A.trace := by
    simp only [hD2, toQuadraticForm'_apply, dotProduct, mulVec, Matrix.trace, Matrix.diag,
      Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, WithLp.ofLp_sub]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hsum, hD1]
  ring

/-- On the annulus `ρ ≤ ‖x - y‖ ≤ R`, the shifted Gaussian barrier
`w = exp (-α ‖· - y‖²) - exp (-α R²)` is a subsolution, `c w ≤ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw + ∂_v w`, once
`α ≥ 1` is large compared with `tr A / λ`, `R ‖v‖ / λ` and `c / λ`, all measured against `ρ²`. -/
private theorem mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub
    {A : Matrix ι ι ℝ} {y x v : EuclideanSpace ℝ ι} {lam Λ β γ ρ R α c : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (htr : A.trace ≤ Λ)
    (hv : ‖v‖ ≤ β) (hc : 0 ≤ c) (hcγ : c ≤ γ) (hρ : 0 ≤ ρ) (hρx : ρ ≤ ‖x - y‖)
    (hxR : ‖x - y‖ ≤ R) (hα : 1 ≤ α)
    (hαbig : 2 * |Λ| + 2 * R * |β| + |γ| ≤ 4 * lam * ρ ^ 2 * α) :
    c * (Real.exp (-α * ‖x - y‖ ^ 2) - Real.exp (-α * R ^ 2)) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) -
        Real.exp (-α * R ^ 2)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * R ^ 2)) x v := by
  have hD : fderiv ℝ (fun z : EuclideanSpace ℝ ι ↦ Real.exp (-α * ‖z - y‖ ^ 2) -
      Real.exp (-α * R ^ 2)) = fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) :=
    funext fun _ ↦ fderiv_sub_const _
  rw [hD, sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq]
  set g := Real.exp (-α * ‖x - y‖ ^ 2)
  have hg : 0 < g := Real.exp_pos _
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hxR
  -- The zeroth-order term is at most `|γ| g`.
  have hlhs : c * (g - Real.exp (-α * R ^ 2)) ≤ |γ| * g := by
    have := Real.exp_pos (-α * R ^ 2)
    nlinarith [le_abs_self γ]
  -- The quadratic form is at least `λ ρ²`, the drift term at most `R |β|`.
  have hQ : lam * ρ ^ 2 ≤ A.toQuadraticForm' (x - y) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρx 2) hlam).trans (hA (x - y))
  have hinner : ⟪x - y, v⟫ ≤ R * |β| :=
    (real_inner_le_norm _ _).trans (mul_le_mul hxR (hv.trans (le_abs_self β)) (norm_nonneg _) hR0)
  refine hlhs.trans (mul_le_mul_of_nonneg_right ?_ hg.le)
  have hα0 : 0 ≤ α := zero_le_one.trans hα
  nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * α ^ 2),
    mul_le_mul_of_nonneg_left hαbig hα0, mul_le_mul_of_nonneg_left (le_abs_self Λ) hα0,
    mul_le_mul_of_nonneg_left hinner hα0, mul_le_mul_of_nonneg_right hα (abs_nonneg γ)]

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c u : EuclideanSpace ℝ ι → ℝ} {y x₀ : EuclideanSpace ℝ ι} {R lam Λ β γ : ℝ}

/-- Hopf's lemma under the sign conditions `c ≥ 0` and `u x₀ ≥ 0`, from which the other cases
follow. -/
private theorem exists_pos_mul_le_sub_of_mul_le_of_nonneg (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
    (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Λ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x) (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hlt : ∀ x ∈ ball y R, u x < u x₀) (hnonneg : 0 ≤ u x₀) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  rw [mem_sphere] at hx₀
  have hne : x₀ ≠ y := fun h ↦ by rw [h, dist_self] at hx₀; exact hR.ne hx₀
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hne (PiLp.ext fun i ↦ isEmptyElim i)
  -- Work on the ball `B'` of radius `r = R / 2` about the midpoint `y'` of `y` and `x₀`, which
  -- touches the sphere `∂B` only at `x₀`, and on the annulus `K` of `B'` with inner radius
  -- `ρ = R / 4`.
  set y' := midpoint ℝ y x₀ with hy'
  set r := R / 2 with hr
  set ρ := R / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by linarith
  have hx₀y' : dist x₀ y' = r := by
    rw [hy', dist_comm, dist_midpoint_right, Real.norm_two, dist_comm, hx₀]
    ring
  -- By Apollonius's theorem, `dist x y ^ 2 + dist x x₀ ^ 2 ≤ R ^ 2` on `B'`.
  have hball : ∀ x, dist x y' ≤ r → x ≠ x₀ → x ∈ ball y R := fun x hx hxx₀ ↦ by
    have h := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      x y x₀
    rw [← hy', dist_comm y x₀, hx₀] at h
    have hpos : 0 < dist x x₀ := dist_pos.mpr hxx₀
    rw [mem_ball]
    nlinarith [dist_nonneg (x := x) (y := y), dist_nonneg (x := x) (y := y')]
  set K := closedBall y' r \ ball y' ρ with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hint : ∀ ⦃x⦄, x ∈ interior K → x ∈ ball y R ∧ ρ ≤ dist x y' ∧ dist x y' ≤ r := by
    intro x hx
    have hxB : x ∈ ball y' r := by
      rw [← interior_closedBall y' (by positivity : r ≠ 0)]
      exact interior_mono sdiff_subset hx
    have hxK := interior_subset hx
    refine ⟨hball x hxK.1 fun h ↦ ?_, not_lt.mp hxK.2, hxK.1⟩
    rw [h, mem_ball, hx₀y'] at hxB
    exact lt_irrefl _ hxB
  -- `u` stays a margin `m₀ > 0` below `u x₀` on the inner sphere of the annulus.
  have hSball : ∀ x ∈ sphere y' ρ, x ∈ ball y R := fun x hx ↦
    hball x (by rw [mem_sphere.mp hx]; exact hρr.le) fun h ↦ by
      rw [h, mem_sphere, hx₀y'] at hx
      exact hρr.ne' hx
  obtain ⟨z, hzS, hzmax⟩ := (isCompact_sphere y' ρ).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hρ0.le)
    fun x hx ↦ (hcd x (hSball x hx)).continuousAt.continuousWithinAt
  set m₀ := u x₀ - u z with hm₀
  have hm₀pos : 0 < m₀ := sub_pos.mpr (hlt z (hSball z hzS))
  -- The Gaussian barrier `v`, vanishing on `∂B'` and a subsolution on the annulus.
  set α := 1 + (2 * |Λ| + 2 * r * |β| + |γ|) / (4 * lam * ρ ^ 2) with hα
  have hα1 : 1 ≤ α := by
    have : 0 ≤ (2 * |Λ| + 2 * r * |β| + |γ|) / (4 * lam * ρ ^ 2) := by positivity
    linarith
  have hαbig : 2 * |Λ| + 2 * r * |β| + |γ| ≤ 4 * lam * ρ ^ 2 * α := by
    have hpos : 0 < 4 * lam * ρ ^ 2 := by positivity
    rw [hα, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
    linarith
  set v : EuclideanSpace ℝ ι → ℝ := fun x ↦
    Real.exp (-α * ‖x - y'‖ ^ 2) - Real.exp (-α * r ^ 2) with hv
  have hvcd : ContDiff ℝ 2 v :=
    ((contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).exp).sub contDiff_const
  have hvle : ∀ x, v x ≤ 1 := fun x ↦ by
    have h1 : Real.exp (-α * ‖x - y'‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x - y'‖])
    linarith [Real.exp_pos (-α * r ^ 2)]
  -- The weak maximum principle bounds `u + m₀ v` by `u x₀` on the annulus.
  have hmax : ∀ ⦃x⦄, x ∈ K → (u + m₀ • v) x ≤ u x₀ := by
    refine le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hKc hlam
      (fun x hx ↦ ha x (hint hx).1) (fun x hx ↦ hb x (hint hx).1)
      (fun x hx ↦ hc x (hint hx).1) hnonneg ?_ ?_ ?_ ?_
    · refine ContinuousOn.add (fun x hx ↦ ?_) (hvcd.continuous.continuousOn.const_smul m₀)
      by_cases hxx₀ : x = x₀
      · subst hxx₀
        refine (continuousWithinAt_insert_self.mpr hcont).mono fun z hz ↦ ?_
        by_cases hzx : z = x
        · exact hzx ▸ mem_insert _ _
        · exact mem_insert_of_mem _ (hball z hz.1 hzx)
      · exact (hcd x (hball x hx.1 hxx₀)).continuousAt.continuousWithinAt
    · exact fun x hx ↦ (hcd x (hint hx).1).add (hvcd.contDiffAt.const_smul m₀)
    · intro x hx
      obtain ⟨hxB, hρx, hxr⟩ := hint hx
      rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hcd x hxB) hvcd.contDiffAt]
      have hbar := mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub
        (A := a x) (v := b x) (y := y') hlam.le (ha x hxB) (htr x hxB) (hb x hxB) (hc x hxB)
        (hcγ x hxB) hρ0.le (by rwa [← dist_eq_norm]) (by rwa [← dist_eq_norm]) hα1 hαbig
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hsub x hxB, mul_le_mul_of_nonneg_left hbar hm₀pos.le]
    · intro x hx
      have hxK : x ∈ K := hKc.isClosed.frontier_subset hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases (mem_closedBall.mp hxK.1).eq_or_lt with hxr | hxr
      · -- On `∂B'` the barrier vanishes.
        have hv0 : v x = 0 := by simp only [hv, ← dist_eq_norm, hxr, sub_self]
        rw [hv0, mul_zero, add_zero]
        by_cases hxx₀ : x = x₀
        · rw [hxx₀]
        · exact (hlt x (hball x hxr.le hxx₀)).le
      · -- Otherwise `x` lies on the inner sphere, where the margin absorbs the barrier.
        have hxρ : dist x y' = ρ := by
          refine le_antisymm (not_lt.mp fun hρx ↦ hx.2 ?_) (not_lt.mp hxK.2)
          refine interior_maximal (t := ball y' r \ closedBall y' ρ) ?_
            (isOpen_ball.sdiff isClosed_closedBall) ⟨hxr, by simpa using hρx⟩
          exact sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall
        have huz : u x ≤ u z := hzmax (mem_sphere.mpr hxρ)
        nlinarith [mul_le_mul_of_nonneg_left (hvle x) hm₀pos.le]
  -- Along the inward normal, the barrier grows at least linearly.
  refine ⟨m₀ * (α * r * Real.exp (-α * r ^ 2)), by positivity, r - ρ, by linarith,
    fun t ht ↦ ?_⟩
  set x := x₀ - t • (R⁻¹ • (x₀ - y)) with hxdef
  have hxy' : dist x y' = r - t := by
    have h : x - y' = (2⁻¹ - t * R⁻¹) • (x₀ - y) := by
      rw [hxdef, hy', midpoint_eq_smul_add, invOf_eq_inv]
      module
    rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, ← dist_eq_norm x₀ y, hx₀,
      abs_of_nonneg (by rw [sub_nonneg, ← div_eq_mul_inv, div_le_iff₀ hR]; linarith [ht.2])]
    field_simp
    ring
  have hxK : x ∈ K := ⟨mem_closedBall.mpr (by linarith [ht.1]),
    fun h ↦ by rw [mem_ball] at h; linarith [ht.2]⟩
  have hw := hmax hxK
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hw
  have hvx : α * r * Real.exp (-α * r ^ 2) * t ≤ v x := by
    have hexp : Real.exp (-α * ‖x - y'‖ ^ 2) =
        Real.exp (-α * r ^ 2) * Real.exp (α * (r ^ 2 - (r - t) ^ 2)) := by
      rw [← Real.exp_add, ← dist_eq_norm, hxy']
      ring_nf
    have h1 := Real.add_one_le_exp (α * (r ^ 2 - (r - t) ^ 2))
    have h2 : α * r * t ≤ α * (r ^ 2 - (r - t) ^ 2) := by
      have : r * t ≤ r ^ 2 - (r - t) ^ 2 := by nlinarith [ht.1, ht.2]
      nlinarith
    simp only [hv, hexp]
    nlinarith [Real.exp_pos (-α * r ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left hvx hm₀pos.le]

/-- **Hopf's boundary-point lemma** for the elliptic operator in non-divergence form
`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` with zeroth-order coefficient `c`. Let `B = ball y R` and let
`x₀` lie on its bounding sphere. On `B` let `a` be elliptic, `λ ‖ξ‖² ≤ ξᵀ a ξ` with `λ > 0`, with
trace at most `Λ`, let `‖b‖ ≤ β` and `c ≤ γ`. Let `u` be `C²` in `B`, continuous at `x₀` relative
to `B`, a subsolution `c u ≤ L u` there, and strictly below `u x₀` in `B`. If `c = 0`, or `c ≥ 0`
and `u x₀ ≥ 0`, or `u x₀ = 0`, then along the inward normal the difference quotient
`(u x₀ - u (x₀ - t ν)) / t`, with `ν = (x₀ - y) / R` the outer unit normal of `B` at `x₀`, is
bounded below by a positive constant for all small `t > 0`.

In Gilbarg–Trudinger's notation the subsolution condition `c u ≤ L u` reads `L' u ≥ 0` for
`L' = L - c`, so their sign condition `c ≤ 0` is `c ≥ 0` here. Nothing is assumed of `u` or of the
coefficients outside `B`, the coefficients need no regularity, not even measurability, and `a`
need not be symmetric. -/
theorem exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv (hR : 0 < R)
    (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Λ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hlt : ∀ x ∈ ball y R, u x < u x₀)
    (hsign : (∀ x ∈ ball y R, c x = 0) ∨ ((∀ x ∈ ball y R, 0 ≤ c x) ∧ 0 ≤ u x₀) ∨ u x₀ = 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  rcases hsign with hc0 | ⟨hc, hnonneg⟩ | hzero
  · -- For `c = 0`, subtracting the constant `u x₀` changes neither `L u` nor the conclusion.
    have hD : fderiv ℝ (fun x ↦ u x - u x₀) = fderiv ℝ u := funext fun _ ↦ fderiv_sub_const _
    obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_sub_of_mul_le_of_nonneg (u := fun x ↦ u x - u x₀)
      hR hx₀ hlam ha htr hb (fun x hx ↦ (hc0 x hx).ge) hcγ
      (fun x hx ↦ (hcd x hx).sub contDiffAt_const) (hcont.sub continuousWithinAt_const)
      (fun x hx ↦ by
        rw [hD, hc0 x hx, zero_mul]
        simpa only [hc0 x hx, zero_mul] using hsub x hx)
      (fun x hx ↦ sub_lt_sub_right (hlt x hx) _) (sub_self _).ge
    exact ⟨ε, hε, δ, hδ, fun t ht ↦ by simpa only [sub_sub_sub_cancel_right] using h t ht⟩
  · exact exists_pos_mul_le_sub_of_mul_le_of_nonneg hR hx₀ hlam ha htr hb hc hcγ hcd hcont hsub
      hlt hnonneg
  · -- For `u x₀ = 0`, `u ≤ 0` on `B`, so replacing `c` by `max c 0` keeps `u` a subsolution.
    refine exists_pos_mul_le_sub_of_mul_le_of_nonneg (c := fun x ↦ max (c x) 0) (γ := max γ 0)
      hR hx₀ hlam ha htr hb (fun _ _ ↦ le_max_right _ _)
      (fun x hx ↦ max_le_max_right 0 (hcγ x hx)) hcd hcont (fun x hx ↦ ?_) hlt hzero.ge
    have hu : u x ≤ 0 := hzero ▸ (hlt x hx).le
    exact (mul_le_mul_of_nonpos_right (le_max_left _ _) hu).trans (hsub x hx)

/-- **Hopf's boundary-point lemma, derivative form.** Under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`, if the derivative of `u`
from inside `B` along the outer normal `ν = (x₀ - y) / R` exists at `x₀`, that is,
`t ↦ u (x₀ + t ν)` has a left derivative `d` at `0`, then `d > 0`. -/
theorem pos_of_hasDerivWithinAt_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv (hR : 0 < R)
    (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Λ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hlt : ∀ x ∈ ball y R, u x < u x₀)
    (hsign : (∀ x ∈ ball y R, c x = 0) ∨ ((∀ x ∈ ball y R, 0 ≤ c x) ∧ 0 ≤ u x₀) ∨ u x₀ = 0)
    {d : ℝ} (hd : HasDerivWithinAt (fun t : ℝ ↦ u (x₀ + t • (R⁻¹ • (x₀ - y)))) d (Iic 0) 0) :
    0 < d := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv hR
    hx₀ hlam ha htr hb hcγ hcd hcont hsub hlt hsign
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Iic_sdiff_right] at hslope
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  -- For `-δ < t < 0` the slope at `0` is the inward difference quotient at `-t`.
  filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hδ)] with t ht
  have hmem : -t ∈ Ioo 0 δ := ⟨neg_pos.mpr ht.2, by linarith [ht.1]⟩
  have h' := h (-t) hmem
  rw [neg_smul, sub_neg_eq_add] at h'
  rw [slope_def_field, zero_smul, add_zero, sub_zero, le_div_iff_of_neg ht.2]
  linarith

/-- A subsolution as in Hopf's lemma with `c ≥ 0` and `u x₀ ≥ 0` that is differentiable at `x₀`
has no local maximum there: its derivative along the outer normal is positive. -/
private theorem not_isLocalMax_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv (hR : 0 < R)
    (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ Λ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x) (hderiv : DifferentiableAt ℝ u x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hlt : ∀ x ∈ ball y R, u x < u x₀) (hnonneg : 0 ≤ u x₀) :
    ¬IsLocalMax u x₀ := by
  intro hmax
  set ν := R⁻¹ • (x₀ - y)
  have hline : HasDerivAt (fun t : ℝ ↦ x₀ + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add x₀
  have hd : HasDerivAt (fun t : ℝ ↦ u (x₀ + t • ν)) (fderiv ℝ u x₀ ν) 0 :=
    hderiv.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hpos := pos_of_hasDerivWithinAt_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv hR hx₀ hlam ha
    htr hb hcγ hcd hderiv.continuousAt.continuousWithinAt hsub hlt (Or.inr (Or.inl ⟨hc, hnonneg⟩))
    hd.hasDerivWithinAt
  rw [hmax.fderiv_eq_zero, _root_.zero_apply] at hpos
  exact lt_irrefl _ hpos

/-- **Local strong maximum principle** for `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` with zeroth-order
coefficient `c`. Let `u` be `C²` at a local maximum point `x` with `0 ≤ u x`, and near `x` let `a`
be elliptic with constant `λ > 0` and trace at most `Λ`, let `‖b‖ ≤ β` and `0 ≤ c ≤ γ`, and let
`u` be a subsolution `c u ≤ L u`. Then `u` is constant on a neighbourhood of `x`. -/
theorem eventually_eq_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isLocalMax
    {x : EuclideanSpace ℝ ι} (hcd : ContDiffAt ℝ 2 u x) (hlam : 0 < lam)
    (ha : ∀ᶠ z in 𝓝 x, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ)
    (htr : ∀ᶠ z in 𝓝 x, (a z).trace ≤ Λ) (hb : ∀ᶠ z in 𝓝 x, ‖b z‖ ≤ β)
    (hc : ∀ᶠ z in 𝓝 x, 0 ≤ c z) (hcγ : ∀ᶠ z in 𝓝 x, c z ≤ γ)
    (hsub : ∀ᶠ z in 𝓝 x, c z * u z ≤
      ∑ i, ∑ j, a z i j * fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u z (b z))
    (hnonneg : 0 ≤ u x) (hmax : IsLocalMax u x) :
    ∀ᶠ z in 𝓝 x, u z = u x := by
  -- Work on a ball `ball x (3 * r)` on which `u` is `C²`, bounded by `u x`, and a subsolution
  -- with controlled coefficients.
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hcd.eventually (by simp)).and (hmax.and (ha.and (htr.and (hb.and (hc.and
      (hcγ.and hsub)))))))
  set r := r₀ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hball : ∀ ⦃z⦄, dist z x < 3 * r →
      ContDiffAt ℝ 2 u z ∧ u z ≤ u x ∧
        (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ) ∧
        (a z).trace ≤ Λ ∧ ‖b z‖ ≤ β ∧ 0 ≤ c z ∧ c z ≤ γ ∧
        c z * u z ≤ ∑ i, ∑ j, a z i j * fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ u z (b z) := fun z hz ↦
    hr₀sub z (by rw [mem_ball]; linarith)
  by_contra hne
  -- Some point `x₂` close to `x` has a different value.
  obtain ⟨x₂, hx₂x, hx₂ne⟩ : ∃ x₂, dist x₂ x < r ∧ u x₂ ≠ u x := by
    by_contra! h
    exact hne (Metric.eventually_nhds_iff.mpr ⟨r, hr, fun z hz ↦ h z hz⟩)
  -- The part `Z` of the level set `{u = u x}` in `closedBall x (2 * r)` is compact.
  set Z := closedBall x (2 * r) ∩ u ⁻¹' {u x}
  have hcont : ContinuousOn u (closedBall x (2 * r)) := fun z hz ↦
    (hball (by rw [mem_closedBall] at hz; linarith)).1.continuousAt.continuousWithinAt
  have hZclosed : IsClosed Z :=
    hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hZcompact : IsCompact Z :=
    (isCompact_closedBall x (2 * r)).of_isClosed_subset hZclosed inter_subset_left
  have hxZ : x ∈ Z := ⟨mem_closedBall_self (by positivity), rfl⟩
  have hx₂Z : x₂ ∉ Z := fun h ↦ hx₂ne h.2
  -- `ρ` is the distance from `x₂` to `Z`, attained at `x₀ ∈ Z`.
  set ρ := infDist x₂ Z
  have hρ : 0 < ρ := (hZclosed.notMem_iff_infDist_pos ⟨x, hxZ⟩).mp hx₂Z
  have hρr : ρ < r := (infDist_le_dist_of_mem hxZ).trans_lt hx₂x
  obtain ⟨x₀, hx₀Z, hx₀dist⟩ := hZcompact.exists_infDist_eq_dist ⟨x, hxZ⟩ x₂
  have hnear : ∀ ⦃z⦄, dist z x₂ ≤ ρ → dist z x < 2 * r := fun z hz ↦ by
    linarith [dist_triangle z x₂ x]
  have hin : ∀ z ∈ ball x₂ ρ, dist z x < 3 * r := fun z hz ↦ by
    rw [mem_ball] at hz
    linarith [hnear hz.le]
  have hlt : ∀ z ∈ ball x₂ ρ, u z < u x₀ := fun z hz ↦ by
    rw [mem_ball] at hz
    have hzx := hnear hz.le
    refine hx₀Z.2 ▸ lt_of_le_of_ne (hball (by linarith)).2.1 fun hzu ↦ ?_
    have hzZ : z ∈ Z := ⟨mem_closedBall.mpr hzx.le, hzu⟩
    have := infDist_le_dist_of_mem (x := x₂) hzZ
    rw [dist_comm] at this
    linarith
  -- `x₀` is again a local maximum, on the sphere touching `Z`: this contradicts Hopf's lemma.
  have hx₀x : dist x₀ x < 3 * r := by
    linarith [hnear (z := x₀) (by rw [dist_comm, ← hx₀dist])]
  refine not_isLocalMax_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv hρ
    (by rw [mem_sphere, dist_comm, ← hx₀dist]) hlam
    (fun z hz ↦ (hball (hin z hz)).2.2.1) (fun z hz ↦ (hball (hin z hz)).2.2.2.1)
    (fun z hz ↦ (hball (hin z hz)).2.2.2.2.1) (fun z hz ↦ (hball (hin z hz)).2.2.2.2.2.1)
    (fun z hz ↦ (hball (hin z hz)).2.2.2.2.2.2.1) (fun z hz ↦ (hball (hin z hz)).1)
    ((hball hx₀x).1.differentiableAt (by simp)) (fun z hz ↦ (hball (hin z hz)).2.2.2.2.2.2.2)
    hlt (hx₀Z.2 ▸ hnonneg) ?_
  refine Metric.eventually_nhds_iff_ball.mpr ⟨3 * r - dist x₀ x, by linarith, fun z hz ↦ ?_⟩
  rw [mem_ball] at hz
  exact hx₀Z.2 ▸ (hball (by linarith [dist_triangle z x₀ x])).2.1

/-- **Strong maximum principle** for `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` with zeroth-order coefficient
`c ≥ 0`. Let `U` be a preconnected open set on which `a` is locally uniformly elliptic with
locally bounded trace, and `b` and `c` are locally bounded. A function that is `C²` on `U`, is a
subsolution `c u ≤ L u` there, and attains a nonnegative maximum over `U` at a point `p ∈ U`, is
constant on `U`. -/
theorem eqOn_const_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isMaxOn
    {U : Set (EuclideanSpace ℝ ι)} {p : EuclideanSpace ℝ ι} (hU : IsOpen U) (hp : p ∈ U)
    (hUconn : IsPreconnected U) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (ha : ∀ x ∈ U, ∃ lam > 0, ∀ᶠ z in 𝓝 x,
      ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ)
    (htr : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun z ↦ (a z).trace)
    (hb : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun z ↦ ‖b z‖) (hc : ∀ x ∈ U, 0 ≤ c x)
    (hcbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c)
    (hsub : ∀ x ∈ U, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u p) (hmax : IsMaxOn u U p) :
    EqOn u (const _ (u p)) U := by
  -- The points near which `u` is identically `u p` form an open set, which is relatively closed
  -- in `U` by continuity and the local principle, and contains `p`.
  have hlocal : ∀ x ∈ U, u x = u p → ∀ᶠ z in 𝓝 x, u z = u p := fun x hx hxp ↦ by
    have hxmax : IsMaxOn u U x := fun z hz ↦ hxp ▸ hmax hz
    obtain ⟨lam, hlam, hlamx⟩ := ha x hx
    obtain ⟨Λ, hΛ⟩ := htr x hx
    obtain ⟨β, hβ⟩ := hb x hx
    obtain ⟨γ, hγ⟩ := hcbdd x hx
    have hxnonneg : 0 ≤ u x := hxp ▸ hnonneg
    have h := eventually_eq_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isLocalMax
      (a := a) (b := b) (c := c) (Λ := Λ) (β := β) (γ := γ)
      (hcd x hx) hlam hlamx (eventually_map.mp hΛ) (eventually_map.mp hβ)
      (eventually_of_mem (hU.mem_nhds hx) hc) (eventually_map.mp hγ)
      (eventually_of_mem (hU.mem_nhds hx) hsub) hxnonneg (hxmax.isLocalMax (hU.mem_nhds hx))
    rwa [hxp] at h
  have hsubset : U ⊆ {x | ∀ᶠ z in 𝓝 x, u z = u p} := by
    refine hUconn.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds
      ⟨p, hp, hlocal p hp rfl⟩ ?_
    rintro x ⟨hxcl, hxU⟩
    refine hlocal x hxU (by_contra fun hxp ↦ ?_)
    obtain ⟨z, hz, hzO⟩ := mem_closure_iff_nhds.mp hxcl _
      ((hcd x hxU).continuousAt.eventually_ne hxp)
    exact hz hzO.self_of_nhds
  exact fun x hx ↦ (hsubset hx).self_of_nhds

/-- **Strong comparison principle** for `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu - c u`. Let `U` be a
preconnected open set on which `a` is locally uniformly elliptic with locally bounded trace, `b`
is locally bounded and `c` is locally bounded above, and let `u` and `v` be `C²` on `U` with
`L v ≤ L u` there. If `u ≤ v` on `U` and they agree at a point of `U`, then they agree on all of
`U`. No sign condition on `c`, `u` or `v` is needed: since `u - v ≤ 0`, the difference is a
subsolution for the coefficient `max c 0`. -/
theorem eqOn_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_of_eq
    {U : Set (EuclideanSpace ℝ ι)} {p : EuclideanSpace ℝ ι} {v : EuclideanSpace ℝ ι → ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (hUconn : IsPreconnected U)
    (hucd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hvcd : ∀ x ∈ U, ContDiffAt ℝ 2 v x)
    (ha : ∀ x ∈ U, ∃ lam > 0, ∀ᶠ z in 𝓝 x,
      ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ)
    (htr : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun z ↦ (a z).trace)
    (hb : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun z ↦ ‖b z‖)
    (hcbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c)
    (hL : ∀ x ∈ U,
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ v x (b x) - c x * v x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x) - c x * u x)
    (hle : ∀ x ∈ U, u x ≤ v x) (heq : u p = v p) :
    EqOn u v U := by
  have huv : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  -- Since `u - v ≤ 0`, replacing `c` by `max c 0` keeps `u - v` a subsolution.
  have h := eqOn_const_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isMaxOn (u := u - v)
    (c := fun x ↦ max (c x) 0) hU hp hUconn (fun x hx ↦ (hucd x hx).sub (hvcd x hx)) ha htr hb
    (fun _ _ ↦ le_max_right _ _)
    (fun x hx ↦ by
      obtain ⟨γ, hγ⟩ := hcbdd x hx
      exact isBoundedUnder_of_eventually_le
        ((eventually_map.mp hγ).mono fun _ hz ↦ max_le_max_right 0 hz))
    (fun x hx ↦ by
      rw [huv, sum_mul_fderiv_fderiv_add_fderiv_add_smul (hucd x hx) (hvcd x hx), ← huv,
        Pi.sub_apply]
      have := mul_le_mul_of_nonpos_right (le_max_left (c x) 0) (sub_nonpos.mpr (hle x hx))
      linarith [hL x hx])
    (by simp [heq])
    (fun x hx ↦ by
      simp only [Pi.sub_apply, heq, sub_self, sub_nonpos]
      exact hle x hx)
  intro x hx
  have hx' := h hx
  simp only [Pi.sub_apply, const_apply, heq, sub_self, sub_eq_zero] at hx'
  exact hx'

/-- **Strong maximum principle without zeroth-order term** (Gilbarg–Trudinger, Theorem 3.5). Let
`U` be a preconnected open set on which `a` is locally uniformly elliptic with locally bounded
trace and `b` is locally bounded. A function that is `C²` on `U` with
`0 ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` there and attains its maximum over `U` at a point `p ∈ U` is constant
on `U`. -/
theorem eqOn_const_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_isMaxOn
    {U : Set (EuclideanSpace ℝ ι)} {p : EuclideanSpace ℝ ι} (hU : IsOpen U) (hp : p ∈ U)
    (hUconn : IsPreconnected U) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (ha : ∀ x ∈ U, ∃ lam > 0, ∀ᶠ z in 𝓝 x,
      ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a z).toQuadraticForm' ξ)
    (htr : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun z ↦ (a z).trace)
    (hb : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun z ↦ ‖b z‖)
    (hL : ∀ x ∈ U, 0 ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hmax : IsMaxOn u U p) :
    EqOn u (const _ (u p)) U :=
  eqOn_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_of_eq (c := 0) hU hp hUconn hcd
    (fun _ _ ↦ contDiffAt_const) ha htr hb (fun _ _ ↦ isBoundedUnder_const)
    (fun x hx ↦ by simpa using hL x hx) (fun _ hx ↦ hmax hx) rfl

end PDE

end TauCeti
