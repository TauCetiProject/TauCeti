/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Hopf's boundary-point lemma for elliptic operators in non-divergence form

Let `B = ball y R` be a ball in `ℝⁿ = EuclideanSpace ℝ ι` and let `x₀` be a point of its bounding
sphere. On `B` consider the operator in non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`

with a variable coefficient matrix satisfying `λ ‖ξ‖² ≤ ξᵀ a(x) ξ ≤ Λ ‖ξ‖²`, `0 < λ`, and a drift
bounded by `‖b‖ ≤ β`. No regularity of the coefficients is assumed, not even measurability, and
`a` need not be symmetric. Let `u` be `C²` in `B`, continuous at `x₀` relative to `B`, and
strictly below `u x₀` in `B`. **Hopf's boundary-point lemma** (Gilbarg–Trudinger, Lemma 3.4)
says that `u` falls off at a linear rate along the inward normal: with `ν = (x₀ - y) / R` the
outer unit normal of `B` at `x₀`, there is `C > 0` with

`C t ≤ u x₀ - u (x₀ - t ν)` for `0 < t ≤ R / 4`,

provided one of the usual sign conditions holds for the zeroth-order coefficient `c`:

* `c u ≤ L u` with `0 ≤ c ≤ γ` and `0 ≤ u x₀`;
* `c u ≤ L u` with `c ≤ γ` and `u x₀ = 0`, with no sign on `c`;
* `0 ≤ L u`, with no sign on `u x₀`.

In particular, if `u` is differentiable at `x₀`, then its outer normal derivative there is
positive. The zeroth-order term is written with the sign of
`TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence`, so that `c ≥ 0` here is `c ≤ 0` in
Gilbarg–Trudinger's operator `L u + c u`. As in Gilbarg–Trudinger, nothing is assumed of `u` off
`B ∪ {x₀}`, and the ball need not touch the boundary of the domain of `u` only at `x₀`. The upper
bound `Λ` enters only through the trace of `a`, which the barrier involves.

The pointwise hypotheses matter: for weak solutions of divergence-form equations with merely
bounded measurable coefficients the lemma fails, the classical counterexample being
`u = r^s sin θ`, `s > 1`, on a half disk. For the Laplacian with lower-order terms the lemma is
`TauCeti.fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere`, which carries a
differentiability hypothesis at `x₀` and a bound on the whole sphere.

## The argument

On the annulus `R / 2 ≤ ‖x - y‖ ≤ R` the Gaussian barrier `w = exp (-κ ‖x - y‖²) - exp (-κ R²)`
satisfies

`L w = exp (-κ ‖x - y‖²) (4 κ² ξᵀ a ξ - 2 κ (tr a + ⟪ξ, b⟫))`, `ξ = x - y`,

so `c w ≤ L w` there once `κ` is large in terms of `n Λ / λ`, `β R / λ` and `γ R² / λ`. The
barrier vanishes on the outer sphere and is at most `1` on the inner one, where `u` stays a
margin `δ` below `u x₀`, so the weak maximum principle
`TauCeti.PDE.le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier` bounds `u + δ w` by `u x₀`
on the annulus, and `w` grows linearly along the inward normal. Since `u` is only known to be
continuous at `x₀` relative to `B`, the argument is run on the ball of radius `R / 2` internally
tangent to `B` at `x₀`, whose closure meets the sphere of `B` only at `x₀`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`:
  **Hopf's boundary-point lemma** for `c ≥ 0` and `0 ≤ u x₀`.
* `exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball_of_eq_zero`: the
  lemma for `u x₀ = 0`, with no sign condition on `c`.
* `TauCeti.PDE.exists_pos_mul_le_sub_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_lt_ball`: the
  lemma without zeroth-order term, with no sign condition on `u x₀`.
* `TauCeti.PDE.fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`: the derivative
  form, the outer normal derivative at `x₀` is positive.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.2 (Lemma 3.4).
* E. Hopf, *A remark on linear elliptic differential equations of second order*, Proc. Amer.
  Math. Soc. **3** (1952), 791–793.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter Matrix Metric Set Topology
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian barrier under `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v`: with `ξ = x - y`, it is
`exp (-κ ‖ξ‖²) (4 κ² ξᵀ A ξ - 2 κ (tr A + ⟪ξ, v⟫))`. -/
private theorem sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq (A : Matrix ι ι ℝ)
    (κ : ℝ) (y x v : EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ ι ↦
        Real.exp (-κ * ‖z - y‖ ^ 2)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z : EuclideanSpace ℝ ι ↦ Real.exp (-κ * ‖z - y‖ ^ 2)) x v =
    Real.exp (-κ * ‖x - y‖ ^ 2) *
      (4 * κ ^ 2 * A.toQuadraticForm' (x - y) - 2 * κ * (A.trace + ⟪x - y, v⟫)) := by
  simp only [fderiv_fderiv_exp_neg_mul_norm_sub_sq_apply, fderiv_exp_neg_mul_norm_sub_sq_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial, toQuadraticForm'_apply, dotProduct,
    mulVec, Matrix.trace, Matrix.diag, Finset.mul_sum, PiLp.single_apply, WithLp.ofLp_sub]
  set E := Real.exp (-κ * ‖x - y‖ ^ 2)
  set d := x.ofLp - y.ofLp
  have hterm (i j : ι) : A i j * (E * (4 * κ ^ 2 * d i * d j - 2 * κ * if j = i then 1 else 0)) =
      E * (4 * κ ^ 2 * (d i * (A i j * d j))) - E * (2 * κ * if j = i then A i j else 0) := by
    split_ifs <;> ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum]
  ring

/-- **The Gaussian barrier is a subsolution on an annulus.** Let `A` satisfy
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` with `0 < λ`, let `‖v‖ ≤ β` and `0 ≤ c ≤ γ`, and let
`0 < ρ ≤ ‖x - y‖ ≤ R`. If `1 ≤ κ` and `2 (n Λ + β R) + γ ≤ 4 λ ρ² κ`, then the barrier
`w = exp (-κ ‖· - y‖²) - exp (-κ R²)` satisfies `c w ≤ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw + ∂_v w` at `x`. -/
private theorem mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub
    {A : Matrix ι ι ℝ} {lam Lam β γ c κ ρ R : ℝ} {x y v : EuclideanSpace ℝ ι} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) (hv : ‖v‖ ≤ β)
    (hc : 0 ≤ c) (hcγ : c ≤ γ) (hρ : 0 < ρ) (hxρ : ρ ≤ ‖x - y‖) (hxR : ‖x - y‖ ≤ R)
    (hκ : 1 ≤ κ) (hκρ : 2 * (Fintype.card ι * Lam + β * R) + γ ≤ 4 * lam * ρ ^ 2 * κ) :
    c * (Real.exp (-κ * ‖x - y‖ ^ 2) - Real.exp (-κ * R ^ 2)) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ ι ↦
          Real.exp (-κ * ‖z - y‖ ^ 2) - Real.exp (-κ * R ^ 2)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z : EuclideanSpace ℝ ι ↦
        Real.exp (-κ * ‖z - y‖ ^ 2) - Real.exp (-κ * R ^ 2)) x v := by
  have hfd : fderiv ℝ (fun z : EuclideanSpace ℝ ι ↦
      Real.exp (-κ * ‖z - y‖ ^ 2) - Real.exp (-κ * R ^ 2)) =
      fderiv ℝ fun z : EuclideanSpace ℝ ι ↦ Real.exp (-κ * ‖z - y‖ ^ 2) :=
    funext fun _ ↦ fderiv_sub_const _
  rw [hfd, sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq]
  set E := Real.exp (-κ * ‖x - y‖ ^ 2)
  have hE : 0 < E := Real.exp_pos _
  have hER : 0 < Real.exp (-κ * R ^ 2) := Real.exp_pos _
  have hγ : 0 ≤ γ := hc.trans hcγ
  have hβ : 0 ≤ β := (norm_nonneg v).trans hv
  -- The three bounds entering `L w`.
  have hQ : lam * ρ ^ 2 ≤ A.toQuadraticForm' (x - y) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hxρ 2) hlam.le).trans (hA (x - y))
  have htr : A.trace ≤ Fintype.card ι * Lam := by
    calc A.trace = ∑ i, A i i := rfl
      _ ≤ ∑ _i : ι, Lam := Finset.sum_le_sum fun i _ ↦ by
          simpa [toQuadraticForm'_apply, dotProduct, mulVec, Pi.single_apply] using
            hA' (EuclideanSpace.single i 1)
      _ = Fintype.card ι * Lam := by simp
  have hinner : ⟪x - y, v⟫ ≤ β * R :=
    (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (x - y), norm_nonneg v])
  -- `4 κ² λ ρ² - 2 κ (n Λ + β R) ≥ γ`, and `c w ≤ γ E`.
  have hkey : γ ≤ 4 * κ ^ 2 * A.toQuadraticForm' (x - y) - 2 * κ * (A.trace + ⟪x - y, v⟫) := by
    nlinarith [mul_le_mul_of_nonneg_left hκρ (by linarith : (0 : ℝ) ≤ κ),
      mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * κ ^ 2)]
  have hcw : c * (E - Real.exp (-κ * R ^ 2)) ≤ γ * E := by
    nlinarith [mul_le_mul_of_nonneg_right hcγ hE.le, mul_nonneg hc hER.le]
  nlinarith [mul_le_mul_of_nonneg_left hkey hE.le]

/-- Along the inward normal, the Gaussian barrier grows at least linearly: for `0 ≤ κ` and
`0 ≤ t ≤ R`, `κ R exp (-κ R²) t ≤ exp (-κ (R - t)²) - exp (-κ R²)`. -/
private theorem mul_le_exp_neg_mul_sub_sq_sub {κ R t : ℝ} (hκ : 0 ≤ κ) (ht : 0 ≤ t)
    (htR : t ≤ R) :
    κ * R * Real.exp (-κ * R ^ 2) * t ≤ Real.exp (-κ * (R - t) ^ 2) - Real.exp (-κ * R ^ 2) := by
  have hsplit : Real.exp (-κ * (R - t) ^ 2) =
      Real.exp (-κ * R ^ 2) * Real.exp (κ * (2 * R * t - t ^ 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have h1 := Real.add_one_le_exp (κ * (2 * R * t - t ^ 2))
  have h2 : κ * (R * t) ≤ κ * (2 * R * t - t ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hκ
  rw [hsplit]
  nlinarith [Real.exp_pos (-κ * R ^ 2)]

/-- The core of Hopf's lemma, on a ball on whose closure `u` is continuous and on whose sphere
`u ≤ u x₀`: the barrier argument on the annulus `R / 2 ≤ ‖x - y‖ ≤ R`. -/
private theorem exists_pos_mul_le_sub_of_lt_ball_of_le_sphere [Nonempty ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (ha' : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β) (hc : ∀ x ∈ ball y R, 0 ≤ c x)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hcont : ContinuousOn u (closedBall y R))
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u x₀) (hlt : ∀ x ∈ ball y R, u x < u x₀)
    (hle : ∀ x ∈ sphere y R, u x ≤ u x₀) :
    ∃ C > 0, ∀ t ∈ Ioc 0 (R / 2), C * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  set ρ := R / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hyR : y ∈ ball y R := mem_ball_self hR
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hb y hyR)
  have hγ : 0 ≤ γ := (hc y hyR).trans (hcγ y hyR)
  -- The inner sphere carries a uniform positive margin `δ` below the maximum `u x₀`.
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere y ρ).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    (hcont.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))))
  set δ := u x₀ - u z with hδdef
  have hδ : 0 < δ := sub_pos.mpr (hlt z (sphere_subset_ball (by linarith) hz))
  -- The barrier `w`, with `κ` large enough for it to be a subsolution on the annulus.
  set κ := max 1 ((2 * (Fintype.card ι * Lam + β * R) + γ) / (4 * lam * ρ ^ 2)) with hκdef
  have hκ : 1 ≤ κ := le_max_left _ _
  have hκρ : 2 * (Fintype.card ι * Lam + β * R) + γ ≤ 4 * lam * ρ ^ 2 * κ := by
    rw [mul_comm _ κ, ← div_le_iff₀ (by positivity)]
    exact le_max_right _ _
  set w : EuclideanSpace ℝ ι → ℝ := fun z ↦ Real.exp (-κ * ‖z - y‖ ^ 2) - Real.exp (-κ * R ^ 2)
    with hwdef
  have hwcd : ContDiff ℝ 2 w := by
    simp only [hwdef]
    exact (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).exp.sub
      contDiff_const
  have hwle : ∀ x, w x ≤ 1 := fun x ↦ by
    have h1 : Real.exp (-κ * ‖x - y‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x - y‖])
    have h2 := Real.exp_pos (-κ * R ^ 2)
    simp only [hwdef]
    linarith
  have hwR : ∀ x ∈ sphere y R, w x = 0 := fun x hx ↦ by
    simp only [hwdef, mem_sphere_iff_norm.mp hx, sub_self]
  -- The closed annulus `K`.
  set K : Set (EuclideanSpace ℝ ι) := closedBall y R \ ball y ρ with hKdef
  have hKsub : K ⊆ closedBall y R := sdiff_subset
  have hKcompact : IsCompact K :=
    (isCompact_closedBall y R).of_isClosed_subset (isClosed_closedBall.sdiff isOpen_ball) hKsub
  have hKnorm : ∀ x ∈ K, ρ ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ R := fun x hx ↦ by
    simp only [hKdef, Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_lt] at hx
    exact ⟨hx.2, hx.1⟩
  have hKball : ∀ x ∈ interior K, x ∈ ball y R := fun x hx ↦ by
    simpa only [interior_closedBall y hR.ne'] using interior_mono hKsub hx
  -- The perturbation `v = u + δ w` is a subsolution on the open annulus.
  set v : EuclideanSpace ℝ ι → ℝ := u + δ • w with hvdef
  have hvcont : ContinuousOn v K :=
    (hcont.mono hKsub).add (hwcd.continuous.continuousOn.const_smul δ)
  have hvcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 v x := fun x hx ↦
    (hcd x (hKball x hx)).add (hwcd.contDiffAt.const_smul δ)
  have hvsub : ∀ ⦃x⦄, x ∈ interior K → c x * v x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ v x (b x) := fun x hx ↦ by
    have hxB := hKball x hx
    have hxK := hKnorm x (interior_subset hx)
    have hw := mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub hlam (ha x hxB)
      (ha' x hxB) (hb x hxB) (hc x hxB) (hcγ x hxB) hρ hxK.1 hxK.2 hκ hκρ
    rw [hvdef, sum_mul_fderiv_fderiv_add_fderiv_add_smul (hcd x hxB) hwcd.contDiffAt]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hsub x hxB, mul_le_mul_of_nonneg_left hw hδ.le]
  -- On the frontier of `K`, that is on the two spheres, `v ≤ u x₀`.
  have hvbdry : ∀ ⦃x⦄, x ∈ frontier K → v x ≤ u x₀ := fun x hx ↦ by
    have hxK := hKnorm x (hKcompact.isClosed.frontier_subset hx)
    simp only [hvdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hxK.2.eq_or_lt with hxR | hxR
    · rw [hwR x (mem_sphere_iff_norm.mpr hxR), mul_zero, add_zero]
      exact hle x (mem_sphere_iff_norm.mpr hxR)
    · have hxρ : ‖x - y‖ = ρ := by
        refine (hxK.1.eq_or_lt.resolve_right fun hlt' ↦ ?_).symm
        refine hx.2 (interior_maximal (t := ball y R \ closedBall y ρ) (fun z hz ↦ ?_)
          (isOpen_ball.sdiff isClosed_closedBall) ?_)
        · exact ⟨ball_subset_closedBall hz.1, fun h ↦ hz.2 (ball_subset_closedBall h)⟩
        · simp only [Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_le]
          exact ⟨hxR, hlt'⟩
      have hux : u x ≤ u z := hzmax (mem_sphere_iff_norm.mpr hxρ)
      nlinarith [hwle x]
  have hKmax := le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hKcompact hlam
    (fun x hx ↦ ha x (hKball x hx)) (fun x hx ↦ hb x (hKball x hx))
    (fun x hx ↦ hc x (hKball x hx)) hnonneg hvcont hvcd hvsub hvbdry
  -- Along the inward normal, `δ w` grows linearly.
  have hκ0 : (0 : ℝ) ≤ κ := by linarith
  refine ⟨δ * (κ * R * Real.exp (-κ * R ^ 2)), by positivity, fun t ht ↦ ?_⟩
  have htR : t ≤ R := by linarith [ht.2]
  have hnorm := norm_sub_smul_sub hR hx₀ htR
  have hmem : x₀ - t • (R⁻¹ • (x₀ - y)) ∈ K := by
    simp only [hKdef, Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, hnorm, not_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hv := hKmax hmem
  have hwt : w (x₀ - t • (R⁻¹ • (x₀ - y))) =
      Real.exp (-κ * (R - t) ^ 2) - Real.exp (-κ * R ^ 2) := by
    simp only [hwdef, hnorm]
  have hgrow := mul_le_exp_neg_mul_sub_sq_sub hκ0 ht.1.le htR
  simp only [hvdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwt] at hv
  nlinarith [mul_le_mul_of_nonneg_left hgrow hδ.le]

/-- **Hopf's boundary-point lemma for elliptic operators in non-divergence form.** Let `x₀` lie on
the sphere bounding `B = ball y R`, and on `B` let `λ ‖ξ‖² ≤ ξᵀ a(x) ξ ≤ Λ ‖ξ‖²` with `0 < λ`,
`‖b‖ ≤ β` and `0 ≤ c ≤ γ`. Let `u` be `C²` in `B`, continuous at `x₀` relative to `B`, a
subsolution `c u ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` in `B`, strictly below `u x₀` in `B`, with
`0 ≤ u x₀`. Then, with `ν = R⁻¹ (x₀ - y)` the outer unit normal of `B` at `x₀`, there is `C > 0`
such that `C t ≤ u x₀ - u (x₀ - t ν)` for `0 < t ≤ R / 4` (Gilbarg–Trudinger, Lemma 3.4).

Nothing is assumed of `u` off `B ∪ {x₀}`, and nothing of the coefficients off `B`. -/
theorem exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (ha' : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β) (hc : ∀ x ∈ ball y R, 0 ≤ c x)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u x₀) (hlt : ∀ x ∈ ball y R, u x < u x₀) :
    ∃ C > 0, ∀ t ∈ Ioc 0 (R / 4), C * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  -- In dimension zero the sphere is empty.
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    have hxy : x₀ = y := Subsingleton.elim _ _
    rw [hxy, mem_sphere, dist_self] at hx₀
    exact hR.ne hx₀
  -- Run the argument on the ball `B' = ball y' (R / 2)` internally tangent to `B` at `x₀`.
  set ν := R⁻¹ • (x₀ - y) with hνdef
  set y' := x₀ - (R / 2) • ν with hy'def
  have hR' : 0 < R / 2 := by positivity
  have hx₀y' : x₀ - y' = (R / 2) • ν := by simp only [hy'def]; abel
  have hν : ‖ν‖ = 1 := by
    rw [hνdef, norm_smul, mem_sphere_iff_norm.mp hx₀, norm_inv, Real.norm_of_nonneg hR.le,
      inv_mul_cancel₀ hR.ne']
  have hx₀' : x₀ ∈ sphere y' (R / 2) := by
    rw [mem_sphere_iff_norm, hx₀y', norm_smul, hν, mul_one, Real.norm_of_nonneg hR'.le]
  have hν' : (R / 2)⁻¹ • (x₀ - y') = ν := by
    rw [hx₀y', smul_smul, inv_mul_cancel₀ hR'.ne', one_smul]
  have hsub' : closedBall y' (R / 2) ⊆ insert x₀ (ball y R) := fun z hz ↦ by
    by_cases hzx₀ : z = x₀
    · exact hzx₀ ▸ mem_insert _ _
    · exact mem_insert_of_mem _ (mem_ball_of_mem_closedBall_sub_smul hR hx₀ hz hzx₀)
  have hball' : ball y' (R / 2) ⊆ ball y R := fun z hz ↦ by
    have hzx₀ : z ≠ x₀ := by
      rintro rfl
      exact (mem_sphere.mp hx₀').not_lt (mem_ball.mp hz) |>.elim
    exact mem_ball_of_mem_closedBall_sub_smul hR hx₀ (ball_subset_closedBall hz) hzx₀
  have hcont' : ContinuousOn u (closedBall y' (R / 2)) := fun z hz ↦ by
    by_cases hzx₀ : z = x₀
    · subst hzx₀
      exact (continuousWithinAt_insert_self.mpr hcont).mono hsub'
    · exact (hcd z (mem_ball_of_mem_closedBall_sub_smul hR hx₀ hz hzx₀)).continuousAt
        |>.continuousWithinAt
  have hle' : ∀ z ∈ sphere y' (R / 2), u z ≤ u x₀ := fun z hz ↦ by
    by_cases hzx₀ : z = x₀
    · rw [hzx₀]
    · exact (hlt z (mem_ball_of_mem_closedBall_sub_smul hR hx₀
        (sphere_subset_closedBall hz) hzx₀)).le
  obtain ⟨C, hC, hCt⟩ := exists_pos_mul_le_sub_of_lt_ball_of_le_sphere hR' hx₀' hlam
    (fun x hx ↦ ha x (hball' hx)) (fun x hx ↦ ha' x (hball' hx)) (fun x hx ↦ hb x (hball' hx))
    (fun x hx ↦ hc x (hball' hx)) (fun x hx ↦ hcγ x (hball' hx)) hcont'
    (fun x hx ↦ hcd x (hball' hx)) (fun x hx ↦ hsub x (hball' hx)) hnonneg
    (fun x hx ↦ hlt x (hball' hx)) hle'
  refine ⟨C, hC, fun t ht ↦ ?_⟩
  have h := hCt t (by rwa [div_div, show (2 : ℝ) * 2 = 4 by norm_num])
  rwa [hν'] at h

/-- **Hopf's boundary-point lemma at a zero maximum.** Under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`, but with
`u x₀ = 0` and no sign condition on `c`, only an upper bound `c ≤ γ`, the same conclusion holds:
since `u ≤ 0` in `B`, the subsolution inequality persists when `c` is replaced by `max c 0`. -/
theorem exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball_of_eq_zero
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (ha' : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x) (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hzero : u x₀ = 0) (hlt : ∀ x ∈ ball y R, u x < u x₀) :
    ∃ C > 0, ∀ t ∈ Ioc 0 (R / 4), C * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  refine exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    (c := fun x ↦ max (c x) 0) (γ := max γ 0) hR hx₀ hlam ha ha' hb
    (fun x _ ↦ le_max_right _ _) (fun x hx ↦ max_le_max_right 0 (hcγ x hx)) hcd hcont
    (fun x hx ↦ ?_) hzero.ge hlt
  have hu : u x < 0 := hzero ▸ hlt x hx
  refine le_trans ?_ (hsub x hx)
  rcases le_total (c x) 0 with hcx | hcx
  · rw [max_eq_right hcx, zero_mul]
    exact mul_nonneg_of_nonpos_of_nonpos hcx hu.le
  · rw [max_eq_left hcx]

/-- **Hopf's boundary-point lemma without zeroth-order term.** Under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`, but with
`0 ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` in `B`, the same conclusion holds with no sign condition on
`u x₀`. -/
theorem exists_pos_mul_le_sub_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : EuclideanSpace ℝ ι → ℝ} {lam Lam β R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (ha' : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hcont : ContinuousWithinAt u (ball y R) x₀)
    (hsub : ∀ x ∈ ball y R, 0 ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hlt : ∀ x ∈ ball y R, u x < u x₀) :
    ∃ C > 0, ∀ t ∈ Ioc 0 (R / 4), C * t ≤ u x₀ - u (x₀ - t • (R⁻¹ • (x₀ - y))) := by
  -- Apply the zero-maximum form to `u - u x₀`, which has the same derivatives as `u`.
  have hfd : fderiv ℝ (fun x ↦ u x - u x₀) = fderiv ℝ u := funext fun _ ↦ fderiv_sub_const _
  have h := exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball_of_eq_zero
    (u := fun x ↦ u x - u x₀) (c := 0) (γ := 0) hR hx₀ hlam ha ha' hb (fun _ _ ↦ le_rfl)
    (fun x hx ↦ (hcd x hx).sub contDiffAt_const) (hcont.sub continuousWithinAt_const)
    (fun x hx ↦ by simpa only [hfd, Pi.zero_apply, zero_mul] using hsub x hx) (sub_self _)
    (fun x hx ↦ sub_lt_sub_right (hlt x hx) _)
  simpa only [sub_sub_sub_cancel_right] using h

/-- **Hopf's boundary-point lemma, derivative form.** Under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`, if `u` is
moreover differentiable at `x₀`, then its derivative there in the outward normal direction is
positive: `0 < Du(x₀) (x₀ - y)`. -/
theorem fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {lam Lam β γ R : ℝ} {y x₀ : EuclideanSpace ℝ ι}
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (ha' : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β) (hc : ∀ x ∈ ball y R, 0 ≤ c x)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hderiv : DifferentiableAt ℝ u x₀)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u x₀) (hlt : ∀ x ∈ ball y R, u x < u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  obtain ⟨C, hC, hCt⟩ := exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    hR hx₀ hlam ha ha' hb hc hcγ hcd hderiv.continuousAt.continuousWithinAt hsub hnonneg hlt
  set ν := R⁻¹ • (x₀ - y)
  -- The difference quotients along the inward normal tend to `Du(x₀) ν` and stay above `C`.
  have hline : HasDerivAt (fun t : ℝ ↦ u (x₀ - t • ν)) (-fderiv ℝ u x₀ ν) 0 := by
    have hγ : HasDerivAt (fun t : ℝ ↦ x₀ - t • ν) (-ν) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub x₀
    have h := hderiv.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hγ (by simp)
    rwa [map_neg] at h
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ * (u x₀ - u (x₀ - t • ν))) (𝓝[>] 0)
      (𝓝 (fderiv ℝ u x₀ ν)) := by
    have h := hline.tendsto_slope_zero_right
    simp only [zero_add, zero_smul, sub_zero, smul_eq_mul] at h
    have h' := h.neg
    simp only [neg_neg] at h'
    refine h'.congr fun t ↦ ?_
    ring
  have hle : C ≤ fderiv ℝ u x₀ ν := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioc_mem_nhdsGT (by positivity : (0 : ℝ) < R / 4)] with t ht
    rw [le_inv_mul_iff₀ ht.1, mul_comm]
    exact hCt t ht
  have hx₀y : x₀ - y = R • ν := by
    simp only [ν, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [hx₀y, map_smul, smul_eq_mul]
  exact mul_pos hR (hC.trans_le hle)

end PDE

end TauCeti
