/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.InnerProductSpace.TouchingBall
import TauCeti.Topology.Connected.Basic

/-!
# Hopf's lemma and the strong maximum principle in non-divergence form

On `ℝⁿ = EuclideanSpace ℝ ι` consider the operator in non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`

with a variable coefficient matrix `a`, written as in
`TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence`. This file proves **Hopf's boundary-point
lemma** for `-L + c` and deduces the **strong maximum principle**.

Let `B = ball y R`, let `e` be a unit vector and `x₀ = y + R • e`. On `B` let
`λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ`, `tr a ≤ τ`, `‖b‖ ≤ β` and `0 ≤ c ≤ γ`. If `u` is `C²` on `B`,
continuous at `x₀` within `B`, a subsolution `c u ≤ L u` on `B` with `0 ≤ u x₀`, and `u < u x₀`
on `B`, then there is `κ > 0` with

`κ t ≤ u x₀ - u (x₀ - t • e)` for `0 < t ≤ R / 4`,

so the outward normal derivative at `x₀`, if it exists, is positive. The coefficients need no
continuity, symmetry or measurability, and `u` is only assumed continuous at `x₀` and not on the
rest of `∂B`; this is the form needed at a boundary point of a domain satisfying an interior
sphere condition. The sign condition `0 ≤ u x₀` can be dropped when `u x₀ = 0`, and then `c`
needs no sign, or when `c = 0`. The upper bound on `a` enters only through its trace; it is
implied by `ξᵀ a ξ ≤ Λ ‖ξ‖²` with `τ = n Λ`.

The proof is the classical barrier argument. First `u` is compared on the ball `B' = ball y' ρ`
of radius `ρ = R / 2` internally tangent to `B` at `x₀`, whose closure meets `∂B` only at `x₀`,
so that `u` is continuous on it. On the annulus `ρ / 2 ≤ ‖x - y'‖ ≤ ρ`, the Gaussian barrier
`w = exp (-α ‖· - y'‖²) - exp (-α ρ²)` satisfies
(`TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq`)

`L w = exp (-α ‖x - y'‖²) (4 α² (x - y')ᵀ a (x - y') - 2 α tr a - 2 α ⟪x - y', b⟫)`,

which dominates `c w` once `α` is large in terms of `τ / λ`, `β ρ / λ` and `γ ρ² / λ`. The weak
maximum principle `TauCeti.PDE.le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier` then
bounds `u + δ w` by `u x₀` on the annulus, where `δ` is the margin of `u` below `u x₀` on the
inner sphere, and `w` grows linearly along the inward ray.

The strong maximum principle follows as in
`TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple`: near a local maximum where
`u` is not locally constant, the largest ball about a point with a smaller value touches the level
set at a point `x₀` which is again a local maximum
(`TauCeti.eventually_eq_of_isLocalMax_of_forall_not_lt_ball`), so `fderiv ℝ u x₀ = 0`,
contradicting Hopf's lemma; preconnectedness then spreads local constancy
(`IsPreconnected.eqOn_const_of_eventually_eq`). The Laplacian case `a = 1` of both results is in
`TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma` and
`TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple`; the strong maximum
principle for weak solutions of equations in divergence form is
`TauCeti.Analysis.PDE.MaximumPrinciple.Strong`.

## Main declarations

All declarations are in the namespace `TauCeti.PDE`.

* `exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`:
  **Hopf's boundary-point lemma** for `-L + c` with `c ≥ 0`, in difference-quotient form.
* `fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`: its derivative
  form.
* `exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball_of_eq_zero`:
  Hopf's lemma at a zero maximum, with no sign condition on `c`.
* `exists_pos_mul_le_sub_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_lt_ball`:
  Hopf's lemma for `-L`, with no sign condition on `u x₀`.
* `eventually_eq_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isLocalMax`: the
  local strong maximum principle.
* `eqOn_const_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isMaxOn`: **the strong
  maximum principle** for `-L + c`, `c ≥ 0`, on a preconnected open set.
* `eqOn_const_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_isMaxOn`: the strong
  maximum principle for `-L`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.2 (Lemma 3.4 and Theorem 3.5).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.4.2.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter Matrix Metric Set Topology RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-! ### The Gaussian barrier -/

/-- The point at distance `t ≤ R` from `y + R • e` along the inward ray lies at distance `R - t`
from `y`. -/
private theorem norm_add_smul_sub_smul_sub {y e : EuclideanSpace ℝ ι} {R t : ℝ} (he : ‖e‖ = 1)
    (htR : t ≤ R) : ‖y + R • e - t • e - y‖ = R - t := by
  rw [show y + R • e - t • e - y = (R - t) • e by module, norm_smul, he, mul_one,
    Real.norm_of_nonneg (by linarith)]

/-- The Hopf barrier `w = exp (-α ‖· - y‖²) - exp (-α R²)` along the inward ray from
`y + R • e`: at distance `t ∈ (0, R]` from the sphere it is at least `exp (-α R²) α R t`. -/
private theorem mul_le_hopfBarrier_sub_smul {y e : EuclideanSpace ℝ ι} {R α t : ℝ}
    (he : ‖e‖ = 1) (hα : 0 ≤ α) (ht : 0 ≤ t) (htR : t ≤ R) :
    Real.exp (-α * R ^ 2) * α * R * t ≤
      Real.exp (-α * ‖y + R • e - t • e - y‖ ^ 2) - Real.exp (-α * R ^ 2) := by
  have hsplit : -α * (R - t) ^ 2 = -α * R ^ 2 + α * t * (2 * R - t) := by ring
  rw [norm_add_smul_sub_smul_sub he htR, hsplit, Real.exp_add]
  have h1 := Real.add_one_le_exp (α * t * (2 * R - t))
  have h2 : α * R * t ≤ α * t * (2 * R - t) := by nlinarith [mul_nonneg hα ht]
  have hK := (Real.exp_pos (-α * R ^ 2)).le
  nlinarith [mul_le_mul_of_nonneg_left h2 hK]

variable [DecidableEq ι]

/-- **The Hopf barrier is a subsolution on an annulus.** Let `λ ‖ξ‖² ≤ ξᵀ A ξ` with `0 ≤ λ`,
`tr A ≤ τ`, `‖v‖ ≤ β` and `0 ≤ c ≤ γ`. If `1 ≤ α` and `2 (τ + R β) + γ ≤ α λ R²`, then the barrier
`w = exp (-α ‖· - y‖²) - exp (-α R²)` satisfies `c w ≤ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw + ∂_v w` at every point `x`
of the annulus `R / 2 ≤ ‖x - y‖ ≤ R`. -/
private theorem mul_le_sum_mul_fderiv_fderiv_add_fderiv_hopfBarrier {A : Matrix ι ι ℝ}
    {y x v : EuclideanSpace ℝ ι} {R α lam τ β γ c : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (htr : A.trace ≤ τ)
    (hv : ‖v‖ ≤ β) (hc : 0 ≤ c) (hcγ : c ≤ γ) (hα : 1 ≤ α)
    (hαbig : 2 * (τ + R * β) + γ ≤ α * (lam * R ^ 2)) (hx₁ : R / 2 ≤ ‖x - y‖)
    (hx₂ : ‖x - y‖ ≤ R) :
    c * (Real.exp (-α * ‖x - y‖ ^ 2) - Real.exp (-α * R ^ 2)) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ ι ↦
          Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * R ^ 2)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) +
        fderiv ℝ (fun z : EuclideanSpace ℝ ι ↦
          Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * R ^ 2)) x v := by
  rw [sum_mul_fderiv_fderiv_add_fderiv_sub_const,
    sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq]
  have hE : 0 < Real.exp (-α * ‖x - y‖ ^ 2) := Real.exp_pos _
  have hK : 0 < Real.exp (-α * R ^ 2) := Real.exp_pos _
  have hR : 0 ≤ R := (norm_nonneg _).trans hx₂
  have hβ : 0 ≤ β := (norm_nonneg _).trans hv
  have hγ : 0 ≤ γ := hc.trans hcγ
  -- The principal part is at least `α² λ R²`, the other two terms at least `-2 α (τ + R β)`.
  have hsq : (R / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hx₁ 2
  have hQ : lam * R ^ 2 ≤ 4 * (A.toQuadraticForm' (x - y)) := by
    have h := (mul_le_mul_of_nonneg_left hsq hlam).trans (hA (x - y))
    rw [WithLp.ofLp_sub] at h
    linarith
  have hinner : ⟪x - y, v⟫ ≤ R * β :=
    (real_inner_le_norm _ _).trans (mul_le_mul hx₂ hv (norm_nonneg _) hR)
  have hbracket : γ ≤ 4 * α ^ 2 * A.toQuadraticForm' (x - y) - 2 * α * A.trace -
      2 * α * ⟪x - y, v⟫ := by
    have h1 : α * (lam * R ^ 2) ≤ α * (4 * A.toQuadraticForm' (x - y)) :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    have h2 : α * (2 * (τ + R * β) + γ) ≤ α * (α * (lam * R ^ 2)) :=
      mul_le_mul_of_nonneg_left hαbig (by linarith)
    have h3 : α * A.trace ≤ α * τ := mul_le_mul_of_nonneg_left htr (by linarith)
    have h4 : α * ⟪x - y, v⟫ ≤ α * (R * β) := mul_le_mul_of_nonneg_left hinner (by linarith)
    nlinarith
  calc c * (Real.exp (-α * ‖x - y‖ ^ 2) - Real.exp (-α * R ^ 2))
      ≤ γ * Real.exp (-α * ‖x - y‖ ^ 2) := by nlinarith
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hbracket hE.le

/-- The core of Hopf's lemma, with continuity on the closed ball and a weak bound on the sphere:
the barrier argument on the annulus `R / 2 ≤ ‖x - y‖ ≤ R`. -/
private theorem exists_pos_mul_le_sub_of_lt_ball_of_le_sphere
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam τ β γ : ℝ} (hR : 0 < R)
    (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ τ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hucont : ContinuousOn u (closedBall y R)) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u (y + R • e)) (hlt : ∀ x ∈ ball y R, u x < u (y + R • e))
    (hle : ∀ x ∈ sphere y R, u x ≤ u (y + R • e)) :
    ∃ κ, 0 < κ ∧ ∀ t ∈ Ioc 0 (R / 2), κ * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  -- The unit vector `e` makes the index type nonempty.
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    rw [Subsingleton.elim e 0, norm_zero] at he
    exact zero_ne_one he
  have hy : y ∈ ball y R := mem_ball_self hR
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hb y hy)
  have hγ : 0 ≤ γ := (hc y hy).trans (hcγ y hy)
  set x₀ : EuclideanSpace ℝ ι := y + R • e with hx₀
  -- The barrier exponent.
  set α : ℝ := max 1 ((2 * (τ + R * β) + γ) / (lam * R ^ 2)) with hαdef
  have hα : 1 ≤ α := le_max_left _ _
  have hαbig : 2 * (τ + R * β) + γ ≤ α * (lam * R ^ 2) :=
    (div_le_iff₀ (by positivity)).mp (le_max_right _ _)
  -- The inner sphere carries a uniform positive margin `δ` below the maximum `u x₀`.
  have hhalf : (0 : ℝ) < R / 2 := by linarith
  obtain ⟨z, hzball, hzmax⟩ := (isCompact_closedBall y (R / 2)).exists_isMaxOn
    (nonempty_closedBall.mpr hhalf.le)
    (hucont.mono (closedBall_subset_closedBall (by linarith)))
  set δ : ℝ := u x₀ - u z with hδdef
  have hδ : 0 < δ := sub_pos.mpr (hlt z (closedBall_subset_ball (by linarith) hzball))
  -- The closed annulus.
  set K : Set (EuclideanSpace ℝ ι) := closedBall y R \ ball y (R / 2) with hKdef
  have hKsub : K ⊆ closedBall y R := sdiff_subset
  have hKcompact : IsCompact K := (isCompact_closedBall y R).diff isOpen_ball
  have hKnorm : ∀ w ∈ K, R / 2 ≤ ‖w - y‖ ∧ ‖w - y‖ ≤ R := by
    intro w hw
    simp only [hKdef, Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_lt] at hw
    exact ⟨hw.2, hw.1⟩
  have hKball : ∀ w ∈ interior K, w ∈ ball y R := fun w hw ↦
    ((interior_closedBall_sdiff_ball y hhalf.ne' hR.ne').subset hw).1
  -- The perturbation `v = u + δ w` by the Hopf barrier `w`.
  set w : EuclideanSpace ℝ ι → ℝ :=
    fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * R ^ 2) with hwdef
  have hwcd : ContDiff ℝ 2 w :=
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).exp.sub
      contDiff_const
  have hwle : ∀ z, w z ≤ 1 := by
    intro z
    have h1 : Real.exp (-α * ‖z - y‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z - y‖])
    have h2 := Real.exp_pos (-α * R ^ 2)
    simp only [hwdef]
    linarith
  have hKmax : ∀ ⦃x⦄, x ∈ K → (u + δ • w) x ≤ u x₀ := by
    refine le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hKcompact hlam
      (fun x hx ↦ ha x (hKball x hx)) (fun x hx ↦ hb x (hKball x hx))
      (fun x hx ↦ hc x (hKball x hx)) hnonneg
      ((hucont.mono hKsub).add (hwcd.continuous.continuousOn.const_smul δ))
      (fun x hx ↦ (hcd x (hKball x hx)).add (hwcd.contDiffAt.const_smul δ)) ?_ ?_
    · intro x hx
      have hxb := hKball x hx
      rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hcd x hxb) hwcd.contDiffAt]
      have hxK := hKnorm x (interior_subset hx)
      have hbar := mul_le_sum_mul_fderiv_fderiv_add_fderiv_hopfBarrier (A := a x) (v := b x)
        hlam.le (ha x hxb) (htr x hxb) (hb x hxb) (hc x hxb) (hcγ x hxb) hα hαbig hxK.1 hxK.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hsub x hxb, mul_le_mul_of_nonneg_left hbar hδ.le]
    · intro x hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases frontier_closedBall_sdiff_ball_subset y (R / 2) R hx with houter | hinner
      · -- On the outer sphere the barrier vanishes.
        have hw0 : w x = 0 := by simp only [hwdef, mem_sphere_iff_norm.mp houter, sub_self]
        rw [hw0, mul_zero, add_zero]
        exact hle x houter
      · -- On the inner sphere the margin `δ` absorbs the barrier.
        have hux : u x ≤ u z := hzmax (sphere_subset_closedBall hinner)
        nlinarith [mul_le_mul_of_nonneg_left (hwle x) hδ.le]
  -- Along the inward ray the barrier grows linearly.
  refine ⟨δ * (Real.exp (-α * R ^ 2) * α * R), by positivity, fun t ht ↦ ?_⟩
  have htK : x₀ - t • e ∈ K := by
    simp only [hKdef, Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, hx₀,
      norm_add_smul_sub_smul_sub he (by linarith [ht.2] : t ≤ R), not_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hv := hKmax htK
  have hbarrier := mul_le_hopfBarrier_sub_smul (y := y) (e := e) (R := R) (α := α) (t := t) he
    (by linarith) ht.1.le (by linarith [ht.2])
  rw [← hx₀] at hbarrier
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwdef] at hv
  nlinarith [mul_le_mul_of_nonneg_left hbarrier hδ.le]

/-! ### Hopf's boundary-point lemma -/

/-- **Hopf's boundary-point lemma for elliptic operators in non-divergence form.** Let `e` be a
unit vector and `x₀ = y + R • e` the point where the outward ray in direction `e` meets the sphere
`∂B` of `B = ball y R`. On `B` let `a` satisfy `λ ‖ξ‖² ≤ ξᵀ a(x) ξ` with `0 < λ` and `tr a(x) ≤ τ`,
let `‖b‖ ≤ β` and `0 ≤ c ≤ γ`. Let `u` be `C²` on `B`, continuous at `x₀` within `B`, and a
subsolution `c u ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` there, with `0 ≤ u x₀` and `u < u x₀` on `B`. Then the
inward difference quotients `(u x₀ - u (x₀ - t • e)) / t` are bounded below by a positive constant
`κ` for `0 < t ≤ R / 4`.

No continuity or symmetry of the coefficients is assumed, and nothing is assumed of `u` on `∂B`
except at `x₀`. The trace bound is implied by `ξᵀ a(x) ξ ≤ Λ ‖ξ‖²`, with `τ = n Λ`. The sign
condition `0 ≤ u x₀` is needed only because of `c`; see
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball_of_eq_zero` and
`exists_pos_mul_le_sub_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_lt_ball` for the other two
cases of Gilbarg–Trudinger, Lemma 3.4. -/
theorem exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam τ β γ : ℝ} (hR : 0 < R)
    (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ τ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hcont : ContinuousWithinAt u (ball y R) (y + R • e))
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u (y + R • e)) (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) :
    ∃ κ, 0 < κ ∧ ∀ t ∈ Ioc 0 (R / 4), κ * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  -- Pass to the ball of radius `R / 2` internally tangent to `ball y R` at `x₀`.
  set y' : EuclideanSpace ℝ ι := y + (R / 2) • e
  have hx₀ : y' + (R / 2) • e = y + R • e := by module
  have hball : ball y' (R / 2) ⊆ ball y R := ball_subset_ball' (by
    rw [dist_eq_norm, show y' - y = (R / 2) • e by module, norm_smul, he, mul_one,
      Real.norm_of_nonneg (by linarith)]
    linarith)
  have hclosed : ∀ z ∈ closedBall y' (R / 2), z = y + R • e ∨ z ∈ ball y R := fun z hz ↦
    or_iff_not_imp_left.mpr (mem_ball_of_mem_closedBall_half_of_ne he hz)
  have hucont : ContinuousOn u (closedBall y' (R / 2)) := by
    intro z hz
    rcases hclosed z hz with rfl | hzb
    · exact (continuousWithinAt_insert_self.mpr hcont).mono fun w hw ↦ hclosed w hw
    · exact (hcd z hzb).continuousAt.continuousWithinAt
  obtain ⟨κ, hκ, hbound⟩ := exists_pos_mul_le_sub_of_lt_ball_of_le_sphere (R := R / 2)
    (by linarith) he hlam (fun x hx ↦ ha x (hball hx)) (fun x hx ↦ htr x (hball hx))
    (fun x hx ↦ hb x (hball hx)) (fun x hx ↦ hc x (hball hx)) (fun x hx ↦ hcγ x (hball hx))
    hucont (fun x hx ↦ hcd x (hball hx)) (fun x hx ↦ hsub x (hball hx)) (hx₀ ▸ hnonneg)
    (fun x hx ↦ hx₀ ▸ hlt x (hball hx))
    (fun x hx ↦ by
      rcases hclosed x (sphere_subset_closedBall hx) with rfl | hxb
      · exact hx₀.symm ▸ le_rfl
      · exact hx₀ ▸ (hlt x hxb).le)
  refine ⟨κ, hκ, fun t ht ↦ ?_⟩
  have h := hbound t ⟨ht.1, by linarith [ht.2]⟩
  rwa [hx₀] at h

/-- **Hopf's boundary-point lemma, derivative form.** Under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`, if `u` is
differentiable at `x₀ = y + R • e`, then its outward normal derivative there is positive:
`0 < fderiv ℝ u x₀ e`. -/
theorem fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam τ β γ : ℝ} (hR : 0 < R)
    (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ τ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hderiv : DifferentiableAt ℝ u (y + R • e)) (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u (y + R • e)) (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) :
    0 < fderiv ℝ u (y + R • e) e := by
  obtain ⟨κ, hκ, hbound⟩ :=
    exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball hR he hlam ha
      htr hb hc hcγ hderiv.continuousAt.continuousWithinAt hcd hsub hnonneg hlt
  exact hκ.trans_le (le_fderiv_of_mul_le_sub (by linarith) hderiv hbound)

/-- **Hopf's boundary-point lemma at a zero maximum.** If `u x₀ = 0`, the zeroth-order coefficient
needs no sign: under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball` with `0 ≤ c`
dropped, the inward difference quotients at `x₀ = y + R • e` are bounded below by a positive
constant for `0 < t ≤ R / 4`. -/
theorem exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball_of_eq_zero
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam τ β γ : ℝ} (hR : 0 < R)
    (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ τ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcγ : ∀ x ∈ ball y R, c x ≤ γ) (hcont : ContinuousWithinAt u (ball y R) (y + R • e))
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hzero : u (y + R • e) = 0) (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) :
    ∃ κ, 0 < κ ∧ ∀ t ∈ Ioc 0 (R / 4), κ * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  -- Where `u < 0`, replacing `c` by its positive part keeps `u` a subsolution.
  refine exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    (c := fun x ↦ max (c x) 0) (γ := max γ 0) hR he hlam ha htr hb (fun _ _ ↦ le_max_right _ _)
    (fun x hx ↦ max_le_max_right 0 (hcγ x hx)) hcont hcd (fun x hx ↦ ?_) hzero.ge hlt
  have hux : u x < 0 := hzero ▸ hlt x hx
  exact (mul_le_mul_of_nonpos_right (le_max_left _ _) hux.le).trans (hsub x hx)

/-- **Hopf's boundary-point lemma without zeroth-order term.** Under the hypotheses of
`exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball` with `c = 0`, so
that `u` is a subsolution `0 ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`, no sign condition on `u x₀` is needed. -/
theorem exists_pos_mul_le_sub_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam τ β : ℝ} (hR : 0 < R)
    (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ τ) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcont : ContinuousWithinAt u (ball y R) (y + R • e))
    (hcd : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, 0 ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) :
    ∃ κ, 0 < κ ∧ ∀ t ∈ Ioc 0 (R / 4), κ * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  obtain ⟨κ, hκ, hbound⟩ :=
    exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
      (u := fun z ↦ u z - u (y + R • e)) (c := 0) (γ := 0) hR he hlam ha htr hb
      (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) (hcont.sub continuousWithinAt_const)
      (fun x hx ↦ (hcd x hx).sub contDiffAt_const)
      (fun x hx ↦ by
        rw [sum_mul_fderiv_fderiv_add_fderiv_sub_const, Pi.zero_apply, zero_mul]
        exact hsub x hx)
      (by simp) (fun x hx ↦ sub_lt_sub_right (hlt x hx) _)
  exact ⟨κ, hκ, fun t ht ↦ by simpa using hbound t ht⟩

/-! ### The strong maximum principle -/

/-- **Local strong maximum principle for elliptic operators in non-divergence form.** Let `u` be
`C²` at a local maximum point `x` with `0 ≤ u x`, and near `x` let `a` satisfy
`λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ` and `tr a ≤ τ`, let `‖b‖ ≤ β` and `0 ≤ c ≤ γ`, and let `u` be a
subsolution `c u ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`. Then `u` is constant on a neighbourhood of `x`. -/
theorem eventually_eq_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isLocalMax
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι} {lam τ β γ : ℝ} (hlam : 0 < lam)
    (ha : ∀ᶠ y in 𝓝 x, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ)
    (htr : ∀ᶠ y in 𝓝 x, (a y).trace ≤ τ) (hb : ∀ᶠ y in 𝓝 x, ‖b y‖ ≤ β)
    (hc : ∀ᶠ y in 𝓝 x, 0 ≤ c y) (hcγ : ∀ᶠ y in 𝓝 x, c y ≤ γ) (hcd : ContDiffAt ℝ 2 u x)
    (hsub : ∀ᶠ y in 𝓝 x, c y * u y ≤
      ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u y (b y))
    (hnonneg : 0 ≤ u x) (hmax : IsLocalMax u x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  -- A ball inside the neighbourhood where the hypotheses hold, touching the level set `{u = u x}`
  -- from inside at a local maximum `x₀`, would make the outward derivative at `x₀` positive.
  refine eventually_eq_of_isLocalMax_of_forall_not_lt_ball
    ((hcd.eventually (by simp)).and (ha.and (htr.and (hb.and (hc.and (hcγ.and hsub))))))
    ((hcd.eventually (by simp)).mono fun y hy ↦ hy.continuousAt) hmax
    fun y e R hR he hball hx₀max hx₀ hlt ↦ ?_
  choose hcdB haB htrB hbB hcB hcγB hsubB using
    fun z (hz : z ∈ ball y R) ↦ hball (ball_subset_closedBall hz)
  have hx₀mem : y + R • e ∈ closedBall y R := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_of_nonneg hR.le]
  have hpos := fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball hR he hlam haB
    htrB hbB hcB hcγB ((hball hx₀mem).1.differentiableAt (by simp)) hcdB hsubB
    (hx₀ ▸ hnonneg) hlt
  rw [hx₀max.fderiv_eq_zero] at hpos
  exact lt_irrefl _ hpos

/-- **The strong maximum principle for elliptic operators in non-divergence form.** Let `U` be a
preconnected open set. On `U` let `a` be locally uniformly elliptic, with locally bounded trace,
and let `b` and `c ≥ 0` be locally bounded. A function that is `C²` on `U`, is a subsolution
`c u ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` there, and attains a nonnegative maximum over `U` at a point
`z ∈ U`, is constant on `U`.

The sign condition `0 ≤ u z` is needed only because of `c`; see
`eqOn_const_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_isMaxOn` for `c = 0`. -/
theorem eqOn_const_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isMaxOn
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {U : Set (EuclideanSpace ℝ ι)} {z : EuclideanSpace ℝ ι}
    (hU : IsOpen U) (hz : z ∈ U) (hUconn : IsPreconnected U)
    (ha : ∀ x ∈ U, ∃ lam > 0, ∀ᶠ y in 𝓝 x, ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ)
    (htr : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ (a y).trace)
    (hb : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ ‖b y‖) (hc : ∀ x ∈ U, 0 ≤ c x)
    (hcγ : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ U, c x * u x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hnonneg : 0 ≤ u z) (hmax : IsMaxOn u U z) :
    EqOn u (Function.const _ (u z)) U := by
  -- By preconnectedness it suffices that `u` is identically `u z` near every point of `U` at which
  -- it takes the value `u z`: this is the local principle.
  refine hUconn.eqOn_const_of_eventually_eq hz (fun x hx ↦ (hcd x hx).continuousAt)
    fun x hx hxz ↦ ?_
  have hxmax : IsMaxOn u U x := isMaxOn_iff.mpr fun y hy ↦ by
    rw [hxz]
    exact isMaxOn_iff.mp hmax y hy
  have hxnonneg : 0 ≤ u x := by
    rw [hxz]
    exact hnonneg
  obtain ⟨lam, hlam, hax⟩ := ha x hx
  obtain ⟨τ, hτ⟩ := htr x hx
  obtain ⟨β, hβ⟩ := hb x hx
  obtain ⟨γ, hγ⟩ := hcγ x hx
  have h1 : ∀ᶠ y in 𝓝 x, (a y).trace ≤ τ := eventually_map.mp hτ
  have h2 : ∀ᶠ y in 𝓝 x, ‖b y‖ ≤ β := eventually_map.mp hβ
  have h3 : ∀ᶠ y in 𝓝 x, c y ≤ γ := eventually_map.mp hγ
  have h4 : ∀ᶠ y in 𝓝 x, 0 ≤ c y := eventually_of_mem (hU.mem_nhds hx) hc
  have h5 : ∀ᶠ y in 𝓝 x, c y * u y ≤
      ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u y (b y) :=
    eventually_of_mem (hU.mem_nhds hx) hsub
  have h := eventually_eq_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isLocalMax hlam hax h1
    h2 h4 h3 (hcd x hx) h5 hxnonneg (hxmax.isLocalMax (hU.mem_nhds hx))
  exact h.mono fun y hy ↦ hy.trans hxz

/-- **The strong maximum principle without zeroth-order term.** Let `U` be a preconnected open
set, on which `a` is locally uniformly elliptic with locally bounded trace and `b` is locally
bounded. A function that is `C²` on `U`, satisfies `0 ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` there, and attains
its maximum over `U` at a point `z ∈ U`, is constant on `U`. -/
theorem eqOn_const_of_sum_mul_fderiv_fderiv_add_fderiv_nonneg_of_isMaxOn
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : EuclideanSpace ℝ ι → ℝ} {U : Set (EuclideanSpace ℝ ι)} {z : EuclideanSpace ℝ ι}
    (hU : IsOpen U) (hz : z ∈ U) (hUconn : IsPreconnected U)
    (ha : ∀ x ∈ U, ∃ lam > 0, ∀ᶠ y in 𝓝 x, ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a y).toQuadraticForm' ξ)
    (htr : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ (a y).trace)
    (hb : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ ‖b y‖)
    (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ U, 0 ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hmax : IsMaxOn u U z) :
    EqOn u (Function.const _ (u z)) U := by
  have h := eqOn_const_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_isMaxOn
    (u := fun x ↦ u x - u z) (c := 0) hU hz hUconn ha htr hb (fun _ _ ↦ le_rfl)
    (fun _ _ ↦ isBoundedUnder_const) (fun x hx ↦ (hcd x hx).sub contDiffAt_const)
    (fun x hx ↦ by
      rw [sum_mul_fderiv_fderiv_add_fderiv_sub_const, Pi.zero_apply, zero_mul]
      exact hsub x hx)
    (by simp) (fun x hx ↦ by simpa using hmax hx)
  exact fun x hx ↦ by simpa [sub_eq_zero] using h hx

end PDE

end TauCeti
