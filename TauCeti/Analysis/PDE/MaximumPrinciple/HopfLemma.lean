/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Hopf's boundary-point lemma for elliptic operators in non-divergence form

Let `B = ball y R ⊆ ℝⁿ = EuclideanSpace ℝ ι`, let `e` be a unit vector and let `x₀ = y + R • e`
be the point where the outward ray in direction `e` meets the sphere `∂B`. This file proves
**Hopf's boundary-point lemma** for the operator in non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`

with a variable coefficient matrix `a`, elliptic with constant `λ > 0` in the sense that
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ`, with bounded trace `tr a(x) ≤ T`, and with a drift `‖b‖ ≤ β` and a
zeroth-order coefficient `|c| ≤ γ`, all on `B`. The notation is that of
`TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence`: `∂ᵢ∂ⱼu` at `x` is
`fderiv ℝ (fderiv ℝ u) x eᵢ eⱼ`, a subsolution satisfies `c u ≤ L u`, and the zeroth-order
coefficient enters with the sign `c ≥ 0` of the weak maximum principle there (that is,
`-L + c` is the operator; in the convention `L + c` of Gilbarg and Trudinger the sign of `c` is
reversed).

If `u` is `C²` on `B`, is a subsolution there, is continuous at `x₀` relative to `B`, and
`u x < u x₀` for every `x ∈ B`, then `u` decreases at least linearly along the inward radius:
there are `ε, δ > 0` with `ε t ≤ u x₀ - u (x₀ - t • e)` for `0 < t < δ`. This holds in each of
the three classical cases: `c = 0`; `c ≥ 0` and `u x₀ ≥ 0`; and `u x₀ = 0` with no sign
condition on `c`. When `u` is differentiable at `x₀`, the outward derivative is then positive,
`0 < ∂ₑu(x₀)`.

The coefficients need no regularity, not even measurability, and `a` need not be symmetric. Unlike
the weak maximum principle, the lemma also uses an upper bound on `a`, here only in the form of a
trace bound `tr a ≤ T`; a coefficient field with `TauCeti.PDE.UniformlyEllipticOn (ball y R) a λ Λ`
has `tr a ≤ (card ι) Λ`. The conclusion only involves `u` on `B` and at `x₀`, so for a domain `Ω`
with an interior ball `B ⊆ Ω` touching `∂Ω` at `x₀` one applies the lemma to `B`.

The Laplacian with lower-order terms, `a = 1`, is
`TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma`, which works with a radial power
barrier in an arbitrary finite-dimensional inner product space.

## The argument

The proof is the classical one with the Gaussian barrier `v = exp (-α ‖x - y'‖²) - exp (-α r²)`,
which vanishes on the sphere of radius `r` about `y'`. The operator applied to the Gaussian
`g = exp (-α ‖x - y'‖²)` is `g (4 α² (x - y')ᵀ a (x - y') - 2 α tr a - 2 α ⟪x - y', b⟫)`
(`TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq`), so for `α` large the
barrier is a subsolution on every annulus `ρ ≤ ‖x - y'‖ ≤ r` with `ρ > 0`. One first replaces `B`
by the ball of radius `r = R / 2` internally tangent to `B` at `x₀`, whose closure meets `∂B`
only at `x₀`, so that `u` is continuous on that closure. On the annulus `r / 2 ≤ ‖x - y'‖ ≤ r`,
the weak maximum principle `le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier` bounds
`u + δ v` by `u x₀`, where `δ > 0` is the margin of `u` below `u x₀` on the inner sphere; along
the inward radius `v` grows at least linearly. The case `u x₀ = 0` reduces to `c ≥ 0` by
replacing `c` with `max c 0`, since `u < 0` on `B`, and the case `c = 0` reduces to it by
subtracting the constant `u x₀`.

## Main declarations

* `TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq`: the operator
  `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v` applied to the Gaussian `exp (-α ‖x - y‖²)`.
* `TauCeti.PDE.exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`:
  **Hopf's boundary-point lemma**, as a linear lower bound on the inward difference quotients.
* `TauCeti.PDE.fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`: its derivative
  form, for `u` differentiable at `x₀`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4.
* E. Hopf, *A remark on linear elliptic differential equations of second order*,
  Proc. Amer. Math. Soc. 3 (1952), 791–793.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Matrix Metric Set Filter Topology RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Gaussian barrier.** The operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v` applied to the Gaussian
`x ↦ exp (-α ‖x - y‖²)` is
`exp (-α ‖x - y‖²) (4 α² (x - y)ᵀ A (x - y) - 2 α tr A - 2 α ⟪x - y, v⟫)`. -/
theorem sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq {A : Matrix ι ι ℝ} {α : ℝ}
    {y x v : EuclideanSpace ℝ ι} :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x v =
    Real.exp (-α * ‖x - y‖ ^ 2) *
      (4 * α ^ 2 * A.toQuadraticForm' (x - y) - 2 * α * A.trace - 2 * α * ⟪x - y, v⟫) := by
  -- The Gaussian is `φ ∘ q` with `φ s = exp (-α s)` and `q z = ‖z - y‖²`.
  let q : EuclideanSpace ℝ ι → ℝ := fun z ↦ ‖z - y‖ ^ 2
  let φ : ℝ → ℝ := fun s ↦ Real.exp (-α * s)
  have hcomp : (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) = φ ∘ q := rfl
  have hq : ContDiffAt ℝ 2 q x :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hφ : ContDiffAt ℝ 2 φ (q x) := by fun_prop
  have hD1 (w : EuclideanSpace ℝ ι) : fderiv ℝ q x w = 2 * ⟪x - y, w⟫ := by
    have h := fderiv_norm_sq_sub_comp (i := id) (a := y) (x := x) differentiableAt_id
    simpa [q, inner_sub_left] using congrArg (· w) h
  have hid : fderiv ℝ (fderiv ℝ (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) x = 0 := by
    have h : fderiv ℝ (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =
        fun _ ↦ ContinuousLinearMap.id ℝ _ := funext fun _ ↦ fderiv_id
    rw [h]
    exact fderiv_const_apply _
  have hD2 (w w' : EuclideanSpace ℝ ι) : fderiv ℝ (fderiv ℝ q) x w w' = 2 * ⟪w, w'⟫ := by
    have h := fderiv_fderiv_norm_sq_sub_comp_apply (i := id) (a := y) (x := x) contDiffAt_id w w'
    simpa [q, hid] using h
  have hφ1 : deriv φ = fun s ↦ -α * φ s := funext fun s ↦ by
    have h := ((hasDerivAt_id s).const_mul (-α)).exp
    simpa [φ, mul_comm] using h.deriv
  have hφ2 : iteratedDeriv 2 φ = fun s ↦ α ^ 2 * φ s := funext fun s ↦ by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hφ1]
    have h := (((hasDerivAt_id s).const_mul (-α)).exp).const_mul (-α)
    simp only [id] at h
    rw [h.deriv]
    simp [φ]
    ring
  rw [hcomp, fderiv_comp x (hφ.differentiableAt two_ne_zero) (hq.differentiableAt two_ne_zero)]
  simp only [fderiv_fderiv_scalar_comp_apply hφ hq, smul_eq_mul, hD1, hD2, hφ1, hφ2,
    ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, EuclideanSpace.inner_single_right]
  -- Pair the Hessian with `A`: the rank-one part gives the quadratic form, the identity part the
  -- trace.
  have hQ : ∑ i, ∑ j, A i j * ((x - y) i * (x - y) j) = A.toQuadraticForm' (x - y) := by
    simp only [toQuadraticForm'_apply, dotProduct, mulVec, Finset.mul_sum, WithLp.ofLp_sub,
      Pi.sub_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have htr : ∑ i, ∑ j, A i j * (Pi.single j (1 : ℝ) : ι → ℝ) i = A.trace := by
    simp [Pi.single_apply, Matrix.trace]
  calc
    _ = ∑ i, ∑ j, (4 * α ^ 2 * φ (q x) * (A i j * ((x - y) i * (x - y) j)) -
          2 * α * φ (q x) * (A i j * (Pi.single j (1 : ℝ) : ι → ℝ) i)) +
          2 * ⟪x - y, v⟫ * (-α * φ (q x)) := by
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hij : i = j
      · subst hij
        simp
        ring
      · simp [hij, Ne.symm hij]
        ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hQ, htr, φ, q]
      ring

/-- Along the inward radius the Gaussian barrier grows at least linearly: for `0 ≤ α` and
`0 ≤ t ≤ s`, `α s t exp (-α s²) ≤ exp (-α (s - t)²) - exp (-α s²)`. -/
private theorem mul_exp_le_exp_neg_mul_sub_sq_sub {α s t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t)
    (hts : t ≤ s) :
    α * s * t * Real.exp (-α * s ^ 2) ≤ Real.exp (-α * (s - t) ^ 2) - Real.exp (-α * s ^ 2) := by
  have hsplit : Real.exp (-α * (s - t) ^ 2) =
      Real.exp (-α * s ^ 2) * Real.exp (α * (s ^ 2 - (s - t) ^ 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hE := Real.exp_pos (-α * s ^ 2)
  have h1 := Real.add_one_le_exp (α * (s ^ 2 - (s - t) ^ 2))
  have h2 : α * s * t ≤ α * (s ^ 2 - (s - t) ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg hα ht) (sub_nonneg.2 hts)]
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 hE.le, mul_le_mul_of_nonneg_left h2 hE.le]

/-- On the annulus `ρ ≤ ‖x - y‖ ≤ r`, the Gaussian barrier `exp (-α ‖x - y‖²) - exp (-α r²)` is a
subsolution, `c v ≤ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼv + ∂_w v`, once `α ≥ 1` is large compared with the trace of `A`,
the drift and the zeroth-order coefficient. -/
private theorem mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub
    {A : Matrix ι ι ℝ} {lam T β γ c α ρ r : ℝ} {y x w : EuclideanSpace ℝ ι}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (htr : A.trace ≤ T)
    (hw : ‖w‖ ≤ β) (hc : 0 ≤ c) (hcγ : c ≤ γ) (hρ : 0 ≤ ρ) (hρx : ρ ≤ ‖x - y‖)
    (hxr : ‖x - y‖ ≤ r) (hα : 1 ≤ α) (hlam : 0 ≤ lam)
    (hαρ : max T 0 + β * r + γ ≤ α * lam * ρ ^ 2) :
    c * (Real.exp (-α * ‖x - y‖ ^ 2) - Real.exp (-α * r ^ 2)) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦
          Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * r ^ 2)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * r ^ 2)) x w := by
  have hfd : fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * r ^ 2)) =
      fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) :=
    funext fun _ ↦ fderiv_sub_const _
  rw [hfd, sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq]
  have hβ : 0 ≤ β := (norm_nonneg w).trans hw
  have hγ : 0 ≤ γ := hc.trans hcγ
  have hr : 0 ≤ r := (norm_nonneg _).trans hxr
  have hE := Real.exp_pos (-α * ‖x - y‖ ^ 2)
  have hEr := Real.exp_pos (-α * r ^ 2)
  -- The bracket is at least `γ`: the quadratic form dominates the trace and the drift.
  have hQ : lam * ρ ^ 2 ≤ (A.toQuadraticForm' (x - y) : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρx 2) hlam).trans (hA (x - y))
  have hinner : ⟪x - y, w⟫ ≤ r * β :=
    (real_inner_le_norm _ _).trans (mul_le_mul hxr hw (norm_nonneg _) hr)
  have hT : T ≤ max T 0 := le_max_left T 0
  have hT0 : 0 ≤ max T 0 := le_max_right T 0
  have hbracket : γ ≤ 4 * α ^ 2 * A.toQuadraticForm' (x - y) - 2 * α * A.trace -
      2 * α * ⟪x - y, w⟫ := by
    nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * α ^ 2),
      mul_le_mul_of_nonneg_left hαρ (by positivity : (0 : ℝ) ≤ 4 * α),
      mul_le_mul_of_nonneg_left (htr.trans hT) (by positivity : (0 : ℝ) ≤ 2 * α),
      mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ 2 * α),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * α - 1) hγ, mul_nonneg hβ hr]
  -- The zeroth-order term is at most `γ exp (-α ‖x - y‖²)`.
  have hlhs : c * (Real.exp (-α * ‖x - y‖ ^ 2) - Real.exp (-α * r ^ 2)) ≤
      γ * Real.exp (-α * ‖x - y‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hcγ hE.le, mul_nonneg hc hEr.le]
  nlinarith [mul_le_mul_of_nonneg_left hbracket hE.le]

/-- The closed ball of radius `R / 2` internally tangent to `ball y R` at `y + R • e` meets the
complement of `ball y R` only at the point of tangency. -/
private theorem eq_or_mem_ball_of_mem_closedBall_add_half_smul {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {y e x : F} {R : ℝ} (he : ‖e‖ = 1)
    (hx : x ∈ closedBall (y + (R / 2) • e) (R / 2)) :
    x = y + R • e ∨ x ∈ ball y R := by
  rw [mem_closedBall, dist_eq_norm] at hx
  have hR : 0 ≤ R / 2 := (norm_nonneg _).trans hx
  set d := x - (y + (R / 2) • e)
  have hw : ‖(R / 2) • e‖ = R / 2 := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hR]
  -- The parallelogram law: `‖x - y‖² + ‖x - x₀‖² = 2 ‖d‖² + 2 (R / 2)² ≤ R²`.
  have hpar := parallelogram_law_with_norm ℝ d ((R / 2) • e)
  have h1 : d + (R / 2) • e = x - y := by simp only [d]; module
  have h2 : d - (R / 2) • e = x - (y + R • e) := by simp only [d]; module
  rw [h1, h2, hw] at hpar
  by_cases hx₀ : x = y + R • e
  · exact Or.inl hx₀
  · right
    have hpos : 0 < ‖x - (y + R • e)‖ := norm_pos_iff.2 (sub_ne_zero.2 hx₀)
    have hlt : ‖x - y‖ ^ 2 < R ^ 2 := by
      nlinarith [mul_le_mul hx hx (norm_nonneg d) hR, mul_pos hpos hpos]
    rw [mem_ball, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) hlt

/-- **Hopf's lemma on a closed ball, in the case `c ≥ 0`, `u x₀ ≥ 0`.** Here `u` is continuous on
the closed ball, strictly below `u x₀` inside and weakly below it on the sphere. On the annulus
`R / 2 ≤ ‖x - y‖ ≤ R`, the weak maximum principle bounds `u + δ₀ v` by `u x₀`, where `v` is the
Gaussian barrier and `δ₀` is the margin of `u` below `u x₀` on the inner sphere. -/
private theorem exists_mul_le_sub_of_lt_ball_of_le_sphere_of_nonneg [Nonempty ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam T β γ : ℝ}
    (hR : 0 < R) (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ T) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hucont : ContinuousOn u (closedBall y R))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) (hle : ∀ x ∈ sphere y R, u x ≤ u (y + R • e))
    (hnonneg : 0 ≤ u (y + R • e)) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hb y (mem_ball_self hR))
  have hγ : 0 ≤ γ := (hc y (mem_ball_self hR)).trans (hcγ y (mem_ball_self hR))
  set x₀ := y + R • e with hx₀
  -- The inner sphere of radius `ρ = R / 2` lies in the ball, so `u` stays a margin `δ₀` below
  -- `u x₀` there.
  set ρ := R / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere y ρ).exists_isMaxOn
    ⟨y + ρ • e, by rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_of_nonneg hρ0.le]⟩
    (hucont.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))))
  have hzB : z ∈ ball y R := by
    rw [mem_sphere_iff_norm] at hz
    rw [mem_ball, dist_eq_norm]
    linarith
  set δ₀ := u x₀ - u z with hδ₀def
  have hδ₀ : 0 < δ₀ := sub_pos.2 (hlt z hzB)
  have hmargin : ∀ x ∈ sphere y ρ, u x ≤ u x₀ - δ₀ := fun x hx ↦ by
    linarith [isMaxOn_iff.1 hzmax x hx]
  -- The barrier `v`, with an exponent `α` large enough for the annulus `ρ ≤ ‖x - y‖ ≤ R`.
  set α := 1 + (max T 0 + β * R + γ) / (lam * ρ ^ 2) with hα
  have hlamρ : 0 < lam * ρ ^ 2 := by positivity
  have hα1 : 1 ≤ α := le_add_of_nonneg_right (by positivity)
  have hαρ : max T 0 + β * R + γ ≤ α * lam * ρ ^ 2 := by
    have : α * lam * ρ ^ 2 = lam * ρ ^ 2 + (max T 0 + β * R + γ) := by
      rw [hα]
      field_simp
    linarith
  set v : EuclideanSpace ℝ ι → ℝ := fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2) - Real.exp (-α * R ^ 2)
    with hv
  have hvcd : ContDiff ℝ 2 v := by
    have hq : ContDiff ℝ 2 fun z : EuclideanSpace ℝ ι ↦ ‖z - y‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact (Real.contDiff_exp.comp (contDiff_const.mul hq)).sub contDiff_const
  set K := closedBall y R \ ball y ρ with hK
  have hKc : IsCompact K := (isCompact_closedBall y R).diff isOpen_ball
  have hKint : ∀ x ∈ interior K, x ∈ ball y R ∧ ρ ≤ ‖x - y‖ := fun x hx ↦ by
    have hx' : x ∈ ball y R := by
      rw [← interior_closedBall y hR.ne']
      exact interior_mono sdiff_subset hx
    have hxK := interior_subset hx
    rw [hK, Set.mem_sdiff, mem_ball, dist_eq_norm, not_lt] at hxK
    exact ⟨hx', hxK.2⟩
  -- The weak maximum principle bounds `u + δ₀ v` by `u x₀` on the annulus `K`.
  have hfmax : ∀ x ∈ K, (u + δ₀ • v) x ≤ u x₀ := by
    refine fun x hx ↦ le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hKc hlam
      (fun x hx ↦ ha x (hKint x hx).1) (fun x hx ↦ hb x (hKint x hx).1)
      (fun x hx ↦ hc x (hKint x hx).1) hnonneg
      ((hucont.mono sdiff_subset).add (hvcd.continuous.continuousOn.const_smul δ₀))
      (fun x hx ↦ (hu x (hKint x hx).1).add (hvcd.contDiffAt.const_smul δ₀)) ?_ ?_ hx
    · intro x hx
      obtain ⟨hxB, hρx⟩ := hKint x hx
      have hxR : ‖x - y‖ ≤ R := by
        rw [mem_ball, dist_eq_norm] at hxB
        exact hxB.le
      rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hu x hxB) hvcd.contDiffAt]
      have hbar := mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub
        (ha x hxB) (htr x hxB) (hb x hxB) (hc x hxB) (hcγ x hxB) hρ0.le hρx hxR hα1 hlam.le hαρ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hsub x hxB, mul_le_mul_of_nonneg_left hbar hδ₀.le]
    · intro x hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hK, sdiff_eq] at hx
      rcases frontier_inter_subset _ _ hx with ⟨hx1, -⟩ | ⟨-, hx2⟩
      · -- On the outer sphere the barrier vanishes, and `u ≤ u x₀`.
        have hxs := frontier_closedBall_subset_sphere hx1
        have hv0 : v x = 0 := by
          rw [hv]
          simp only [mem_sphere_iff_norm.1 hxs, sub_self]
        rw [hv0, mul_zero, add_zero]
        exact hle x hxs
      · -- On the inner sphere `u ≤ u x₀ - δ₀` and the barrier is at most `1`.
        rw [frontier_compl] at hx2
        have hxs := frontier_ball_subset_sphere hx2
        have hv1 : v x ≤ 1 := by
          have h1 : Real.exp (-α * ‖x - y‖ ^ 2) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x - y‖])
          have := Real.exp_pos (-α * R ^ 2)
          simp only [hv]
          linarith
        nlinarith [hmargin x hxs, mul_le_mul_of_nonneg_left hv1 hδ₀.le]
  -- Along the inward radius, the barrier grows linearly.
  refine ⟨δ₀ * (α * R * Real.exp (-α * R ^ 2)), by positivity, ρ, hρ0, fun t ht ↦ ?_⟩
  have hnorm : ‖(x₀ - t • e) - y‖ = R - t := by
    have : (x₀ - t • e) - y = (R - t) • e := by rw [hx₀, sub_smul]; abel
    rw [this, norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith [ht.2])]
  have hpK : x₀ - t • e ∈ K := by
    rw [hK, Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, hnorm, not_lt]
    constructor <;> linarith [ht.1, ht.2]
  have h := hfmax _ hpK
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, hnorm] at h
  have hgrow := mul_exp_le_exp_neg_mul_sub_sq_sub (by linarith : (0 : ℝ) ≤ α) ht.1.le
    (by linarith [ht.2] : t ≤ R)
  nlinarith [mul_le_mul_of_nonneg_left hgrow hδ₀.le]

/-- **Hopf's lemma in the case `c ≥ 0`, `u x₀ ≥ 0`.** The ball of radius `R / 2` internally
tangent to `ball y R` at `x₀` has closure inside `ball y R ∪ {x₀}`, so `u` is continuous on it
and the closed-ball case applies. -/
private theorem exists_mul_le_sub_of_lt_ball_of_nonneg
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam T β γ : ℝ}
    (hR : 0 < R) (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ T) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hcont : ContinuousWithinAt u (ball y R) (y + R • e))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) (hnonneg : 0 ≤ u (y + R • e)) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  -- A unit vector exists, so `ι` is nonempty, as the weak maximum principle requires.
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Subsingleton.elim e 0] at he
  set x₀ := y + R • e with hx₀
  set r := R / 2 with hr
  set y' := y + r • e with hy'
  have hr0 : 0 < r := by positivity
  have hx₀' : x₀ = y' + r • e := by
    rw [hx₀, hy', add_assoc, ← add_smul, hr, add_halves]
  have hball : ball y' r ⊆ ball y R := fun x hx ↦ by
    rw [mem_ball, dist_eq_norm] at hx ⊢
    calc ‖x - y‖ = ‖(x - y') + r • e‖ := by rw [hy']; congr 1; abel
      _ ≤ ‖x - y'‖ + ‖r • e‖ := norm_add_le _ _
      _ < r + r := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hr0.le]; linarith
      _ = R := add_halves R
  have htangent : ∀ x ∈ closedBall y' r, x = x₀ ∨ x ∈ ball y R := fun x hx ↦
    eq_or_mem_ball_of_mem_closedBall_add_half_smul he hx
  have hucont : ContinuousOn u (closedBall y' r) := by
    have hsub' : closedBall y' r ⊆ insert x₀ (ball y R) := fun z hz ↦ htangent z hz
    intro x hx
    rcases htangent x hx with hxx₀ | hxB
    · rw [hxx₀]
      exact (continuousWithinAt_insert_self.2 hcont).mono hsub'
    · exact (hu x hxB).continuousAt.continuousWithinAt
  have hle : ∀ x ∈ sphere y' r, u x ≤ u x₀ := fun x hx ↦ by
    rcases htangent x (sphere_subset_closedBall hx) with hxx₀ | hxB
    · rw [hxx₀]
    · exact (hlt x hxB).le
  have hrt (t : ℝ) : y' + r • e - t • e = x₀ - t • e := by rw [hx₀']
  have h := exists_mul_le_sub_of_lt_ball_of_le_sphere_of_nonneg (e := e) hr0 he hlam
    (fun x hx ↦ ha x (hball hx)) (fun x hx ↦ htr x (hball hx)) (fun x hx ↦ hb x (hball hx))
    (fun x hx ↦ hc x (hball hx)) (fun x hx ↦ hcγ x (hball hx)) (fun x hx ↦ hu x (hball hx))
    (fun x hx ↦ hsub x (hball hx)) hucont (fun x hx ↦ hx₀' ▸ hlt x (hball hx))
    (fun x hx ↦ hx₀' ▸ hle x hx) (hx₀' ▸ hnonneg)
  simpa only [← hx₀', hrt] using h

/-- **Hopf's lemma in the case `u x₀ = 0`.** Since `u < 0` on the ball, `max c 0` is a
nonnegative zeroth-order coefficient for which `u` is still a subsolution. -/
private theorem exists_mul_le_sub_of_lt_ball_of_eq_zero
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam T β γ : ℝ}
    (hR : 0 < R) (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ T) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, |c x| ≤ γ) (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hcont : ContinuousWithinAt u (ball y R) (y + R • e))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e)) (hzero : u (y + R • e) = 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  refine exists_mul_le_sub_of_lt_ball_of_nonneg (c := fun x ↦ max (c x) 0) hR he hlam ha htr hb
    (fun x _ ↦ le_max_right _ _) (fun x hx ↦ max_le ((le_abs_self _).trans (hc x hx))
      ((abs_nonneg _).trans (hc x hx))) hu (fun x hx ↦ ?_) hcont hlt hzero.ge
  have hux : u x ≤ 0 := hzero ▸ (hlt x hx).le
  nlinarith [hsub x hx, mul_le_mul_of_nonpos_right (le_max_left (c x) 0) hux]

/-- **Hopf's boundary-point lemma for elliptic operators in non-divergence form.** Let
`x₀ = y + R • e` with `‖e‖ = 1` be a point of the sphere `∂B` of `B = ball y R`. On `B` let
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ` with `0 < λ`, `tr a(x) ≤ T`, `‖b‖ ≤ β` and `|c| ≤ γ`. Let `u` be `C²` on `B`,
a subsolution `c u ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` there, continuous at `x₀` relative to `B`, and
`u x < u x₀` for every `x ∈ B`. Suppose that `c = 0` on `B`, or that `c ≥ 0` on `B` and
`u x₀ ≥ 0`, or that `u x₀ = 0`. Then `u` decreases at least linearly along the inward radius:
there are `ε, δ > 0` with `ε t ≤ u x₀ - u (x₀ - t • e)` for `0 < t < δ`. -/
theorem exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam T β γ : ℝ}
    (hR : 0 < R) (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ T) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, |c x| ≤ γ) (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hcont : ContinuousWithinAt u (ball y R) (y + R • e))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e))
    (hsign : (∀ x ∈ ball y R, c x = 0) ∨ ((∀ x ∈ ball y R, 0 ≤ c x) ∧ 0 ≤ u (y + R • e)) ∨
      u (y + R • e) = 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (y + R • e) - u (y + R • e - t • e) := by
  rcases hsign with hc0 | ⟨hc0, hnonneg⟩ | hzero
  · -- For `c = 0`, subtract the constant `u x₀`, which changes neither side of the equation.
    set k := u (y + R • e)
    have hfd : fderiv ℝ (fun x ↦ u x - k) = fderiv ℝ u := funext fun _ ↦ fderiv_sub_const _
    obtain ⟨ε, hε, δ, hδ, h⟩ := exists_mul_le_sub_of_lt_ball_of_eq_zero (u := fun x ↦ u x - k)
      hR he hlam ha htr hb hc (fun x hx ↦ (hu x hx).sub contDiffAt_const) (fun x hx ↦ by
        simpa only [hfd, hc0 x hx, zero_mul] using hsub x hx)
      (hcont.sub continuousWithinAt_const) (fun x hx ↦ sub_lt_sub_right (hlt x hx) k)
      (sub_self k)
    exact ⟨ε, hε, δ, hδ, fun t ht ↦ by simpa using h t ht⟩
  · exact exists_mul_le_sub_of_lt_ball_of_nonneg hR he hlam ha htr hb hc0
      (fun x hx ↦ (le_abs_self _).trans (hc x hx)) hu hsub hcont hlt hnonneg
  · exact exists_mul_le_sub_of_lt_ball_of_eq_zero hR he hlam ha htr hb hc hu hsub hcont hlt hzero

/-- **Hopf's boundary-point lemma, derivative form.** Under the hypotheses of
`TauCeti.PDE.exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball`, if `u` is
moreover differentiable at `x₀ = y + R • e`, then its derivative at `x₀` in the outward normal
direction `e` is positive. -/
theorem fderiv_pos_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c u : EuclideanSpace ℝ ι → ℝ} {y e : EuclideanSpace ℝ ι} {R lam T β γ : ℝ}
    (hR : 0 < R) (he : ‖e‖ = 1) (hlam : 0 < lam)
    (ha : ∀ x ∈ ball y R, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (htr : ∀ x ∈ ball y R, (a x).trace ≤ T) (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hc : ∀ x ∈ ball y R, |c x| ≤ γ) (hu : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x))
    (hderiv : DifferentiableAt ℝ u (y + R • e))
    (hlt : ∀ x ∈ ball y R, u x < u (y + R • e))
    (hsign : (∀ x ∈ ball y R, c x = 0) ∨ ((∀ x ∈ ball y R, 0 ≤ c x) ∧ 0 ≤ u (y + R • e)) ∨
      u (y + R • e) = 0) :
    0 < fderiv ℝ u (y + R • e) e := by
  obtain ⟨ε, hε, δ, hδ, h⟩ :=
    exists_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_of_lt_ball hR he hlam ha htr hb
      hc hu hsub hderiv.continuousAt.continuousWithinAt hlt hsign
  set x₀ := y + R • e
  -- The slope of `t ↦ u (x₀ - t • e)` at `0⁺` is `-∂ₑu(x₀)` and is at most `-ε`.
  have hline : HasDerivAt (fun t : ℝ ↦ x₀ - t • e) (-e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub x₀
  have h1 : HasDerivAt (fun t : ℝ ↦ u (x₀ - t • e)) (-(fderiv ℝ u x₀ e)) 0 := by
    have h := hderiv.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline (by simp)
    rwa [map_neg] at h
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ * (u (x₀ - t • e) - u x₀)) (𝓝[>] 0)
      (𝓝 (-(fderiv ℝ u x₀ e))) := by
    simpa only [zero_add, zero_smul, sub_zero, smul_eq_mul] using h1.tendsto_slope_zero_right
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * (u (x₀ - t • e) - u x₀) ≤ -ε := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith [h t ht]
  linarith [le_of_tendsto hslope hle]

end PDE

end TauCeti
