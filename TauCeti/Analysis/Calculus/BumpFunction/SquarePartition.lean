/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Partitions of unity by squares around separated points

Localization formulas of IMS type split a quadratic form along functions `J₀, J₁, …, J_N` whose
squares, rather than the functions themselves, sum to one: then `∑ₐ Jₐ A Jₐ` differs from `A` only
by the commutator terms `∑ₐ |∇Jₐ|²` for a second-order operator `A`. This file constructs such a
partition adapted to finitely many points `p` of a finite-dimensional real normed space at mutual
distance at least `2 r`: one smooth function `J p` for each point, nonzero only on the ball of
radius `r` around it, and a smooth function `J₀` that vanishes on the balls of radius `ρ < r`
around the points and is constant outside a compact set.

The construction takes smooth bumps `θ p`, equal to one on `closedBall p ρ` and supported in
`ball p r`, and sets `J p = sin (π θ p / 2)` and `J₀ = cos (π ∑ₚ θ p / 2)`. As the balls are
disjoint, at most one `θ p` is nonzero at each point, and `sin² + cos² = 1` gives
`J₀² + ∑ₚ (J p)² = 1`. For a single ball, `TauCeti.exists_contDiff_angle_cutoff` gives the
two-function version `cos² θ + sin² θ = 1` with gradients as small as required.

## Main results

* `TauCeti.exists_sq_add_sum_sq_eq_one`: a smooth partition of unity by squares subordinate to
  balls around finitely many separated points.

## References

* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 3 (the IMS localization formula) and
  Chapter 11 (its partition of unity around the critical points of a Morse function).
-/

public section

open Metric Set
open scoped ContDiff Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A partition of unity by squares around separated points.** Let `P` be a finite set of points
at mutual distance at least `2 r`, and `0 < ρ < r`. There are smooth functions `J₀` and `J p`,
`p ∈ P`, with `J₀² + ∑ₚ (J p)² = 1`, such that `J p` vanishes outside the ball of radius `r`
around `p` and has compact support, and `J₀` vanishes on the closed balls of radius `ρ` around the
points of `P` and has compactly supported derivative. -/
theorem exists_sq_add_sum_sq_eq_one {P : Finset E} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hP : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q) :
    ∃ (J₀ : E → ℝ) (J : E → E → ℝ), ContDiff ℝ ∞ J₀ ∧ (∀ p, ContDiff ℝ ∞ (J p)) ∧
      (∀ x, J₀ x ^ 2 + ∑ p ∈ P, J p x ^ 2 = 1) ∧
      (∀ p x, J p x ≠ 0 → dist x p < r) ∧ (∀ x, J₀ x ≠ 0 → ∀ p ∈ P, ρ < dist x p) ∧
      HasCompactSupport (fderiv ℝ J₀) ∧ ∀ p, HasCompactSupport (J p) := by
  let θ : ∀ p : E, ContDiffBump p := fun p ↦ ⟨ρ, r, hρ, hρr⟩
  -- The bumps have disjoint supports: at most one of them is nonzero at each point.
  have hθ : ∀ x, ∀ p ∈ P, θ p x ≠ 0 → ∀ q ∈ P, q ≠ p → θ q x = 0 := by
    intro x p hp hx q hq hqp
    have hxp : dist x p < r := by
      simpa [θ, ContDiffBump.support_eq] using (Function.mem_support.2 hx)
    refine (θ q).zero_of_le_dist ?_
    have := hP p hp q hq hqp.symm
    have := dist_triangle p x q
    rw [dist_comm p x] at this
    have hr : (θ q).rOut = r := rfl
    rw [hr]
    linarith
  have hsum : ∀ (g : ℝ → ℝ), g 0 = 0 → ∀ x, ∀ p ∈ P, θ p x ≠ 0 →
      ∑ q ∈ P, g (θ q x) = g (θ p x) := fun g hg x p hp hx ↦
    Finset.sum_eq_single_of_mem p hp fun q hq hqp ↦ by rw [hθ x p hp hx q hq hqp, hg]
  have hzero : ∀ (g : ℝ → ℝ), g 0 = 0 → ∀ x, (∀ p ∈ P, θ p x = 0) →
      ∑ q ∈ P, g (θ q x) = 0 := fun g hg x hx ↦
    Finset.sum_eq_zero fun q hq ↦ by rw [hx q hq, hg]
  refine ⟨fun x ↦ Real.cos (π / 2 * ∑ p ∈ P, θ p x), fun p x ↦ Real.sin (π / 2 * θ p x),
    (contDiff_const.mul (ContDiff.sum fun p _ ↦ (θ p).contDiff)).cos,
    fun p ↦ (contDiff_const.mul (θ p).contDiff).sin, fun x ↦ ?_, fun p x hx ↦ ?_,
    fun x hx p hp ↦ ?_, ?_, fun p ↦ ?_⟩
  · beta_reduce
    by_cases h : ∃ p ∈ P, θ p x ≠ 0
    · obtain ⟨p, hp, hx⟩ := h
      rw [hsum (fun u ↦ u) rfl x p hp hx,
        hsum (fun u ↦ Real.sin (π / 2 * u) ^ 2) (by simp) x p hp hx]
      exact Real.cos_sq_add_sin_sq _
    · push Not at h
      rw [hzero (fun u ↦ u) rfl x h, hzero (fun u ↦ Real.sin (π / 2 * u) ^ 2) (by simp) x h]
      simp
  · have hθx : θ p x ≠ 0 := fun h ↦ hx (by simp [h])
    simpa [θ, ContDiffBump.support_eq] using (Function.mem_support.2 hθx)
  · by_contra! hxp
    have h1 : θ p x = 1 := (θ p).one_of_mem_closedBall (mem_closedBall.2 hxp)
    refine hx ?_
    beta_reduce
    rw [hsum (fun u ↦ u) rfl x p hp (by rw [h1]; exact one_ne_zero), h1, mul_one,
      Real.cos_pi_div_two]
  · have hcs : HasCompactSupport fun x ↦ Real.cos (π / 2 * ∑ p ∈ P, θ p x) - 1 := by
      refine HasCompactSupport.intro (P.isCompact_biUnion fun p _ ↦ isCompact_closedBall p r)
        fun x hx ↦ ?_
      simp only [mem_iUnion, mem_closedBall, not_exists, not_le] at hx
      rw [hzero (fun u ↦ u) rfl x fun p hp ↦ (θ p).zero_of_le_dist (hx p hp).le]
      simp
    have hJ₀ : fderiv ℝ (fun x ↦ Real.cos (π / 2 * ∑ p ∈ P, θ p x) - 1) =
        fderiv ℝ fun x ↦ Real.cos (π / 2 * ∑ p ∈ P, θ p x) := funext fun x ↦ fderiv_sub_const 1
    exact hJ₀ ▸ hcs.fderiv (𝕜 := ℝ)
  · exact (θ p).hasCompactSupport.comp_left (g := fun u ↦ Real.sin (π / 2 * u)) (by simp)

end TauCeti
