/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.InnerProductSpace.Laplacian.GradientEstimate

/-!
# Exponential decay of all derivatives of exterior solutions of `Δu = G(u)`

Let `L` be a smooth function on a finite-dimensional real inner product space which, outside a
ball of radius `R`, solves the semilinear equation `Δ L = G(L)` for a smooth `G` with `G(0) = 0`,
and which decays exponentially there: `|L(z)| ≤ K exp(-c ‖z‖)` with `c ≥ 0`. Then every derivative
of `L` decays at the same rate: for each `n` there is `K'` with

`‖Dⁱ L(z)‖ ≤ K' exp(-c ‖z‖)`  for `i ≤ n` and `‖z‖ > R + n`

(`TauCeti.exists_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_comp`). No lower bound on `G'(0)`
and no maximum principle at infinity is used: the decay rate is inherited from `L` itself.

The proof gains one derivative at a time. Suppose the derivatives of `L` of order at most `n` are
bounded by `K₀ exp(-c ‖z‖)` outside the ball of radius `R + n`. Since `G(0) = 0`, the Faà di Bruno
bound gives the same decay for `Dⁿ (G ∘ L)` (`ContDiff.exists_norm_iteratedFDeriv_comp_le_mul`),
and `Dⁿ (G ∘ L) = Dⁿ (Δ L)` there. So `Dⁿ L` and `Dⁿ (Δ L)` are bounded by a multiple of
`exp(-c ‖z‖)` on the unit ball around `z`, and the interior gradient estimate, applied to the
components `y ↦ Dⁿ L(y) m` whose Laplacians are `Dⁿ (Δ L)(y) m`
(`TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`), bounds `Dⁿ⁺¹ L(z)` by
the same multiple.

This is the bootstrap that turns the exponential decay of a solution of a vortex-type equation into
exponential decay of all its derivatives.

## Main results

* `TauCeti.exists_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_comp`: exponential decay of all
  derivatives of an exterior solution of `Δ L = G(L)` that decays exponentially.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 3.9.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Metric Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On the unit ball around `z`, the weight `exp(-c ‖y‖)` is at most `exp c` times its value at
`z`. -/
private theorem exp_neg_mul_norm_le_of_mem_closedBall {c : ℝ} (hc : 0 ≤ c) {y z : E}
    (hy : y ∈ closedBall z 1) :
    Real.exp (-(c * ‖y‖)) ≤ Real.exp c * Real.exp (-(c * ‖z‖)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h₁ : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
  have h₂ : ‖z - y‖ ≤ 1 := by rw [← dist_eq_norm, dist_comm]; exact hy
  nlinarith

/-- **Exponential decay of all derivatives of exterior solutions of `Δ L = G(L)`.** Let `L` be a
smooth function which, outside the ball of radius `R`, solves `Δ L = G(L)` for a smooth `G` with
`G(0) = 0` and satisfies `|L(z)| ≤ K exp(-c ‖z‖)` with `c ≥ 0`. Then for every `n` there is
`K' ≥ 0` with `‖Dⁱ L(z)‖ ≤ K' exp(-c ‖z‖)` for all `i ≤ n` whenever `‖z‖ > R + n`. -/
theorem exists_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_comp {L : E → ℝ} {G : ℝ → ℝ}
    (hL : ContDiff ℝ ∞ L) (hG : ContDiff ℝ ∞ G) (hG₀ : G 0 = 0) {R c K : ℝ} (hc : 0 ≤ c)
    (heq : ∀ z, R < ‖z‖ → Δ L z = G (L z))
    (hdecay : ∀ z, R < ‖z‖ → |L z| ≤ K * Real.exp (-(c * ‖z‖))) (n : ℕ) :
    ∃ K', 0 ≤ K' ∧ ∀ z, R + n < ‖z‖ → ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i L z‖ ≤ K' * Real.exp (-(c * ‖z‖)) := by
  have hw₁ : ∀ y : E, Real.exp (-(c * ‖y‖)) ≤ 1 := fun y ↦
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc (norm_nonneg y)))
  induction n with
  | zero =>
    refine ⟨max K 0, le_max_right _ _, fun z hz i hi ↦ ?_⟩
    obtain rfl := Nat.le_zero.mp hi
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact (hdecay z (by simpa using hz)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  | succ n ih =>
    obtain ⟨K₀, hK₀, hP⟩ := ih
    have hGn : ContDiff ℝ (n + 1) G := hG.of_le (by simp)
    obtain ⟨K₁, hK₁⟩ := hGn.exists_norm_iteratedFDeriv_comp_le_mul (E := E) hG₀ K₀
    set K₂ := max K₁ 0
    -- The `n`-th derivative of `Δ L = G ∘ L` decays outside the ball of radius `R + n`.
    have hΔ : ∀ y, R + n < ‖y‖ → ‖iteratedFDeriv ℝ n (Δ L) y‖ ≤ K₂ * Real.exp (-(c * ‖y‖)) := by
      intro y hy
      have hRy : R < ‖y‖ := lt_of_le_of_lt (by simp) hy
      have hev : Δ L =ᶠ[𝓝 y] G ∘ L := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hRy] with w hw
        exact heq w hw
      rw [(hev.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
      exact (hK₁ L y _ (hL.contDiffAt.of_le (by simp)) (Real.exp_pos _).le (hw₁ y)
        fun i hi ↦ hP y hy i hi).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    set d : ℝ := (Module.finrank ℝ E : ℝ)
    set K₃ := d * (K₀ * Real.exp c) + K₂ * Real.exp c / 2
    have hK₃ : 0 ≤ K₃ := by positivity
    refine ⟨max K₀ K₃, le_max_of_le_left hK₀, fun z hz i hi ↦ ?_⟩
    have hz' : R + n < ‖z‖ := lt_trans (by push_cast; linarith) hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hi | rfl
    · exact (hP z hz' i (Nat.lt_succ_iff.mp hi)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    -- On the unit ball around `z`, `Dⁿ L` and `Dⁿ (Δ L)` are bounded by multiples of
    -- `exp(-c ‖z‖)`, so the interior estimate bounds `Dⁿ⁺¹ L(z)`.
    have hfar : ∀ y ∈ closedBall z 1, R + n < ‖y‖ := by
      intro y hy
      have h₁ : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
      have h₂ : ‖z - y‖ ≤ 1 := by rw [← dist_eq_norm, dist_comm]; exact hy
      push_cast at hz
      linarith
    have hM : ∀ y ∈ closedBall z 1,
        ‖iteratedFDeriv ℝ n L y‖ ≤ K₀ * Real.exp c * Real.exp (-(c * ‖z‖)) := fun y hy ↦
      (hP y (hfar y hy) n le_rfl).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (exp_neg_mul_norm_le_of_mem_closedBall hc hy) hK₀)
    have hF : ∀ y ∈ ball z 1,
        ‖iteratedFDeriv ℝ n (Δ L) y‖ ≤ K₂ * Real.exp c * Real.exp (-(c * ‖z‖)) := fun y hy ↦
      (hΔ y (hfar y (ball_subset_closedBall hy))).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (exp_neg_mul_norm_le_of_mem_closedBall hc (ball_subset_closedBall hy))
          (le_max_right _ _))
    refine (norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le hL (by simp)
      one_pos hM hF).trans (le_of_eq ?_)
    ring

end TauCeti
