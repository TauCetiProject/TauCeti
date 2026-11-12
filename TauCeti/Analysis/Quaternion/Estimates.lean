/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Kernel
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous

/-!
# Derivative bounds for the Cauchy–Fueter kernel

The kernel is homogeneous of degree `-3`. Compactness of the unit sphere therefore
bounds its `m`-th real derivative by `C / ‖q - q₀‖^(3 + m)`, with a constant independent
of the pole. The same bound holds when differentiating the pole rather than the
spatial variable; the derivatives differ by the chain-rule sign `(-1)^m`.

A uniform positive separation between a boundary piece and a set of poles gives a
common bound for all these parameter derivatives. This is the dominator needed to
differentiate Cauchy–Fueter boundary integrals and estimate their derivatives.

The compact-sphere argument is supplied by
`TauCeti.exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq`.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9 (the integral formula).
-/

public section

open scoped Quaternion

namespace TauCeti

/-- Spatial derivatives of a kernel with arbitrary pole are translates of those
of the kernel with pole zero. This identity also holds at the totalized pole. -/
theorem iteratedFDeriv_cauchyFueterKernel (m : ℕ) (q q₀ : ℍ) :
    iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x q₀) q =
      iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x 0) (q - q₀) := by
  have heq : (fun x ↦ cauchyFueterKernel x q₀) =
      (fun x ↦ cauchyFueterKernel (x - q₀) 0) := by
    funext x
    simp [cauchyFueterKernel_eq]
  rw [heq, iteratedFDeriv_comp_sub (f := fun x ↦ cauchyFueterKernel x 0)]

/-- Differentiation in the pole contributes one minus sign per derivative.
No differentiability hypothesis is needed for this identity of totalized derivatives. -/
theorem iteratedFDeriv_cauchyFueterKernel_pole (m : ℕ) (q q₀ : ℍ) :
    iteratedFDeriv ℝ m (cauchyFueterKernel q) q₀ =
      (-1 : ℝ) ^ m • iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x 0) (q - q₀) := by
  have heq : cauchyFueterKernel q =
      (fun x ↦ cauchyFueterKernel (q + (-1 : ℝ) • x) 0) := by
    funext x
    simp [cauchyFueterKernel_eq, sub_eq_add_neg]
  rw [heq, iteratedFDeriv_comp_const_smul_apply
    (fun x ↦ cauchyFueterKernel (q + x) 0),
    iteratedFDeriv_comp_add_left (f := fun x ↦ cauchyFueterKernel x 0)]
  simp [sub_eq_add_neg]

/-- Uniform bounds through any prescribed finite order for spatial derivatives of
the kernel, with a positive constant independent of the pole and evaluation point. -/
theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ q q₀ : ℍ, q ≠ q₀ →
      ‖iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x q₀) q‖ ≤
        C / ‖q - q₀‖ ^ (3 + m) := by
  have hs : ContDiffOn ℝ N (fun x ↦ cauchyFueterKernel x 0) {0}ᶜ :=
    fun x hx ↦ (contDiffAt_cauchyFueterKernel hx).contDiffWithinAt
  have hh (t : ℝ) (_ht : 0 < t) (x : ℍ) (_hx : x ≠ 0) :
      cauchyFueterKernel (t • x) 0 = t ^ (-3 : ℤ) • cauchyFueterKernel x 0 := by
    simpa [zpow_neg, zpow_ofNat] using cauchyFueterKernel_smul t x 0
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq hs hh
  refine ⟨A + 1, by positivity, fun m hm q q₀ hq ↦ ?_⟩
  rw [iteratedFDeriv_cauchyFueterKernel]
  have h := hA m hm (q - q₀) (sub_ne_zero.mpr hq)
  have hexp : (-3 : ℤ) - m = -((3 + m : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at h
  exact h.trans (div_le_div_of_nonneg_right (by simp) (by positivity))

/-- The same pole-independent decay estimate holds for derivatives in the pole,
as used in the differentiated boundary representation. -/
theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_pole_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ q q₀ : ℍ, q ≠ q₀ →
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel q) q₀‖ ≤
        C / ‖q - q₀‖ ^ (3 + m) := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_le N
  refine ⟨C, hC, fun m hm q q₀ hq ↦ ?_⟩
  simpa [iteratedFDeriv_cauchyFueterKernel_pole, norm_smul,
    iteratedFDeriv_cauchyFueterKernel] using h m hm q q₀ hq

/-- A positive separation from the poles gives a uniform bound for parameter
derivatives on an arbitrary boundary piece. No compactness or regularity of the
parametrization is needed once the separation bound is supplied. -/
theorem exists_bound_iteratedFDeriv_cauchyFueterKernel_pole {ι : Type*}
    (N : ℕ) {φ : ι → ℍ} {s : Set ι} {K : Set ℍ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u ∈ s, ∀ q₀ ∈ K, δ ≤ ‖φ u - q₀‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ u ∈ s, ∀ q₀ ∈ K,
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel (φ u)) q₀‖ ≤ C / δ ^ (3 + m) := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_pole_le N
  refine ⟨C, hC, fun m hm u hu q₀ hq₀ ↦ ?_⟩
  have hd := hsep u hu q₀ hq₀
  have hne : φ u ≠ q₀ := by
    intro heq
    simp [heq] at hd
    linarith
  exact (h m hm _ _ hne).trans
    (div_le_div_of_nonneg_left hC.le (by positivity) (pow_le_pow_left₀ hδ.le hd _))

/-- If a boundary piece is at distance at least `δ` from a pole, all its kernel
parameter derivatives through order `N` have a common bound on the closed ball of
radius `δ / 2` about that pole. This supplies a common-neighbourhood dominator,
not merely a pointwise bound at the centre. -/
theorem exists_bound_iteratedFDeriv_cauchyFueterKernel_pole_closedBall {ι : Type*}
    (N : ℕ) {φ : ι → ℍ} {s : Set ι} {q₀ : ℍ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u ∈ s, δ ≤ ‖φ u - q₀‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ u ∈ s, ∀ q ∈ Metric.closedBall q₀ (δ / 2),
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel (φ u)) q‖ ≤ C / (δ / 2) ^ (3 + m) := by
  apply exists_bound_iteratedFDeriv_cauchyFueterKernel_pole N (half_pos hδ)
  intro u hu q hq
  have hdist : ‖q - q₀‖ ≤ δ / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hq
  have htri := dist_triangle (φ u) q q₀
  simp only [dist_eq_norm] at htri
  linarith [hsep u hu]

end TauCeti
