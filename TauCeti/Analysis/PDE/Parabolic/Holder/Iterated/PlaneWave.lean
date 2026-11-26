/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.HeatEquation
import TauCeti.Analysis.Holder.Trigonometric
import TauCeti.Analysis.InnerProductSpace.Laplacian.PlaneWave

/-!
# The heat flow of a plane wave in the parabolic Hölder spaces of every order

For a vector `ξ` of a finite-dimensional real inner product space `E`, the plane wave
`u(x, t) = exp (-t ‖ξ‖²) cos ⟪ξ, x⟫` solves the heat equation `∂ₜu = Δu` with initial datum
`cos ⟪ξ, ·⟫`. This file shows that it lies in the bounded parabolic Hölder space
`C_{par,b}^{k+α}(E × [a, b])` of every order `k`, for `0 ≤ a < b` and `α ≤ 1`, with every mixed
derivative bounded by the corresponding power of the frequency,
`‖D_t^r D_x^m u‖ ≤ ‖ξ‖ ^ (2 r + m)`
(`TauCeti.ParabolicCkHolderSpace.exists_coe_eq_exp_mul_cos_inner`). On the line with `ξ = 1` this
is `u = e^{-t} cos x`, every mixed derivative of which is bounded by `1`
(`TauCeti.ParabolicCkHolderSpace.exists_coe_eq_exp_neg_mul_cos`). On `ℝⁿ` and for `0 < α < 1`,
the plane wave is the solution of order `k + 2` of the Cauchy problem `∂ₜu - Δu = 0`,
`u(·, 0) = cos ⟪ξ, ·⟫`
(`TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE_symm_apply_zero_of_coe_eq_cos_inner`).

So smooth data with bounded derivatives of every order give a solution in every finite-order
space, as the order-`k` theory predicts: the datum lies in `C_b^{k,α}(E)` for every `k`
(`TauCeti.CkHolderSpace.exists_coe_eq_cos_inner`), and the solution of each order is the same
function.

## The argument

The plane wave is the Cauchy heat potential of its datum, since plane waves are eigenfunctions of
the heat flow (`TauCeti.heatCauchyPotential_cos_inner`), and the potential maps `C_b^{k,α}(E)`
into `C_{par,b}^{k+α}` (`TauCeti.ParabolicCkHolderSpace.heatCauchyPotentialL`). Its field
`D_t^r D_x^m u` is the potential of `D^m Δ^r cos ⟪ξ, ·⟫`. Since
`Δ^r cos ⟪ξ, ·⟫ = (-‖ξ‖²)^r cos ⟪ξ, ·⟫` (`TauCeti.iterate_laplacian_cos_inner`) and
`‖D^m cos ⟪ξ, ·⟫‖ ≤ ‖ξ‖ ^ m` (`TauCeti.norm_iteratedFDeriv_cos_inner_le`), the maximum principle
for the potential bounds the field by `‖ξ‖ ^ (2 r + m)`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (parabolic Hölder spaces of higher order).
-/

public section

noncomputable section

namespace TauCeti

open Real Set ParabolicSpaceTime InnerProductSpace Laplacian
open scoped NNReal RealInnerProductSpace

namespace ParabolicCkHolderSpace

section Potential

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ} {ξ : E}

/-- **The heat flow of a cosine plane wave.** For `α ≤ 1` and `0 ≤ a < b`, the Cauchy heat
potential in `C_{par,b}^{k+α}(E × [a, b])` of the datum `cos ⟪ξ, ·⟫ ∈ C_b^{k,α}(E)` is
`exp (-t ‖ξ‖²) cos ⟪ξ, x⟫`. -/
theorem heatCauchyPotentialL_apply_of_coe_eq_cos_inner (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a)
    {g : CkHolderSpace k α E ℝ} (hg : ⇑g = fun x ↦ cos ⟪ξ, x⟫) (p : slab (E := E) a b) :
    heatCauchyPotentialL hα hab ha g p =
      exp (-((p : ParabolicSpaceTime E).time * ‖ξ‖ ^ 2)) *
        cos ⟪ξ, (p : ParabolicSpaceTime E).space⟫ := by
  rw [heatCauchyPotentialL_apply, hg,
    heatCauchyPotential_cos_inner ξ (ha.trans (mem_slab.1 p.property).1)]

/-- **The mixed derivatives of the heat flow of a plane wave.** For `α ≤ 1` and `0 ≤ a < b`, every
field `D_t^r D_x^m u` of the Cauchy heat potential `u` of the datum `cos ⟪ξ, ·⟫ ∈ C_b^{k,α}(E)` is
bounded by `‖ξ‖ ^ (2 r + m)`. -/
theorem norm_mixedDerivL_heatCauchyPotentialL_le_of_coe_eq_cos_inner (hα : α ≤ 1) (hab : a < b)
    (ha : 0 ≤ a) {g : CkHolderSpace k α E ℝ} (hg : ⇑g = fun x ↦ cos ⟪ξ, x⟫) (r m : ℕ)
    (p : slab (E := E) a b) :
    ‖mixedDerivL r m (heatCauchyPotentialL hα hab ha g) p‖ ≤ ‖ξ‖ ^ (2 * r + m) := by
  rcases le_or_gt (2 * r + m) k with h | h
  · rw [mixedDerivL_heatCauchyPotentialL g h, hg, iterate_laplacian_cos_inner]
    refine norm_heatCauchyPotential_le (fun y ↦ ?_) _ _
    -- `D^m Δ^r cos ⟪ξ, ·⟫ = (-‖ξ‖²)^r D^m cos ⟪ξ, ·⟫`, of norm at most `‖ξ‖^(2 r) ‖ξ‖^m`.
    have hsmul : (fun y ↦ (-‖ξ‖ ^ 2) ^ r * cos ⟪ξ, y⟫) =
        (-‖ξ‖ ^ 2) ^ r • fun y ↦ cos ⟪ξ, y⟫ := (rfl)
    have hcd : ContDiff ℝ m fun y : E ↦ cos ⟪ξ, y⟫ :=
      contDiff_cos.comp (contDiff_const.inner ℝ contDiff_id)
    rw [hsmul, iteratedFDeriv_const_smul_apply hcd.contDiffAt, norm_smul, norm_pow, norm_neg,
      norm_pow, norm_norm, pow_add, ← pow_mul]
    gcongr
    exact norm_iteratedFDeriv_cos_inner_le ξ y m
  · rw [mixedDerivL_of_lt h]
    simp

/-- **The plane wave solution of the heat equation lies in every parabolic Hölder space.** For
`α ≤ 1`, `0 ≤ a < b`, every order `k` and every `ξ ∈ E`, the map
`u(x, t) = exp (-t ‖ξ‖²) cos ⟪ξ, x⟫` lies in `C_{par,b}^{k+α}(E × [a, b])`, and each of its
mixed derivatives `D_t^r D_x^m u` is bounded by `‖ξ‖ ^ (2 r + m)`. -/
theorem exists_coe_eq_exp_mul_cos_inner (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a) (ξ : E) :
    ∃ u : ParabolicCkHolderSpace k α E ℝ hab,
      (∀ p, u p = exp (-((p : ParabolicSpaceTime E).time * ‖ξ‖ ^ 2)) *
        cos ⟪ξ, (p : ParabolicSpaceTime E).space⟫) ∧
      ∀ r m p, ‖mixedDerivL r m u p‖ ≤ ‖ξ‖ ^ (2 * r + m) := by
  obtain ⟨g, hg⟩ := CkHolderSpace.exists_coe_eq_cos_inner (k := k) hα ξ
  exact ⟨heatCauchyPotentialL hα hab ha g,
    heatCauchyPotentialL_apply_of_coe_eq_cos_inner hα hab ha hg,
    norm_mixedDerivL_heatCauchyPotentialL_le_of_coe_eq_cos_inner hα hab ha hg⟩

/-- **`e^{-t} cos x` lies in every parabolic Hölder space.** For `α ≤ 1` and `0 ≤ a < b`, the
solution `u(x, t) = e^{-t} cos x` of the heat equation on the line lies in
`C_{par,b}^{k+α}(ℝ × [a, b])` for every order `k`, and every mixed derivative `D_t^r D_x^m u` is
bounded by `1`. -/
theorem exists_coe_eq_exp_neg_mul_cos (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a) :
    ∃ u : ParabolicCkHolderSpace k α ℝ ℝ hab,
      (∀ p, u p = exp (-(p : ParabolicSpaceTime ℝ).time) * cos (p : ParabolicSpaceTime ℝ).space) ∧
      ∀ r m p, ‖mixedDerivL r m u p‖ ≤ 1 := by
  obtain ⟨u, hu, hD⟩ := exists_coe_eq_exp_mul_cos_inner (k := k) hα hab ha (1 : ℝ)
  exact ⟨u, fun p ↦ by simpa using hu p, fun r m p ↦ by simpa using hD r m p⟩

end Potential

/-! ### The Cauchy problem on `ℝⁿ` -/

section Euclidean

variable {k : ℕ} {α T : ℝ≥0} {hT : (0 : ℝ) < T} {ι : Type*} [Fintype ι]

/-- **The plane wave is the solution of the Cauchy problem.** For `0 < α < 1` and every order `k`,
the solution in `C_{par,b}^{(k+2)+α}(ℝⁿ × [0, T])` of the heat equation `∂ₜu - Δu = 0` with initial
datum `cos ⟪ξ, ·⟫ ∈ C_b^{k+2,α}(ℝⁿ)` is `exp (-t ‖ξ‖²) cos ⟪ξ, x⟫`. -/
theorem heatInitialDataCLE_symm_apply_zero_of_coe_eq_cos_inner (hα₀ : 0 < α) (hα₁ : α < 1)
    {ξ : EuclideanSpace ℝ ι} {g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ}
    (hg : ⇑g = fun x ↦ cos ⟪ξ, x⟫) (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    (heatInitialDataCLE (k := k) hα₀ hα₁ hT).symm (0, g) p =
      exp (-((p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time * ‖ξ‖ ^ 2)) *
        cos ⟪ξ, (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).space⟫ := by
  rw [heatInitialDataCLE_symm_apply, heatSolutionL_apply, map_zero, zero_add,
    heatCauchyPotentialL_apply_of_coe_eq_cos_inner hα₁.le hT le_rfl hg]

end Euclidean

end ParabolicCkHolderSpace

end TauCeti
