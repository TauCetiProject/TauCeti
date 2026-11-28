/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Linarith

/-!
# Star-convex affine charts for positive cones of complex Hermitian forms

Let `H : Matrix n n ℂ` be a Hermitian matrix and `u : n → ℂ` a vector with
`0 < (star u ⬝ᵥ H *ᵥ u).re`. Splitting `n → ℂ` along the line through `star u` and the kernel of
`y ↦ y ⬝ᵥ H *ᵥ u` produces a continuous linear equivalence
`e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ)` such that
`(star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u` and `e.symm (1, 0) = star u`.
In these affine coordinates, the slice `{b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re}`
is star-convex at `0`, because the cross terms vanish along `t ↦ e.symm (1, t • b)`.

## Main results

* `Matrix.IsHermitian.exists_starConvex_ballChart`: existence of the linear coordinate equivalence
  `e` whose positive affine slice is star-convex at `0`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Uniformisation/BallModel.lean` (`exists_ball_chart`), dropping the auxiliary scalar
parameter and `Complex.partialOrder` in favor of `0 < (star u ⬝ᵥ H *ᵥ u).re`.
-/

public section

namespace Matrix

/-- For a complex Hermitian matrix `H` and a vector `u` with `0 < (star u ⬝ᵥ H *ᵥ u).re`, there is
a continuous linear equivalence `e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ)` with
`(star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u` and `e.symm (1, 0) = star u` such that the positive
affine slice `{b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re}` is star-convex at `0`. -/
theorem IsHermitian.exists_starConvex_ballChart {n : Type*} [Fintype n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {u : n → ℂ} (hu : 0 < (star u ⬝ᵥ H *ᵥ u).re) :
    ∃ e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ),
      StarConvex ℝ (0 : Fin (Fintype.card n - 1) → ℂ)
        {b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re} ∧
      (∀ y : n → ℂ, (star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u) ∧
      e.symm (1, 0) = star u := by
  classical
  set a : ℂ := star u ⬝ᵥ H *ᵥ u with ha
  have ha_ne : a ≠ 0 := fun h ↦ by simp [h] at hu
  obtain ⟨e, he, he₀⟩ : ∃ e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ),
      (∀ y : n → ℂ, a * (e y).fst = y ⬝ᵥ H *ᵥ u) ∧ e.symm (1, 0) = star u := by
    let φ : (n → ℂ) →L[ℂ] ℂ :=
      ({ toFun := fun y ↦ a⁻¹ * (y ⬝ᵥ H *ᵥ u)
         map_add' := fun y₁ y₂ ↦ by simp [add_dotProduct, mul_add]
         map_smul' := fun c y ↦ by simp [smul_dotProduct]; ring } :
        (n → ℂ) →ₗ[ℂ] ℂ).toContinuousLinearMap
    have h_rightInv : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℂ (star u)) φ :=
      fun c ↦ by
        change a⁻¹ * ((c • star u) ⬝ᵥ H *ᵥ u) = c
        rw [smul_dotProduct, smul_eq_mul, ← ha, mul_left_comm, inv_mul_cancel₀ ha_ne, mul_one]
    let j : (n → ℂ) ≃L[ℂ] ℂ × φ.ker :=
      ContinuousLinearEquiv.equivOfRightInverse φ (.toSpanSingleton ℂ (star u)) h_rightInv
    have h_rank : Module.finrank ℂ φ.ker = Module.finrank ℂ (Fin (Fintype.card n - 1) → ℂ) := by
      have := congrArg (fun k : ℕ ↦ k - 1) j.finrank_eq.symm
      simpa -dsimp using this
    let kEquiv : (ℂ × φ.ker) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ) :=
      (LinearEquiv.prodCongr (.refl ℂ ℂ)
        (LinearEquiv.ofFinrankEq _ _ h_rank)).toContinuousLinearEquiv
    exact ⟨j.trans kEquiv, fun y ↦ by
      change a * (a⁻¹ * (y ⬝ᵥ H *ᵥ u)) = y ⬝ᵥ H *ᵥ u
      exact mul_inv_cancel_left₀ ha_ne _,
      by simp [j, kEquiv]⟩
  refine ⟨e, fun b hb s t hs ht hst ↦ ?_, he, he₀⟩
  set x : n → ℂ := e.symm (1, b) with hx
  have hpoint : e.symm (1, (t : ℂ) • b) = star u + t • (x - star u) :=
    e.injective (by simp [hx, ← he₀, ← Complex.coe_smul])
  have hxu : x ⬝ᵥ H *ᵥ u = a := by simp [hx, ← he]
  have hux : star u ⬝ᵥ H *ᵥ star x = star a := by
    have hcomm : star (x ⬝ᵥ H *ᵥ u) = star u ⬝ᵥ H *ᵥ star x := by
      rw [star_dotProduct, star_mulVec, hH.eq, dotProduct_mulVec, star_star]
    rw [← hcomm, hxu]
  have hconv : 0 < a.re + t ^ 2 * ((x ⬝ᵥ H *ᵥ star x).re - a.re) :=
    (convex_Ioi 0).add_smul_sub_mem hu hb ⟨sq_nonneg t, by bound⟩
  change 0 < (e.symm (1, s • 0 + t • b) ⬝ᵥ H *ᵥ star (e.symm (1, s • 0 + t • b))).re
  simp only [smul_zero, zero_add, ← Complex.coe_smul]
  simp [hpoint, ← ha, hxu, hux, ← Complex.coe_smul, mulVec_add, mulVec_smul, mulVec_sub]
  linarith

end Matrix
