/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Star
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

* `Matrix.exists_ballChart`: existence of the linear coordinate equivalence `e` adapted to `u`
  and the linear form `y ↦ y ⬝ᵥ H *ᵥ u`, assuming only `star u ⬝ᵥ H *ᵥ u ≠ 0`.
* `Matrix.IsHermitian.starConvex_ballChart`: the positive affine slice of any such chart is
  star-convex at `0`.
* `Matrix.IsHermitian.exists_starConvex_ballChart`: existence of a chart whose positive affine
  slice is star-convex at `0`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Uniformisation/BallModel.lean` (`exists_ball_chart`), dropping the auxiliary scalar
parameter and `Complex.partialOrder` in favor of `0 < (star u ⬝ᵥ H *ᵥ u).re`.
-/

public section

namespace Matrix

/-- For a matrix `H` and a vector `u` with `star u ⬝ᵥ H *ᵥ u ≠ 0`, there is a continuous linear
equivalence `e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ)` with
`(star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u` and `e.symm (1, 0) = star u`. -/
theorem exists_ballChart {n : Type*} [Fintype n] (H : Matrix n n ℂ) {u : n → ℂ}
    (ha : star u ⬝ᵥ H *ᵥ u ≠ 0) :
    ∃ e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ),
      (∀ y : n → ℂ, (star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u) ∧ e.symm (1, 0) = star u := by
  classical
  set a : ℂ := star u ⬝ᵥ H *ᵥ u with hadef
  let φ : (n → ℂ) →L[ℂ] ℂ :=
    ({ toFun := fun y ↦ a⁻¹ * (y ⬝ᵥ H *ᵥ u)
       map_add' := fun y₁ y₂ ↦ by simp [add_dotProduct, mul_add]
       map_smul' := fun c y ↦ by simp [smul_dotProduct]; ring } :
      (n → ℂ) →ₗ[ℂ] ℂ).toContinuousLinearMap
  have h_rightInv : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℂ (star u)) φ :=
    fun c ↦ by
      simp [φ, ← hadef]
      field_simp
  let j : (n → ℂ) ≃L[ℂ] ℂ × φ.ker :=
    ContinuousLinearEquiv.equivOfRightInverse φ (.toSpanSingleton ℂ (star u)) h_rightInv
  have h_rank : Module.finrank ℂ φ.ker = Module.finrank ℂ (Fin (Fintype.card n - 1) → ℂ) := by
    have := j.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at this ⊢
    omega
  let kEquiv : (ℂ × φ.ker) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ) :=
    (LinearEquiv.prodCongr (.refl ℂ ℂ)
      (LinearEquiv.ofFinrankEq _ _ h_rank)).toContinuousLinearEquiv
  refine ⟨j.trans kEquiv, fun y ↦ ?_, by simp [j, kEquiv]⟩
  -- `kEquiv` is the identity on the first factor, so this is `fst_equivOfRightInverse`.
  have hfst : ((j.trans kEquiv) y).fst = φ y :=
    ContinuousLinearEquiv.fst_equivOfRightInverse φ (.toSpanSingleton ℂ (star u)) h_rightInv y
  rw [hfst]
  simp [φ, ha]

/-- Star-convexity of the positive affine slice in any chart `e` with
`(star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u` and `e.symm (1, 0) = star u`, for a Hermitian
matrix `H` with `0 < (star u ⬝ᵥ H *ᵥ u).re`. -/
theorem IsHermitian.starConvex_ballChart {n : Type*} [Fintype n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {u : n → ℂ} (hu : 0 < (star u ⬝ᵥ H *ᵥ u).re)
    (e : (n → ℂ) ≃L[ℂ] ℂ × (Fin (Fintype.card n - 1) → ℂ))
    (he : ∀ y : n → ℂ, (star u ⬝ᵥ H *ᵥ u) * (e y).fst = y ⬝ᵥ H *ᵥ u)
    (he₀ : e.symm (1, 0) = star u) :
    StarConvex ℝ (0 : Fin (Fintype.card n - 1) → ℂ)
      {b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re} := by
  set a : ℂ := star u ⬝ᵥ H *ᵥ u with ha
  intro b hb s t hs ht hst
  set x : n → ℂ := e.symm (1, b) with hx
  have hpoint : e.symm (1, (t : ℂ) • b) = star u + t • (x - star u) :=
    e.injective (by simp [hx, ← he₀, ← Complex.coe_smul])
  have hxu : x ⬝ᵥ H *ᵥ u = a := by simp [hx, ← he]
  have hux : star u ⬝ᵥ H *ᵥ star x = star a := by
    have hcomm : star (x ⬝ᵥ H *ᵥ u) = star u ⬝ᵥ H *ᵥ star x := by
      simpa using hH.star_dotProduct_mulVec_comm (star x) u
    rw [← hcomm, hxu]
  have hconv : 0 < a.re + t ^ 2 * ((x ⬝ᵥ H *ᵥ star x).re - a.re) :=
    (convex_Ioi 0).add_smul_sub_mem hu hb ⟨sq_nonneg t, by bound⟩
  simp [hpoint, ← ha, hxu, hux, ← Complex.coe_smul, mulVec_add, mulVec_smul, mulVec_sub]
  linarith

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
  obtain ⟨e, he, he₀⟩ := exists_ballChart H (fun h ↦ hu.ne' (by rw [h, Complex.zero_re]))
  exact ⟨e, hH.starConvex_ballChart hu e he he₀, he, he₀⟩

end Matrix
