/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Realizing positive-definite real forms on inner product spaces

Every positive-definite real quadratic form on a finite-dimensional real vector space `W` is
isometric to the standard sum of squares
(`TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef`). Combining that diagonalization
with an orthonormal basis of any finite-dimensional real inner product space `E` of the same
dimension produces a linear equivalence `e : W ≃ₗ[ℝ] E` transporting the quadratic form to the
squared norm (`QuadraticMap.PosDef.exists_linearEquiv_norm_sq_eq`) and, by polarization, any
symmetric positive-definite bilinear form to the inner product of `E`
(`LinearMap.BilinForm.exists_linearEquiv_inner_eq`).

## Main results

* `QuadraticMap.PosDef.exists_linearEquiv_norm_sq_eq`: a positive-definite quadratic form on `W`
  is pulled back from `‖·‖ ^ 2` along a linear equivalence `W ≃ₗ[ℝ] E` whenever `W` and `E` are
  finite-dimensional of equal dimension.
* `LinearMap.BilinForm.exists_linearEquiv_inner_eq`: a symmetric bilinear form on `W` whose
  quadratic map is positive definite is pulled back from `inner ℝ` along a linear equivalence
  `W ≃ₗ[ℝ] E` whenever `W` and `E` are finite-dimensional of equal dimension.

## References

* S. Axler, *Linear Algebra Done Right*, 4th ed., Springer (2024), Chapter 6 (orthonormal bases
  and Gram--Schmidt).
-/

public section

open Module

/-- **Euclidean realization of a positive-definite real quadratic form.** If `Q` is a
positive-definite quadratic form on a finite-dimensional real vector space `W` and `E` is a
finite-dimensional real inner product space of the same dimension, there exists a linear
equivalence `e : W ≃ₗ[ℝ] E` such that `‖e x‖ ^ 2 = Q x` for every `x`. -/
theorem QuadraticMap.PosDef.exists_linearEquiv_norm_sq_eq
    {W E : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : QuadraticForm ℝ W} (hQ : Q.PosDef) (hdim : finrank ℝ W = finrank ℝ E) :
    ∃ e : W ≃ₗ[ℝ] E, ∀ x, ‖e x‖ ^ 2 = Q x := by
  obtain ⟨f⟩ := TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef hQ
  let b : OrthonormalBasis (Fin (finrank ℝ W)) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hdim.symm)
  let u : (Fin (finrank ℝ W) → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W)) :=
    (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ W) → ℝ)).symm
  refine ⟨f.toLinearEquiv.trans (u.trans b.repr.symm.toLinearEquiv), fun x ↦ ?_⟩
  simp only [LinearEquiv.trans_apply, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, u,
    PiLp.norm_sq_eq_of_L2, WithLp.coe_symm_linearEquiv, Real.norm_eq_abs, sq_abs]
  simpa only [Matrix.toQuadraticForm'_apply, Matrix.one_mulVec, dotProduct, ← pow_two] using
    f.map_app x

/-- **Euclidean realization of a positive-definite symmetric real bilinear form.** If `B` is a
symmetric bilinear form with positive-definite quadratic map on a finite-dimensional real vector
space `W` and `E` is a finite-dimensional real inner product space of the same dimension, there
exists a linear equivalence `e : W ≃ₗ[ℝ] E` such that `inner ℝ (e x) (e y) = B x y` for all
`x, y : W`. -/
theorem LinearMap.BilinForm.exists_linearEquiv_inner_eq
    {W E : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ W) (hB : B.toQuadraticMap.PosDef) (hsymm : B.IsSymm)
    (hdim : finrank ℝ W = finrank ℝ E) :
    ∃ e : W ≃ₗ[ℝ] E, ∀ x y, inner ℝ (e x) (e y) = B x y := by
  obtain ⟨e, he⟩ := hB.exists_linearEquiv_norm_sq_eq hdim
  refine ⟨e, fun x y ↦ ?_⟩
  have hdiag (z : W) : ‖e z‖ ^ 2 = B z z := he z
  have hnorm : ‖e (x + y)‖ ^ 2 = ‖e x‖ ^ 2 + 2 * inner ℝ (e x) (e y) + ‖e y‖ ^ 2 := by
    rw [map_add, norm_add_sq_real]
  have hbilin : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    simp only [map_add, LinearMap.add_apply, hsymm.eq y x]
    ring
  linarith [hdiag (x + y), hdiag x, hdiag y]
