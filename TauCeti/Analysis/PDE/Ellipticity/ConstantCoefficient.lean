/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Analysis.Matrix.EuclideanLin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.Order
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Constant-coefficient elliptic operators as the Laplacian in linear coordinates

Let `A` be a constant `n × n` coefficient matrix whose quadratic form satisfies
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` with `0 < λ`. This file shows that the operator
`u ↦ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is the Laplacian after a linear change of variables whose stretching is
controlled by `λ` and `Λ`, so that `C²` solutions of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` become harmonic
functions in the new coordinates. This reduces questions about constant-coefficient elliptic
equations, such as decay estimates on balls, to the corresponding questions for harmonic
functions.

## The argument

Only the symmetric part `S` of `A` enters the operator, because the second derivative of `u` is
symmetric. Let `T = √S`, the positive square root of the positive definite matrix `S`. By the
chain rule `Δ (u ∘ T) = (∑ᵢⱼ (T Tᵀ)ᵢⱼ ∂ᵢ∂ⱼu) ∘ T`
(`TauCeti.laplacian_comp_toEuclideanCLE_apply`), and `T Tᵀ = S`. Since `‖T y‖² = yᵀ A y`, the
map `T` stretches lengths by at most `√Λ` and its inverse by at most `1 / √λ`.

## Main declarations

* `TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`: an elliptic constant-coefficient
  operator is the Laplacian after a linear change of variables with controlled condition number.
* `TauCeti.PDE.harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero`: after such a change of
  variables, a `C²` solution on an open set becomes a harmonic function.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
-/

public section

open InnerProductSpace Laplacian Matrix
open scoped Topology MatrixOrder

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A constant-coefficient operator is the Laplacian in suitable linear coordinates.** Let `A`
be a square matrix whose quadratic form satisfies `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` with `0 < λ`. Then
there is a continuous linear automorphism `e` of `EuclideanSpace ℝ ι`, with
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ` and `‖e y‖ ≤ √Λ ‖y‖`, such that

`Δ (u ∘ e) y = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu (e y)`

for every `u` twice continuously differentiable near `e y`. So `u` solves `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0`
exactly when `u ∘ e` is harmonic. One can take `e` to be the square root of the symmetric part of
`A`; only the symmetric part matters, since the second derivative of `u` is symmetric. -/
theorem exists_continuousLinearEquiv_laplacian_comp_eq {A : Matrix ι ι ℝ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι,
      (∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) ∧ (∀ y, ‖e y‖ ≤ √Lam * ‖y‖) ∧
      ∀ (u : EuclideanSpace ℝ ι → F) (y : EuclideanSpace ℝ ι), ContDiffAt ℝ 2 u (e y) →
        Δ (u ∘ e) y = ∑ i, ∑ j, A i j •
          fderiv ℝ (fderiv ℝ u) (e y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  set S := coefficientSymmetricPart A
  have hSq : ∀ ξ : EuclideanSpace ℝ ι, S.toQuadraticForm' ξ = A.toQuadraticForm' ξ :=
    toQuadraticForm'_coefficientSymmetricPart A
  have hS : S.PosDef := by
    refine Matrix.PosDef.of_toQuadraticForm' (coefficientSymmetricPart_isSymm A) fun x hx => ?_
    have h := hA (WithLp.toLp 2 x)
    have hx' : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.2 (by simpa using hx)
    have := hSq (WithLp.toLp 2 x)
    rw [this]
    nlinarith [sq_pos_of_pos hx']
  -- `T = √S` is symmetric, invertible, and `Tᵀ T = T Tᵀ = S`.
  set T := CFC.sqrt S
  have hT : T.PosSemidef := Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)
  have hTT : T * T = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hTt : Tᵀ = T := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hT.isHermitian.eq
  have hdet : T.det ≠ 0 := by
    have : T.det = √S.det := by simpa using hS.posSemidef.det_sqrt
    rw [this]
    exact (Real.sqrt_pos.2 hS.det_pos).ne'
  set e := T.toEuclideanCLE hdet
  have hnorm : ∀ y, ‖e y‖ ^ 2 = A.toQuadraticForm' y := fun y => by
    have h := Matrix.inner_toEuclideanLin_toEuclideanLin T 1 y
    rw [Matrix.toEuclideanCLE_apply, ← real_inner_self_eq_norm_sq, ← hSq, ← hTT]
    simpa [Matrix.toQuadraticForm'_apply, EuclideanSpace.inner_eq_star_dotProduct, hTt,
      dotProduct_comm] using h
  refine ⟨e, fun x => ?_, fun y => ?_, fun u y hu => ?_⟩
  · -- `√λ ‖y‖ ≤ ‖e y‖`, applied to `y = e⁻¹ x`.
    have h := hA (e.symm x)
    rw [← hnorm, e.apply_symm_apply] at h
    have hl : √lam * ‖e.symm x‖ ≤ ‖x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (norm_nonneg (e.symm x)),
        ← Real.sqrt_mul hlam.le]
      exact Real.sqrt_le_sqrt h
    rw [inv_mul_eq_div, le_div_iff₀' (Real.sqrt_pos.2 hlam)]
    exact hl
  · rw [← Real.sqrt_sq (norm_nonneg (e y)), hnorm, ← Real.sqrt_sq (norm_nonneg y),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hA' y)
  · -- Only the symmetric part of `A` enters, because the second derivative is symmetric.
    have hsymm := hu.isSymmSndFDerivAt (by simp)
    rw [laplacian_comp_toEuclideanCLE_apply, hTt, hTT]
    simp only [S, coefficientSymmetricPart_apply, div_eq_mul_inv, add_mul, add_smul,
      Finset.sum_add_distrib]
    set H := fderiv ℝ (fderiv ℝ u) (e y)
    rw [Finset.sum_comm (f := fun i j => (A j i * 2⁻¹) • H (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm (EuclideanSpace.single j 1), ← add_smul]
    ring_nf

variable {A : Matrix ι ι ℝ}

/-- **Solutions become harmonic after the change of variables.** If `e` is a continuous linear
automorphism with `Δ (u ∘ e) = (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu) ∘ e` for every `u` that is `C²` at the relevant
point, as provided by `exists_continuousLinearEquiv_laplacian_comp_eq`, then a `C²` solution of
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` on an open set `s` becomes harmonic on `e ⁻¹' s`. -/
theorem harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero
    {e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι}
    (he : ∀ (u : EuclideanSpace ℝ ι → F) (y : EuclideanSpace ℝ ι), ContDiffAt ℝ 2 u (e y) →
      Δ (u ∘ e) y = ∑ i, ∑ j, A i j •
        fderiv ℝ (fderiv ℝ u) (e y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    {s : Set (EuclideanSpace ℝ ι)} (hs : IsOpen s) {u : EuclideanSpace ℝ ι → F}
    (hu : ContDiffOn ℝ 2 u s)
    (hLu : ∀ x ∈ s, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0) :
    HarmonicOnNhd (u ∘ e) (e ⁻¹' s) := by
  intro y hy
  refine ⟨(hu.contDiffAt (hs.mem_nhds hy)).comp y e.contDiff.contDiffAt, ?_⟩
  filter_upwards [(hs.preimage e.continuous).mem_nhds hy] with z hz
  rw [he u z (hu.contDiffAt (hs.mem_nhds hz)), hLu _ hz, Pi.zero_apply]

end PDE

end TauCeti
