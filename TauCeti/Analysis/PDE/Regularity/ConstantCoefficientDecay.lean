/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import TauCeti.Analysis.Matrix.EuclideanLin
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.Order
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Decay estimates for elliptic equations with constant coefficients

Let `A` be a constant `n × n` coefficient matrix whose quadratic form satisfies
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` with `0 < λ`, and let `u` be a `C²` solution of

`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0`

on a ball `B_R = ball x₀ R ⊆ ℝⁿ`, with values in a Banach space. This file proves the two decay
estimates on concentric balls `B_ρ ⊆ B_R` that harmonic functions satisfy
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sq_le` and
`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`), now with constants
depending only on `n` and the ellipticity ratio `Λ / λ`:

`∫_{B_ρ} ‖u‖² ≤ C (ρ / R)ⁿ ∫_{B_R} ‖u‖²`,

`∫_{B_ρ} ‖u - u_ρ‖² ≤ C (ρ / R)^(n + 2) ∫_{B_R} ‖u - c‖²`

for every constant `c`, where `u_ρ` is the average of `u` over `B_ρ`.

These are the decay estimates of the frozen problem in the Campanato approach to Schauder
estimates for equations with variable coefficients: on each ball the coefficients are frozen at
the centre, and the solution is compared with a solution of the resulting constant-coefficient
equation. The Laplacian, the case `A = 1`, is not enough there, since the frozen coefficient
matrix is an arbitrary elliptic matrix.

## The argument

Only the symmetric part `S` of `A` enters the operator, because the second derivative of `u` is
symmetric. Let `T = √S`, the positive square root of the positive definite matrix `S`. By the
chain rule `Δ (u ∘ T) = (∑ᵢⱼ (T Tᵀ)ᵢⱼ ∂ᵢ∂ⱼu) ∘ T`
(`TauCeti.PDE.laplacian_comp_toEuclideanCLE_apply`), and `T Tᵀ = S`, so `u` solves the equation
exactly when `u ∘ T` is harmonic (`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`
and `TauCeti.PDE.harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero`). Since
`‖T y‖² = yᵀ A y`, the map `T` stretches lengths by at most `√Λ` and its inverse by at most
`1 / √λ`, and the decay estimates for harmonic functions after a linear change of variables
(`TauCeti.setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp`) give the result with the bound
`√(Λ / λ)` on the condition number of `T` in the constant.

## Main declarations

* `TauCeti.PDE.laplacian_comp_toEuclideanCLE_apply`: the Laplacian of `u ∘ T` is the
  constant-coefficient operator with matrix `T Tᵀ` applied to `u`.
* `TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`: an elliptic constant-coefficient
  operator is the Laplacian after a linear change of variables with controlled condition number.
* `TauCeti.PDE.harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero`: after such a change of
  variables, a `C²` solution on an open set becomes a harmonic function.
* `TauCeti.PDE.setIntegral_ball_norm_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`: decay of the `L²`
  mass with exponent `n`.
* `TauCeti.PDE.setIntegral_ball_norm_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`:
  decay of the `L²` mean oscillation with exponent `n + 2`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Chapter 5 (decay estimates for constant coefficients and
  Schauder estimates by Campanato's method).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
-/

public section

open InnerProductSpace Laplacian Matrix MeasureTheory Metric Set Filter
open scoped Topology RealInnerProductSpace MatrixOrder

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The Laplacian after a linear change of variables by a matrix.** For a square matrix `T`
with nonzero determinant, `Δ (u ∘ T) y = ∑ᵢⱼ (T Tᵀ)ᵢⱼ ∂ᵢ∂ⱼu (T y)`: composing with `T` turns the
Laplacian into the constant-coefficient operator with coefficient matrix `T Tᵀ`. No
differentiability hypothesis is needed. -/
theorem laplacian_comp_toEuclideanCLE_apply (T : Matrix ι ι ℝ) (hT : T.det ≠ 0)
    (u : EuclideanSpace ℝ ι → F) (y : EuclideanSpace ℝ ι) :
    Δ (u ∘ T.toEuclideanCLE hT) y = ∑ i, ∑ j, (T * Tᵀ) i j •
      fderiv ℝ (fderiv ℝ u) (T.toEuclideanCLE hT y) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  set e := T.toEuclideanCLE hT
  set b := EuclideanSpace.basisFun ι ℝ
  have hcol : ∀ k, e (b k) = ∑ i, T i k • b i := fun k => by
    ext i
    simp [e, b, Pi.single_apply]
  -- Expand `e bₖ = ∑ᵢ Tᵢₖ bᵢ` in both slots of the second derivative and resum over `k`.
  rw [laplacian_comp_continuousLinearEquiv_right_apply e b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hcol, map_sum,
    map_smul, _root_.sum_apply, _root_.smul_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  simp only [b, EuclideanSpace.basisFun_apply]
  set H := fderiv ℝ (fderiv ℝ u) (e y)
  calc _ = ∑ k, ∑ c, ∑ a, (T a k * T c k) •
        H (EuclideanSpace.single c 1) (EuclideanSpace.single a 1) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ c, ∑ k, ∑ a, (T a k * T c k) •
        H (EuclideanSpace.single c 1) (EuclideanSpace.single a 1) := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ k, (T a k * T c k) •
        H (EuclideanSpace.single c 1) (EuclideanSpace.single a 1) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun k _ => by rw [mul_comm]

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

variable [CompleteSpace F] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {lam Lam : ℝ}
  {u : EuclideanSpace ℝ ι → F} {x₀ : EuclideanSpace ℝ ι} {ρ R : ℝ}

/-- **Decay of the `L²` mass for constant coefficients.** Let `A` be a square matrix with
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u` be a `C²` solution of
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` on the ball `ball x₀ R ⊆ ℝⁿ`, with `‖u‖²` integrable there. Then for every
`0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u‖² ≤ 2ⁿ (Λ / λ)^(n / 2) (ρ / R)ⁿ ∫_{ball x₀ R} ‖u‖²`.

The constant depends only on `n` and the ellipticity ratio `Λ / λ`. -/
theorem setIntegral_ball_norm_sq_le_of_sum_smul_fderiv_fderiv_eq_zero (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hu : ContDiffOn ℝ 2 u (ball x₀ R))
    (hLu : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0)
    (hint : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ ≤
      2 ^ Fintype.card ι * √(Lam / lam) ^ Fintype.card ι * (ρ / R) ^ Fintype.card ι *
        ∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ := by
  obtain ⟨e, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := F) hlam hA hA'
  have h := setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp e hae hbe
    (harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hu hLu) hint hρ hρR
  rwa [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at h

/-- **Decay of the `L²` mean oscillation for constant coefficients.** Let `A` be a square matrix
with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u` be a `C²` solution of
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` on the ball `ball x₀ R ⊆ ℝⁿ`, with `‖u - c‖²` integrable there for some
constant `c`. Then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u - u_ρ‖² ≤ C (Λ / λ)^((n + 2) / 2) (ρ / R)^(n + 2) ∫_{ball x₀ R} ‖u - c‖²`
with `C = 2^(3n + 10) (n + 1)²`,

where `u_ρ` is the average of `u` over `ball x₀ ρ`. The constant depends only on `n` and the
ellipticity ratio `Λ / λ`. This is the decay estimate of the frozen problem in the Campanato
approach to Schauder estimates for equations with variable coefficients. -/
theorem setIntegral_ball_norm_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hu : ContDiffOn ℝ 2 u (ball x₀ R))
    (hLu : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0)
    {c : F} (hint : IntegrableOn (fun x ↦ ‖u x - c‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ)
    (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ ≤
      2 ^ (3 * Fintype.card ι + 10) * (Fintype.card ι + 1) ^ 2 *
        √(Lam / lam) ^ (Fintype.card ι + 2) * (ρ / R) ^ (Fintype.card ι + 2) *
          ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ := by
  obtain ⟨e, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := F) hlam hA hA'
  have h := setIntegral_ball_norm_sub_setAverage_sq_le_of_harmonicOnNhd_comp e hae hbe
    (harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hu hLu) hint hρ hρR
  rwa [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at h

end PDE

end TauCeti
