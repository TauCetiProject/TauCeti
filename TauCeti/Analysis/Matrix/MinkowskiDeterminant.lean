/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.Analysis.MeanInequalities

/-!
# Minkowski's determinant inequality

For positive semidefinite real `n × n` matrices `A` and `B`, with `n ≥ 1`,

`det A ^ (1 / n) + det B ^ (1 / n) ≤ det (A + B) ^ (1 / n)`.

Since `det (c • A) ^ (1 / n) = c * det A ^ (1 / n)` for `c ≥ 0`, this says that
`A ↦ det A ^ (1 / n)` is concave on the convex cone of positive semidefinite matrices. The same
statements hold for positive operators on a finite-dimensional real inner product space of
dimension `n`, by passing to the matrix in an orthonormal basis.

This concavity is the matrix inequality behind the displacement convexity of internal energies in
optimal transport. Along the interpolation `x ↦ (1 - t) • x + t • ∇u x` of the gradient of a convex
function `u`, the Jacobian matrix `(1 - t) • 1 + t • ∇²u x` moves along a segment of positive
semidefinite matrices, so `t ↦ det ((1 - t) • 1 + t • ∇²u x) ^ (1 / n)` is concave on `[0, 1]`;
McCann's condition on an internal energy is exactly what turns this into convexity of the energy.

The proof first treats `A = 1`: with `μ i ≥ 0` the eigenvalues of `B`, the inequality reads
`1 + (∏ i, μ i) ^ (1 / n) ≤ (∏ i, (1 + μ i)) ^ (1 / n)`, the superadditivity of the geometric mean
(`Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`). A positive definite `A` factors as `C * Cᵀ` with
`C` invertible, and congruence by `C⁻¹` reduces the general inequality to that case. If neither
matrix is positive definite then both determinants vanish and there is nothing to prove.

## Main statements

* `Matrix.PosSemidef.det_rpow_add_det_rpow_le`: **Minkowski's determinant inequality**.
* `Matrix.concaveOn_det_rpow`: `A ↦ det A ^ (1 / n)` is concave on the positive semidefinite
  matrices.
* `LinearMap.IsPositive.det_rpow_add_det_rpow_le` and `LinearMap.concaveOn_det_rpow`: the same for
  positive operators on a finite-dimensional real inner product space.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press 2013,
  Section 7.8 (the Minkowski determinant theorem).
* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153--179.
-/

public section

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Minkowski's determinant inequality against the identity matrix:
`1 + det M ^ (1 / n) ≤ det (1 + M) ^ (1 / n)` for positive semidefinite `M`. -/
private theorem PosSemidef.one_add_det_rpow_le [Nonempty n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) :
    1 + M.det ^ (Fintype.card n : ℝ)⁻¹ ≤ (1 + M).det ^ (Fintype.card n : ℝ)⁻¹ := by
  have hμ := hM.eigenvalues_nonneg
  have hw : ∑ _i : n, (Fintype.card n : ℝ)⁻¹ = 1 := by
    simp [Finset.card_univ, Fintype.card_ne_zero]
  have hdet : M.det = ∏ i, hM.isHermitian.eigenvalues i := by
    simpa using hM.isHermitian.det_eq_prod_eigenvalues
  have hdet_one_add : (1 + M).det = ∏ i, (1 + hM.isHermitian.eigenvalues i) := by
    simpa [sub_eq_add_neg] using hM.isHermitian.det_one_sub_smul (-1)
  rw [hdet, hdet_one_add, ← Real.finsetProd_rpow _ _ fun i _ => hμ i,
    ← Real.finsetProd_rpow _ _ fun i _ => add_nonneg zero_le_one (hμ i)]
  simpa using Real.prod_rpow_add_prod_rpow_le_prod_add_rpow Finset.univ
    (w := fun _ => (Fintype.card n : ℝ)⁻¹) (a := fun _ => 1)
    (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)) hw (fun _ _ => zero_le_one) fun i _ => hμ i

/-- **Minkowski's determinant inequality.** For positive semidefinite real `n × n` matrices `A`
and `B` with `n ≥ 1`, `det A ^ (1 / n) + det B ^ (1 / n) ≤ det (A + B) ^ (1 / n)`. -/
theorem PosSemidef.det_rpow_add_det_rpow_le [Nonempty n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det ^ (Fintype.card n : ℝ)⁻¹ + B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      (A + B).det ^ (Fintype.card n : ℝ)⁻¹ := by
  have hr : (Fintype.card n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  -- If one of the two matrices is positive definite we may assume it is `A`; if neither is,
  -- both determinants vanish.
  wlog hA' : A.PosDef generalizing A B
  · by_cases hB' : B.PosDef
    · simpa only [add_comm] using this hB hA hB'
    rw [not_not.1 (mt hA.posDef_iff_det_ne_zero.2 hA'),
      not_not.1 (mt hB.posDef_iff_det_ne_zero.2 hB'), Real.zero_rpow hr, add_zero]
    exact Real.rpow_nonneg (hA.add hB).det_nonneg _
  -- Write `A = C * Cᵀ` and `B = C * M * Cᵀ` with `M = C⁻¹ * B * C⁻ᵀ` positive semidefinite.
  obtain ⟨C, hC⟩ := hA'.exists_generalLinearGroup_mul_transpose_eq
  set D : Matrix n n ℝ := ((C⁻¹ : GL n ℝ) : Matrix n n ℝ)
  set M : Matrix n n ℝ := D * B * Dᵀ
  have hM : M.PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hB.mul_mul_conjTranspose_same D
  have hCD : (C : Matrix n n ℝ) * D = 1 := by simp [D]
  have hBM : B = C * M * (C : Matrix n n ℝ)ᵀ := by
    rw [show (C : Matrix n n ℝ) * M * (C : Matrix n n ℝ)ᵀ =
        (C * D) * B * ((C : Matrix n n ℝ) * D)ᵀ by simp only [M, transpose_mul, mul_assoc]]
    rw [hCD, transpose_one, one_mul, mul_one]
  have hAB : A + B = C * (1 + M) * (C : Matrix n n ℝ)ᵀ := by
    rw [hBM, ← hC, mul_add, add_mul, mul_one]
  -- All three determinants carry the common factor `det A = det C ^ 2 > 0`.
  have hdetA : 0 < A.det := hA'.det_pos
  have hdetB : B.det = A.det * M.det := by
    rw [hBM, ← hC]
    simp only [det_mul]
    ring
  have hdetAB : (A + B).det = A.det * (1 + M).det := by
    rw [hAB, ← hC]
    simp only [det_mul]
    ring
  rw [hdetB, hdetAB, Real.mul_rpow hdetA.le hM.det_nonneg,
    Real.mul_rpow hdetA.le (PosSemidef.one.add hM).det_nonneg, ← mul_one_add]
  exact mul_le_mul_of_nonneg_left hM.one_add_det_rpow_le (Real.rpow_nonneg hdetA.le _)

/-- `A ↦ det A ^ (1 / n)` is concave on the positive semidefinite real `n × n` matrices. -/
theorem concaveOn_det_rpow :
    ConcaveOn ℝ {A : Matrix n n ℝ | A.PosSemidef} fun A => A.det ^ (Fintype.card n : ℝ)⁻¹ := by
  refine ⟨fun A hA B hB a b ha hb _ => (hA.smul ha).add (hB.smul hb), ?_⟩
  intro A hA B hB a b ha hb _
  cases isEmpty_or_nonempty n with
  | inl _ => simp_all
  | inr _ =>
    -- `det (c • A) ^ (1 / n) = c * det A ^ (1 / n)` for `c ≥ 0`.
    have hhom {c : ℝ} (hc : 0 ≤ c) {A : Matrix n n ℝ} (hA : A.PosSemidef) :
        (c • A).det ^ (Fintype.card n : ℝ)⁻¹ = c * A.det ^ (Fintype.card n : ℝ)⁻¹ := by
      rw [det_smul, Real.mul_rpow (pow_nonneg hc _) hA.det_nonneg,
        Real.pow_rpow_inv_natCast hc Fintype.card_ne_zero]
    simpa only [smul_eq_mul, hhom ha hA, hhom hb hB] using
      (hA.smul ha).det_rpow_add_det_rpow_le (hB.smul hb)

end Matrix

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Minkowski's determinant inequality** for positive operators: on a nonzero real inner product
space of finite dimension `n`, `det A ^ (1 / n) + det B ^ (1 / n) ≤ det (A + B) ^ (1 / n)`. -/
theorem IsPositive.det_rpow_add_det_rpow_le [Nontrivial E] {A B : E →ₗ[ℝ] E}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    A.det ^ (Module.finrank ℝ E : ℝ)⁻¹ + B.det ^ (Module.finrank ℝ E : ℝ)⁻¹ ≤
      (A + B).det ^ (Module.finrank ℝ E : ℝ)⁻¹ := by
  let b := stdOrthonormalBasis ℝ E
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have h := ((posSemidef_toMatrix_iff b).2 hA).det_rpow_add_det_rpow_le
    ((posSemidef_toMatrix_iff b).2 hB)
  rwa [← map_add, det_toMatrix, det_toMatrix, det_toMatrix, Fintype.card_fin] at h

/-- On a finite-dimensional real inner product space of dimension `n`, `A ↦ det A ^ (1 / n)` is
concave on the positive operators. -/
theorem concaveOn_det_rpow :
    ConcaveOn ℝ {A : E →ₗ[ℝ] E | A.IsPositive} fun A => A.det ^ (Module.finrank ℝ E : ℝ)⁻¹ := by
  let b := stdOrthonormalBasis ℝ E
  convert (Matrix.concaveOn_det_rpow (n := Fin (Module.finrank ℝ E))).comp_linearMap
    (toMatrix b.toBasis b.toBasis).toLinearMap using 1
  · ext A
    simp
  · ext A
    simp [det_toMatrix]

end LinearMap
