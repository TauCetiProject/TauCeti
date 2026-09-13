/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Coordinates
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin

/-!
# The Jacobian of Cholesky reconstruction

Cholesky reconstruction sends a lower-triangular matrix `L` to the symmetric matrix `L * Lᵀ`.
Both sides are determined by their on-or-below-diagonal entries, so in the coordinates of
`TauCeti.lowerTriangle` the reconstruction becomes a quadratic self-map
`TauCeti.choleskyReconstructionCoordinates` of a Euclidean space. This file computes its
derivative and the determinant `2 ^ p * ∏ i, (L i i) ^ (p - i)` of that derivative.

This determinant is the Jacobian factor of the change of variables `S = L * Lᵀ`, which runs from
the positive-diagonal lower-triangular matrices to the positive-definite cone carrying Lebesgue
measure in symmetric coordinates. Substituting it into an integral over the cone — the
multivariate Gamma integral, and through it the Wishart normalizing constant — turns that integral
into a product of independent one-dimensional integrals.

The determinant is computed by ordering the lower-triangular positions by column and then by row.
In that order the derivative is triangular, and its diagonal entry at position `(i, j)` is `L j j`,
doubled when `i = j`.

## Main declarations

* `TauCeti.choleskyReconstructionCoordinates` — reconstruction read in triangular coordinates.
* `TauCeti.fderivCholeskyReconstructionCoordinates` — its derivative, `H ↦ L * Hᵀ + H * Lᵀ`.
* `TauCeti.abs_det_fderiv_choleskyReconstructionCoordinates` — the Jacobian factor.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Theorem 2.1.9.
* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 2, "Cholesky
  decomposition".
* Declaration skeleton: `TauCetiRoadmap/StandardDistributions/Suggested.lean`, section "Cholesky
  coordinates", which supplies `choleskyReconstructionCoordinates` and the statement of the
  Jacobian theorem (there called `abs_det_fderiv_choleskyReconstruction`).
-/

public section

noncomputable section

open Finset
open scoped Matrix

namespace TauCeti

variable (p : ℕ)

/-- Cholesky reconstruction `L ↦ L * Lᵀ` read in lower-triangular coordinates on both sides: the
input lists the on-or-below-diagonal entries of `L`, and the output lists those of `L * Lᵀ`, which
determine that symmetric matrix. -/
def choleskyReconstructionCoordinates (x : lowerTriangle p → ℝ) : lowerTriangle p → ℝ :=
  fun ij ↦ (lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ) ij.1.1 ij.1.2

/-- The derivative of `TauCeti.choleskyReconstructionCoordinates` at `x`: writing `L` for the
lower-triangular matrix of `x`, it sends the lower-triangular matrix `H` of an increment to the
on-or-below-diagonal entries of `L * Hᵀ + H * Lᵀ`. -/
def fderivCholeskyReconstructionCoordinates (x : lowerTriangle p → ℝ) :
    (lowerTriangle p → ℝ) →L[ℝ] (lowerTriangle p → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h ij ↦
        (lowerTriangleMatrix p x * (lowerTriangleMatrix p h)ᵀ +
          lowerTriangleMatrix p h * (lowerTriangleMatrix p x)ᵀ) ij.1.1 ij.1.2
      map_add' := fun h₁ h₂ ↦ by
        ext ij
        simp only [map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
          Pi.add_apply]
        ring
      map_smul' := fun c h ↦ by
        ext ij
        simp [map_smul, Matrix.transpose_smul, mul_add] }

variable {p}

@[simp]
theorem choleskyReconstructionCoordinates_apply (x : lowerTriangle p → ℝ)
    (ij : lowerTriangle p) :
    choleskyReconstructionCoordinates p x ij =
      ∑ k, lowerTriangleMatrix p x ij.1.1 k * lowerTriangleMatrix p x ij.1.2 k :=
  Matrix.mul_apply.trans (by simp [Matrix.transpose_apply])

/-- On the coordinates of a positive-diagonal lower-triangular matrix, the coordinate form of
Cholesky reconstruction reads off `TauCeti.choleskyReconstruction`. -/
theorem choleskyReconstructionCoordinates_lowerTriangleCoordinatesHomeomorph
    (L : PosDiagLowerTriangular p) (ij : lowerTriangle p) :
    choleskyReconstructionCoordinates p (lowerTriangleCoordinatesHomeomorph p L).1 ij =
      ((choleskyReconstruction L).1 : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 := by
  rw [choleskyReconstructionCoordinates, lowerTriangleMatrix_lowerTriangleCoordinatesHomeomorph,
    choleskyReconstruction_coe]

@[simp]
theorem fderivCholeskyReconstructionCoordinates_apply (x h : lowerTriangle p → ℝ)
    (ij : lowerTriangle p) :
    fderivCholeskyReconstructionCoordinates p x h ij =
      (lowerTriangleMatrix p x * (lowerTriangleMatrix p h)ᵀ +
        lowerTriangleMatrix p h * (lowerTriangleMatrix p x)ᵀ) ij.1.1 ij.1.2 :=
  (rfl)

/-- The coordinate functional reading off the `(i, j)` entry of the lower-triangular matrix of a
coordinate vector. -/
private def lowerTriangleEntryL (i j : Fin p) : (lowerTriangle p → ℝ) →L[ℝ] ℝ :=
  if h : j ≤ i then ContinuousLinearMap.proj ⟨(i, j), h⟩ else 0

private theorem lowerTriangleEntryL_apply (i j : Fin p) (x : lowerTriangle p → ℝ) :
    lowerTriangleEntryL i j x = lowerTriangleMatrix p x i j := by
  rw [lowerTriangleEntryL]
  by_cases h : j ≤ i
  · simp [h]
  · simp [h, lowerTriangleMatrix_apply_of_lt x (not_le.1 h)]

private theorem hasFDerivAt_lowerTriangleMatrix_apply (i j : Fin p) (x : lowerTriangle p → ℝ) :
    HasFDerivAt (fun y : lowerTriangle p → ℝ ↦ lowerTriangleMatrix p y i j)
      (lowerTriangleEntryL i j) x := by
  have h : (fun y : lowerTriangle p → ℝ ↦ lowerTriangleMatrix p y i j) = lowerTriangleEntryL i j :=
    funext fun y ↦ (lowerTriangleEntryL_apply i j y).symm
  rw [h]
  exact (lowerTriangleEntryL i j).hasFDerivAt

/-- Cholesky reconstruction is quadratic in the triangular coordinates, hence differentiable, with
the derivative computed entrywise from the product rule. -/
theorem hasFDerivAt_choleskyReconstructionCoordinates (x : lowerTriangle p → ℝ) :
    HasFDerivAt (choleskyReconstructionCoordinates p)
      (fderivCholeskyReconstructionCoordinates p x) x := by
  rw [hasFDerivAt_pi']
  intro ij
  have hsum : HasFDerivAt
      (fun y : lowerTriangle p → ℝ ↦
        ∑ k, lowerTriangleMatrix p y ij.1.1 k * lowerTriangleMatrix p y ij.1.2 k)
      (∑ k, (lowerTriangleMatrix p x ij.1.1 k • lowerTriangleEntryL ij.1.2 k +
        lowerTriangleMatrix p x ij.1.2 k • lowerTriangleEntryL ij.1.1 k)) x :=
    HasFDerivAt.fun_sum fun k _ ↦
      (hasFDerivAt_lowerTriangleMatrix_apply ij.1.1 k x).fun_mul
        (hasFDerivAt_lowerTriangleMatrix_apply ij.1.2 k x)
  have hfun : (fun y : lowerTriangle p → ℝ ↦ choleskyReconstructionCoordinates p y ij) =
      fun y ↦ ∑ k, lowerTriangleMatrix p y ij.1.1 k * lowerTriangleMatrix p y ij.1.2 k :=
    funext fun y ↦ choleskyReconstructionCoordinates_apply y ij
  have hderiv : (ContinuousLinearMap.proj (R := ℝ) ij).comp
      (fderivCholeskyReconstructionCoordinates p x) =
      ∑ k, (lowerTriangleMatrix p x ij.1.1 k • lowerTriangleEntryL ij.1.2 k +
        lowerTriangleMatrix p x ij.1.2 k • lowerTriangleEntryL ij.1.1 k) := by
    ext h
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      fderivCholeskyReconstructionCoordinates_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply, _root_.sum_apply, add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, lowerTriangleEntryL_apply, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _)
  rw [hfun, hderiv]
  exact hsum

@[fun_prop]
theorem differentiable_choleskyReconstructionCoordinates :
    Differentiable ℝ (choleskyReconstructionCoordinates p) :=
  fun x ↦ (hasFDerivAt_choleskyReconstructionCoordinates x).differentiableAt

@[simp]
theorem fderiv_choleskyReconstructionCoordinates (x : lowerTriangle p → ℝ) :
    fderiv ℝ (choleskyReconstructionCoordinates p) x =
      fderivCholeskyReconstructionCoordinates p x :=
  (hasFDerivAt_choleskyReconstructionCoordinates x).fderiv

/-! ### The determinant of the derivative -/

/-- The lower-triangular positions ordered by column and then by row: the order that makes the
derivative of Cholesky reconstruction triangular. -/
private def lowerTriangleKey (ij : lowerTriangle p) : Fin p ×ₗ Fin p := toLex (ij.1.2, ij.1.1)

private theorem lowerTriangleKey_injective :
    Function.Injective (lowerTriangleKey (p := p)) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  simp only [lowerTriangleKey, toLex_inj, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.2 h.1)

/-- A matrix vanishing above the diagonal in the column-then-row order has the product of its
diagonal entries as determinant. -/
private theorem det_eq_prod_diag_of_lowerTriangleKey
    {M : Matrix (lowerTriangle p) (lowerTriangle p) ℝ}
    (hM : ∀ ij kl, lowerTriangleKey ij < lowerTriangleKey kl → M ij kl = 0) :
    M.det = ∏ ij, M ij ij := by
  let _ : LinearOrder (lowerTriangle p) :=
    LinearOrder.lift' lowerTriangleKey lowerTriangleKey_injective
  exact Matrix.det_of_isLowerTriangular _ fun _ _ h ↦ hM _ _ h

private theorem lowerTriangleMatrix_pi_single (kl : lowerTriangle p) :
    lowerTriangleMatrix p (Pi.single kl 1) = Matrix.single kl.1.1 kl.1.2 1 := by
  refine Matrix.ext fun a b ↦ ?_
  by_cases h : b ≤ a
  · rw [lowerTriangleMatrix_apply_of_le _ h, Pi.single_apply, Matrix.single_apply]
    refine if_congr ?_ rfl rfl
    rw [Subtype.ext_iff]
    exact ⟨fun hc ↦ ⟨(Prod.ext_iff.1 hc).1.symm, (Prod.ext_iff.1 hc).2.symm⟩,
      fun hc ↦ Prod.ext hc.1.symm hc.2.symm⟩
  · rw [lowerTriangleMatrix_apply_of_lt _ (not_le.1 h), Matrix.single_apply, ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact h kl.2

/-- The matrix of the derivative in the standard basis of the coordinate space. -/
private theorem toMatrix_fderivCholeskyReconstructionCoordinates (x : lowerTriangle p → ℝ)
    (ij kl : lowerTriangle p) :
    LinearMap.toMatrix (Pi.basisFun ℝ (lowerTriangle p)) (Pi.basisFun ℝ (lowerTriangle p))
        (fderivCholeskyReconstructionCoordinates p x) ij kl =
      (if kl.1.1 = ij.1.2 then lowerTriangleMatrix p x ij.1.1 kl.1.2 else 0) +
        (if kl.1.1 = ij.1.1 then lowerTriangleMatrix p x ij.1.2 kl.1.2 else 0) := by
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply, ContinuousLinearMap.coe_coe,
    fderivCholeskyReconstructionCoordinates_apply, lowerTriangleMatrix_pi_single]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply,
    mul_ite, mul_one, mul_zero, ite_and]
  by_cases h1 : kl.1.1 = ij.1.2 <;> by_cases h2 : kl.1.1 = ij.1.1 <;>
    simp [h1, h2, Finset.sum_ite_eq]

private theorem toMatrix_fderiv_eq_zero_of_lowerTriangleKey_lt (x : lowerTriangle p → ℝ)
    (ij kl : lowerTriangle p) (h : lowerTriangleKey ij < lowerTriangleKey kl) :
    LinearMap.toMatrix (Pi.basisFun ℝ (lowerTriangle p)) (Pi.basisFun ℝ (lowerTriangle p))
      (fderivCholeskyReconstructionCoordinates p x) ij kl = 0 := by
  rw [toMatrix_fderivCholeskyReconstructionCoordinates]
  rw [lowerTriangleKey, lowerTriangleKey, Prod.Lex.toLex_lt_toLex] at h
  rcases h with hcol | ⟨hcol, hrow⟩
  · -- The column of `kl` is strictly to the right, so the first indicator cannot fire, and the
    -- surviving entry of the second one lies strictly above the diagonal.
    have h1 : kl.1.1 ≠ ij.1.2 := fun hk ↦ absurd hcol (not_lt.2 (by rw [← hk]; exact kl.2))
    rw [ite_eq_right h1]
    by_cases h2 : kl.1.1 = ij.1.1
    · rw [ite_eq_left h2, lowerTriangleMatrix_apply_of_lt _ hcol, add_zero]
    · rw [ite_eq_right h2, add_zero]
  · -- Equal columns with a strictly larger row: neither indicator fires.
    have h1 : kl.1.1 ≠ ij.1.2 := fun hk ↦ by
      have hle : kl.1.1 ≤ ij.1.1 := by rw [hk]; exact ij.2
      exact absurd hrow (not_lt.2 hle)
    have h2 : kl.1.1 ≠ ij.1.1 := fun hk ↦ by rw [hk] at hrow; exact lt_irrefl _ hrow
    rw [ite_eq_right h1, ite_eq_right h2, add_zero]

private theorem toMatrix_fderiv_diag (x : lowerTriangle p → ℝ) (ij : lowerTriangle p) :
    LinearMap.toMatrix (Pi.basisFun ℝ (lowerTriangle p)) (Pi.basisFun ℝ (lowerTriangle p))
        (fderivCholeskyReconstructionCoordinates p x) ij ij =
      (if ij.1.1 = ij.1.2 then (2 : ℝ) else 1) * lowerTriangleMatrix p x ij.1.2 ij.1.2 := by
  rw [toMatrix_fderivCholeskyReconstructionCoordinates, ite_eq_left rfl]
  by_cases h : ij.1.1 = ij.1.2
  · rw [ite_eq_left h, ite_eq_left h, h]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    ring

/-- The contribution of one column to the diagonal product. -/
private theorem prod_column_toMatrix_fderiv_diag (x : lowerTriangle p → ℝ) (j : Fin p) :
    ∏ i : Fin p, (if j ≤ i then
        (if i = j then (2 : ℝ) else 1) * lowerTriangleMatrix p x j j else 1) =
      lowerTriangleMatrix p x j j ^ (p - j.1) * 2 := by
  have step : ∀ i : Fin p, (if j ≤ i then
      (if i = j then (2 : ℝ) else 1) * lowerTriangleMatrix p x j j else 1) =
      (if j ≤ i then lowerTriangleMatrix p x j j else 1) * (if i = j then (2 : ℝ) else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · by_cases hle : j ≤ i <;> simp [hij, hle]
  rw [Finset.prod_congr rfl fun i _ ↦ step i, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' univ j fun _ ↦ (2 : ℝ), ite_eq_left (Finset.mem_univ j),
    ← Finset.prod_filter, Finset.prod_const, Finset.filter_le_eq_Ici, Fin.card_Ici]

/-- **The Jacobian determinant of Cholesky reconstruction.** In lower-triangular coordinates the
derivative of `L ↦ L * Lᵀ` has determinant `2 ^ p * ∏ i, (L i i) ^ (p - i)`. -/
theorem det_fderiv_choleskyReconstructionCoordinates (x : lowerTriangle p → ℝ) :
    (fderiv ℝ (choleskyReconstructionCoordinates p) x).det =
      2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1) := by
  -- Read the determinant off the matrix of the derivative in the standard basis; that matrix is
  -- triangular for the column-then-row order, so only its diagonal survives.
  rw [fderiv_choleskyReconstructionCoordinates, ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ (lowerTriangle p)),
    det_eq_prod_diag_of_lowerTriangleKey (toMatrix_fderiv_eq_zero_of_lowerTriangleKey_lt x),
    Finset.prod_congr rfl fun ij (_ : ij ∈ univ) ↦ toMatrix_fderiv_diag x ij]
  -- Regroup the diagonal product over the lower-triangular positions by column.
  rw [← Finset.prod_subtype ({ij : Fin p × Fin p | ij.2 ≤ ij.1} : Finset _) (fun _ ↦ by simp)
      (fun ij : Fin p × Fin p ↦
        (if ij.1 = ij.2 then (2 : ℝ) else 1) * lowerTriangleMatrix p x ij.2 ij.2),
    Finset.prod_filter, Fintype.prod_prod_type_right]
  -- Each column contributes a power of its diagonal entry and one factor of `2`.
  rw [Finset.prod_congr rfl fun j (_ : j ∈ univ) ↦ prod_column_toMatrix_fderiv_diag x j,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [mul_comm]

/-- **The absolute Jacobian factor of Cholesky reconstruction.** On the positive-diagonal region,
which is where the Cholesky factors live, the determinant above is positive and is therefore the
density appearing in the change-of-variables formula. -/
theorem abs_det_fderiv_choleskyReconstructionCoordinates (x : lowerTriangle p → ℝ)
    (hx : ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩) :
    |(fderiv ℝ (choleskyReconstructionCoordinates p) x).det| =
      2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1) := by
  rw [det_fderiv_choleskyReconstructionCoordinates, abs_of_pos]
  exact mul_pos (by positivity) (Finset.prod_pos fun i _ ↦ pow_pos (hx i) _)

end TauCeti
