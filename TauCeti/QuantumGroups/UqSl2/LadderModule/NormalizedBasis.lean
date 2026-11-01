/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic

/-!
# Normalized bases of positive quantum ladder modules

For a positive real parameter different from one, divide each positive ladder vector by
its length in the invariant metric. The resulting basis is orthonormal for `invariantForm`.
We compute the matrices of the generators in this basis, with column-vector conventions.
In the fundamental representation they are
`K = diag(q, q⁻¹)`, `E = [[0, 1/√q], [0, 0]]`, and `F = [[0, 0], [√q, 0]]`.
These formulas fix the normalization of matrix coefficients for the compact real form.
No global norm or inner product instance is installed on the algebraic ladder modules.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Chapter 3,
  for the compact real form and its finite-dimensional representations.
-/

public noncomputable section

namespace TauCeti.UqSl2.LadderModule

open Module ComplexConjugate

variable {q : ℝ} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0) (m : ℕ)

/-- The ladder basis divided by its positive lengths in the invariant metric. -/
def normalizedBasis : Basis (Fin (m + 1)) ℂ (LadderModule (q : ℂ) m 1) :=
  (basis (q : ℂ) m 1).unitsSMul fun i =>
    (Units.mk0 (Real.sqrt (innerWeight q m i) : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (innerWeight_pos hq hd (by omega))).ne'))⁻¹

/-- Each normalized vector is the original ladder vector divided by its length. -/
theorem normalizedBasis_apply (i : Fin (m + 1)) :
    normalizedBasis hq hd m i =
      (Real.sqrt (innerWeight q m i) : ℂ)⁻¹ • basis (q : ℂ) m 1 i := by
  simp [normalizedBasis, Basis.unitsSMul_apply, Units.smul_def]

/-- Coordinates in the normalized basis multiply the original coordinates by the lengths. -/
@[simp]
theorem normalizedBasis_repr (v : LadderModule (q : ℂ) m 1) (i : Fin (m + 1)) :
    (normalizedBasis hq hd m).repr v i =
      (Real.sqrt (innerWeight q m i) : ℂ) * (basis (q : ℂ) m 1).repr v i := by
  simp [normalizedBasis, Basis.repr_unitsSMul, Units.smul_def]

-- Not a simp lemma: `invariantForm_normalizedBasis_left` already extracts the coordinate.
/-- The normalized basis is orthonormal for the invariant Hermitian form. -/
theorem invariantForm_normalizedBasis (i j : Fin (m + 1)) :
    invariantForm q m (normalizedBasis hq hd m i) (normalizedBasis hq hd m j) =
      if i = j then 1 else 0 := by
  simp only [normalizedBasis_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    invariantForm_basis, map_inv₀, Complex.conj_ofReal, RingHom.id_apply]
  split_ifs with hij
  · subst j
    have hs : (Real.sqrt (innerWeight q m i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (innerWeight_pos hq hd (by omega))).ne'
    have hs2 : (Real.sqrt (innerWeight q m i) : ℂ) ^ 2 = (innerWeight q m i : ℂ) := by
      exact_mod_cast Real.sq_sqrt (innerWeight_pos hq hd (by omega)).le
    rw [← hs2]
    field_simp
  · simp

/-- Pairing a normalized basis vector with a vector extracts its normalized coordinate. -/
@[simp]
theorem invariantForm_normalizedBasis_left (i : Fin (m + 1))
    (v : LadderModule (q : ℂ) m 1) :
    invariantForm q m (normalizedBasis hq hd m i) v =
      (normalizedBasis hq hd m).repr v i := by
  conv_lhs => rw [← (normalizedBasis hq hd m).sum_repr v]
  simp [invariantForm_normalizedBasis]

variable [Fact ((q : ℂ) ≠ 0)]

/-- The weight generator remains diagonal under normalization. -/
theorem k_smul_normalizedBasis (i : Fin (m + 1)) :
    k (q : ℂ) • normalizedBasis hq hd m i =
      (q : ℂ) ^ ((m : ℤ) - 2 * i) • normalizedBasis hq hd m i := by
  simp [normalizedBasis_apply, smul_comm (k (q : ℂ)), k_smul_basis, smul_smul, mul_comm]

/-- The matrix of `K` in the normalized basis. -/
theorem toMatrix_rep_k_normalizedBasis :
    LinearMap.toMatrix (normalizedBasis hq hd m) (normalizedBasis hq hd m)
      (rep (q : ℂ) m 1 (k (q : ℂ))) =
      Matrix.diagonal (fun i : Fin (m + 1) => (q : ℂ) ^ ((m : ℤ) - 2 * i)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, ← smul_def, k_smul_normalizedBasis]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

/-- The raising matrix in the normalized basis; its only possible nonzero entries are
on the first superdiagonal. -/
theorem toMatrix_rep_e_normalizedBasis (i j : Fin (m + 1)) :
    LinearMap.toMatrix (normalizedBasis hq hd m) (normalizedBasis hq hd m)
      (rep (q : ℂ) m 1 (e (q : ℂ))) i j =
      if (j : ℕ) = i + 1 then
        quantumInteger (q : ℂ) ((m : ℤ) - i) *
          (Real.sqrt (innerWeight q m i) : ℂ) /
          (Real.sqrt (innerWeight q m j) : ℂ) else 0 := by
  rw [LinearMap.toMatrix_apply, normalizedBasis_apply, map_smul, normalizedBasis_repr,
    map_smul, Finsupp.smul_apply, ← smul_def, e_smul_basis]
  simp only [Units.val_one, Int.cast_one, one_mul, map_smul, Finsupp.smul_apply,
    basis_repr_vec, smul_eq_mul]
  by_cases hij : (j : ℕ) = i + 1
  · simp only [ite_eq_left (by omega : (i : ℤ) = (j : ℤ) - 1), ite_eq_left hij]
    rw [show (m : ℤ) - j + 1 = (m : ℤ) - i by omega]
    ring
  · simp [hij, show ¬(i : ℤ) = (j : ℤ) - 1 by omega]

/-- The lowering matrix in the normalized basis; its only possible nonzero entries are
on the first subdiagonal. -/
theorem toMatrix_rep_f_normalizedBasis (i j : Fin (m + 1)) :
    LinearMap.toMatrix (normalizedBasis hq hd m) (normalizedBasis hq hd m)
      (rep (q : ℂ) m 1 (f (q : ℂ))) i j =
      if (i : ℕ) = j + 1 then
        quantumInteger (q : ℂ) i *
          (Real.sqrt (innerWeight q m i) : ℂ) /
          (Real.sqrt (innerWeight q m j) : ℂ) else 0 := by
  rw [LinearMap.toMatrix_apply, normalizedBasis_apply, map_smul, normalizedBasis_repr,
    map_smul, Finsupp.smul_apply, ← smul_def, f_smul_basis]
  simp only [map_smul, Finsupp.smul_apply, basis_repr_vec, smul_eq_mul]
  by_cases hij : (i : ℕ) = j + 1
  · simp only [ite_eq_left (by omega : (i : ℤ) = (j : ℤ) + 1), ite_eq_left hij]
    rw [show (j : ℤ) + 1 = (i : ℤ) by omega]
    ring
  · simp [hij, show ¬(i : ℤ) = (j : ℤ) + 1 by omega]

/-- The fundamental weight matrix in the normalized basis. -/
theorem toMatrix_rep_k_normalizedBasis_one :
    LinearMap.toMatrix (normalizedBasis hq hd 1) (normalizedBasis hq hd 1)
      (rep (q : ℂ) 1 1 (k (q : ℂ))) = !![(q : ℂ), 0; 0, (q : ℂ)⁻¹] := by
  rw [toMatrix_rep_k_normalizedBasis]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]

/-- The fundamental raising matrix has upper-right entry `q^(-1/2)`. -/
theorem toMatrix_rep_e_normalizedBasis_one :
    LinearMap.toMatrix (normalizedBasis hq hd 1) (normalizedBasis hq hd 1)
      (rep (q : ℂ) 1 1 (e (q : ℂ))) = !![0, (Real.sqrt q : ℂ)⁻¹; 0, 0] := by
  have hdc : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := by exact_mod_cast hd
  ext i j
  rw [toMatrix_rep_e_normalizedBasis]
  fin_cases i <;> fin_cases j <;>
    norm_num [innerWeight_one_one hd, quantumInteger_one hdc]

/-- The fundamental lowering matrix has lower-left entry `q^(1/2)`. -/
theorem toMatrix_rep_f_normalizedBasis_one :
    LinearMap.toMatrix (normalizedBasis hq hd 1) (normalizedBasis hq hd 1)
      (rep (q : ℂ) 1 1 (f (q : ℂ))) = !![0, 0; (Real.sqrt q : ℂ), 0] := by
  have hdc : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := by exact_mod_cast hd
  ext i j
  rw [toMatrix_rep_f_normalizedBasis]
  fin_cases i <;> fin_cases j <;>
    norm_num [innerWeight_one_one hd, quantumInteger_one hdc]

end TauCeti.UqSl2.LadderModule
