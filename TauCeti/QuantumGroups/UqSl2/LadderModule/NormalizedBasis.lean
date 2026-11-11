/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.InnerProduct
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

include hq hd in
private theorem sqrt_innerWeight_ne_zero (i : Fin (m + 1)) :
    (Real.sqrt (innerWeight q m i) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (innerWeight_pos hq hd (by omega))).ne'

include hq hd in
private theorem sq_sqrt_innerWeight (i : Fin (m + 1)) :
    (Real.sqrt (innerWeight q m i) : ℂ) ^ 2 = (innerWeight q m i : ℂ) := by
  exact_mod_cast Real.sq_sqrt (innerWeight_pos hq hd (by omega)).le

/-- The ladder basis divided by its positive lengths in the invariant metric. -/
def normalizedBasis : Basis (Fin (m + 1)) ℂ (LadderModule (q : ℂ) m 1) :=
  (basis (q : ℂ) m 1).unitsSMul fun i =>
    (Units.mk0 (Real.sqrt (innerWeight q m i) : ℂ)
      (sqrt_innerWeight_ne_zero hq hd m i))⁻¹

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
    rw [← sq_sqrt_innerWeight hq hd m i]
    field_simp [sqrt_innerWeight_ne_zero hq hd m i]
  · simp

/-- Pairing a normalized basis vector with a vector extracts its normalized coordinate. -/
@[simp]
theorem invariantForm_normalizedBasis_left (i : Fin (m + 1))
    (v : LadderModule (q : ℂ) m 1) :
    invariantForm q m (normalizedBasis hq hd m i) v =
      (normalizedBasis hq hd m).repr v i := by
  conv_lhs => rw [← (normalizedBasis hq hd m).sum_repr v]
  simp [invariantForm_normalizedBasis]

/-- Pairing with a normalized basis vector extracts the conjugate normalized coordinate. -/
@[simp]
theorem invariantForm_normalizedBasis_right (v : LadderModule (q : ℂ) m 1)
    (j : Fin (m + 1)) :
    invariantForm q m v (normalizedBasis hq hd m j) =
      conj ((normalizedBasis hq hd m).repr v j) := by
  rw [← invariantForm_symm, invariantForm_normalizedBasis_left, Complex.star_def]

variable [Fact ((q : ℂ) ≠ 0)]

/-- The weight generator remains diagonal under normalization. -/
@[simp]
theorem k_smul_normalizedBasis (i : Fin (m + 1)) :
    k (q : ℂ) • normalizedBasis hq hd m i =
      (q : ℂ) ^ ((m : ℤ) - 2 * i) • normalizedBasis hq hd m i := by
  simp [normalizedBasis_apply, smul_comm (k (q : ℂ)), k_smul_basis, smul_smul, mul_comm]

/-- The inverse weight generator remains diagonal under normalization. -/
@[simp]
theorem kInv_smul_normalizedBasis (i : Fin (m + 1)) :
    kInv (q : ℂ) • normalizedBasis hq hd m i =
      (q : ℂ) ^ (-((m : ℤ) - 2 * i)) • normalizedBasis hq hd m i := by
  simp [normalizedBasis_apply, smul_comm (kInv (q : ℂ)), kInv_smul_basis,
    smul_smul, mul_comm]

/-- Raising a normalized vector, with zero at the highest weight. -/
@[simp]
theorem e_smul_normalizedBasis (j : Fin (m + 1)) :
    e (q : ℂ) • normalizedBasis hq hd m j =
      if h : 0 < (j : ℕ) then
        (quantumInteger (q : ℂ) ((m : ℤ) - j + 1) *
          (Real.sqrt (innerWeight q m (j - 1)) : ℂ) /
          (Real.sqrt (innerWeight q m j) : ℂ)) •
            normalizedBasis hq hd m ⟨j - 1, by omega⟩
      else 0 := by
  rw [normalizedBasis_apply, smul_comm, e_smul_basis]
  split_ifs with h
  · have hv : vec (q : ℂ) m 1 ((j : ℤ) - 1) =
        basis (q : ℂ) m 1 ⟨j - 1, by omega⟩ := by
      convert vec_coe (q := (q : ℂ)) (ε := 1) (⟨j - 1, by omega⟩ : Fin (m + 1)) using 1
      push_cast [Nat.cast_sub (by omega : 1 ≤ (j : ℕ))]
      rfl
    rw [hv, normalizedBasis_apply]
    simp only [Units.val_one, Int.cast_one, one_mul, smul_smul]
    congr 1
    field_simp [sqrt_innerWeight_ne_zero hq hd m ⟨j - 1, by omega⟩]
  · rw [vec_eq_zero_of_neg (by omega), smul_zero, smul_zero]

/-- Lowering a normalized vector, with zero at the lowest weight. -/
@[simp]
theorem f_smul_normalizedBasis (j : Fin (m + 1)) :
    f (q : ℂ) • normalizedBasis hq hd m j =
      if h : (j : ℕ) < m then
        (quantumInteger (q : ℂ) ((j : ℤ) + 1) *
          (Real.sqrt (innerWeight q m (j + 1)) : ℂ) /
          (Real.sqrt (innerWeight q m j) : ℂ)) •
            normalizedBasis hq hd m ⟨j + 1, by omega⟩
      else 0 := by
  rw [normalizedBasis_apply, smul_comm, f_smul_basis]
  split_ifs with h
  · have hv : vec (q : ℂ) m 1 ((j : ℤ) + 1) =
        basis (q : ℂ) m 1 ⟨j + 1, by omega⟩ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (vec_coe (q := (q : ℂ)) (ε := 1) (⟨j + 1, by omega⟩ : Fin (m + 1)))
    rw [hv, normalizedBasis_apply, smul_smul, smul_smul]
    congr 1
    field_simp [sqrt_innerWeight_ne_zero hq hd m ⟨j + 1, by omega⟩]
  · rw [vec_eq_zero_of_lt (by omega), smul_zero, smul_zero]

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
  rw [LinearMap.toMatrix_apply, ← smul_def, e_smul_normalizedBasis]
  by_cases h : 0 < (j : ℕ)
  · simp only [dite_eq_left h, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hij : (j : ℕ) = i + 1
    · have heq : (⟨j - 1, by omega⟩ : Fin (m + 1)) = i := by ext; dsimp; omega
      rw [ite_eq_left heq, ite_eq_left hij]
      rw [show (j : ℕ) - 1 = i by omega,
        show (m : ℤ) - j + 1 = (m : ℤ) - i by omega]
      simp
    · have heq : (⟨j - 1, by omega⟩ : Fin (m + 1)) ≠ i := by
        intro he; have := congrArg Fin.val he; dsimp at this; omega
      simp only [ite_eq_right heq, ite_eq_right hij, mul_zero]
  · simp only [dite_eq_right h, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      ite_eq_right (show ¬(j : ℕ) = i + 1 by omega)]

/-- The lowering matrix in the normalized basis; its only possible nonzero entries are
on the first subdiagonal. -/
theorem toMatrix_rep_f_normalizedBasis (i j : Fin (m + 1)) :
    LinearMap.toMatrix (normalizedBasis hq hd m) (normalizedBasis hq hd m)
      (rep (q : ℂ) m 1 (f (q : ℂ))) i j =
      if (i : ℕ) = j + 1 then
        quantumInteger (q : ℂ) i *
          (Real.sqrt (innerWeight q m i) : ℂ) /
          (Real.sqrt (innerWeight q m j) : ℂ) else 0 := by
  rw [LinearMap.toMatrix_apply, ← smul_def, f_smul_normalizedBasis]
  by_cases h : (j : ℕ) < m
  · simp only [dite_eq_left h, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hij : (i : ℕ) = j + 1
    · have heq : (⟨j + 1, by omega⟩ : Fin (m + 1)) = i := by ext; dsimp; omega
      rw [ite_eq_left heq, ite_eq_left hij]
      rw [← hij, show (j : ℤ) + 1 = (i : ℤ) by omega]
      simp
    · have heq : (⟨j + 1, by omega⟩ : Fin (m + 1)) ≠ i := by
        intro he; have := congrArg Fin.val he; dsimp at this; omega
      simp only [ite_eq_right heq, ite_eq_right hij, mul_zero]
  · simp only [dite_eq_right h, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      ite_eq_right (show ¬(i : ℕ) = j + 1 by omega)]

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
