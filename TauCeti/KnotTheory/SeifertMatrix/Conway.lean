/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Alexander
public import TauCeti.Algebra.Polynomial.Laurent.SignedInversion
public import TauCeti.LinearAlgebra.Matrix.CornerMinor

/-!
# The Seifert determinant and its Conway skein calculation

The determinant of `s V - s⁻¹ Vᵀ` makes sense for Seifert matrices of both odd and even size.
Here `s` is a Laurent variable representing the square root of the Alexander variable. For
an even matrix it is the existing normalized Alexander polynomial after doubling exponents.
Allowing odd sizes is essential: smoothing a crossing changes the rank of a Seifert surface's
first homology by one.

Changing a diagonal entry of `V` by `r` changes this determinant by
`r (s - s⁻¹)` times the determinant for the matrix with that row and column deleted.
This is the algebraic calculation underlying the Conway skein relation. For the negative-normal
push-off convention, decreasing that entry by one gives the factor `s⁻¹ - s`. No construction
of Seifert surfaces for a diagram skein triple is asserted here.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapters 6 and 8, especially Theorem 8.6 (the Conway-normalized skein relation).

The determinant is unchanged by reindexing and by a congruence `V ↦ P V Pᵀ` with
`(det P)² = 1`, such as an integral change of basis of the first homology of the surface.

The normalization comparison uses `TauCeti.KnotTheory.alexander`. The minor calculation uses
`Matrix.det_updateCol_last_single` and Mathlib's column multilinearity of the determinant.
-/

public section

open LaurentPolynomial
open scoped Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The matrix `s V - s⁻¹ Vᵀ` over Laurent polynomials, with `s` representing the square root
of the Alexander variable. Unlike genus normalization, this formula allows odd matrix sizes. -/
noncomputable def seifertConwayMatrix (V : Matrix ι ι R) : Matrix ι ι R[T;T⁻¹] :=
  (T 1 : R[T;T⁻¹]) • V.map C - (T (-1) : R[T;T⁻¹]) • (V.map C)ᵀ

/-- The entries of the half-power Seifert matrix. -/
@[simp]
theorem seifertConwayMatrix_apply (V : Matrix ι ι R) (i j : ι) :
    V.seifertConwayMatrix i j = T 1 * C (V i j) - T (-1) * C (V j i) := by
  simp [seifertConwayMatrix]

/-- Taking a submatrix commutes with the half-power Seifert construction. -/
@[simp]
theorem seifertConwayMatrix_submatrix {κ : Type*} (V : Matrix ι ι R) (e : κ → ι) :
    (V.submatrix e e).seifertConwayMatrix = V.seifertConwayMatrix.submatrix e e := by
  ext i j : 2
  simp

/-- Evaluating the half-power Seifert matrix at a unit `s` gives `s V - s⁻¹ Vᵀ`,
with coefficients transported by the chosen ring homomorphism. -/
@[simp]
theorem map_eval₂_seifertConwayMatrix {S : Type*} [CommRing S]
    (V : Matrix ι ι R) (f : R →+* S) (s : Sˣ) :
    V.seifertConwayMatrix.map (eval₂ f s) =
      (s : S) • V.map f - (s⁻¹ : Sˣ).val • (V.map f)ᵀ := by
  ext i j : 2
  simp only [map_apply, seifertConwayMatrix_apply, map_sub, map_mul, eval₂_T, eval₂_C,
    sub_apply, smul_apply, smul_eq_mul, transpose_apply, zpow_one, zpow_neg_one]

/-- Doubling Laurent exponents in the Alexander matrix and multiplying by `s⁻¹` gives
`s V - s⁻¹ Vᵀ`. -/
private theorem seifertConwayMatrix_eq_smul_map_alexanderMatrix (V : Matrix ι ι R) :
    V.seifertConwayMatrix = (T (-1) : R[T;T⁻¹]) •
      (TauCeti.KnotTheory.alexanderMatrix V).map
        (AddMonoidAlgebra.mapDomainRingHom R (nsmulAddMonoidHom 2 : ℤ →+ ℤ)) := by
  ext i j : 2
  simp only [seifertConwayMatrix_apply, smul_apply, smul_eq_mul, map_apply,
    TauCeti.KnotTheory.alexanderMatrix_apply, map_sub, map_mul]
  have hT (k : ℤ) : AddMonoidAlgebra.mapDomainRingHom R
      (nsmulAddMonoidHom 2 : ℤ →+ ℤ) (T k) = T (2 * k) := by
    rw [T, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
    rfl
  have hC (a : R) : AddMonoidAlgebra.mapDomainRingHom R
      (nsmulAddMonoidHom 2 : ℤ →+ ℤ) (C a) = C a := by
    rw [← single_eq_C, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    rfl
  rw [hT, hC, hC, mul_sub, ← mul_assoc, ← T_add]
  norm_num

/-- Signed inversion transposes the half-power Seifert matrix. -/
@[simp] theorem map_signedInvert_seifertConwayMatrix (V : Matrix ι ι R) :
    V.seifertConwayMatrix.map signedInvert = V.seifertConwayMatrixᵀ := by
  ext i j : 2
  simp [seifertConwayMatrix_apply, sub_eq_add_neg, add_comm]

variable [Fintype ι] [DecidableEq ι]

/-- The Laurent determinant `det(s V - s⁻¹ Vᵀ)`. This is the Seifert-matrix expression used
in the Conway skein calculation; no polynomial in `s - s⁻¹` is chosen by this definition. -/
noncomputable def seifertConwayDeterminant (V : Matrix ι ι R) : R[T;T⁻¹] :=
  V.seifertConwayMatrix.det

/-- The defining determinant expression. -/
theorem seifertConwayDeterminant_def (V : Matrix ι ι R) :
    V.seifertConwayDeterminant = V.seifertConwayMatrix.det :=
  (rfl)

/-- Evaluation of the Seifert determinant at a unit parameter is the determinant of
`s V - s⁻¹ Vᵀ`. -/
@[simp]
theorem eval₂_seifertConwayDeterminant {S : Type*} [CommRing S]
    (V : Matrix ι ι R) (f : R →+* S) (s : Sˣ) :
    eval₂ f s V.seifertConwayDeterminant =
      ((s : S) • V.map f - (s⁻¹ : Sˣ).val • (V.map f)ᵀ).det := by
  rw [seifertConwayDeterminant_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_eval₂_seifertConwayMatrix]

/-- The empty Seifert matrix, corresponding to a disc, has determinant one. -/
@[simp]
theorem seifertConwayDeterminant_of_isEmpty [IsEmpty ι] (V : Matrix ι ι R) :
    V.seifertConwayDeterminant = 1 := by
  simp [seifertConwayDeterminant]

/-- The Seifert determinant is unchanged by a simultaneous bijective reindexing of the rows and
columns, including between different finite index types. -/
@[simp]
theorem seifertConwayDeterminant_submatrix_equiv_self {κ : Type*} [Fintype κ] [DecidableEq κ]
    (V : Matrix ι ι R) (e : κ ≃ ι) :
    (V.submatrix e e).seifertConwayDeterminant = V.seifertConwayDeterminant := by
  rw [seifertConwayDeterminant_def, seifertConwayMatrix_submatrix, det_submatrix_equiv_self,
    seifertConwayDeterminant_def]

omit [DecidableEq ι] in
/-- A change of basis of the Seifert form, `V ↦ P V Pᵀ`, acts on the half-power Seifert matrix
by the same congruence. -/
theorem seifertConwayMatrix_mul_mul_transpose (P V : Matrix ι ι R) :
    (P * V * Pᵀ).seifertConwayMatrix =
      P.map C * V.seifertConwayMatrix * (P.map C)ᵀ := by
  simp only [seifertConwayMatrix, Matrix.map_mul, transpose_mul, transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    transpose_map]

/-- Congruence multiplies the Seifert determinant by the square of the determinant of the
congruence matrix. -/
theorem seifertConwayDeterminant_congruence (P V : Matrix ι ι R) :
    (P * V * Pᵀ).seifertConwayDeterminant = C P.det ^ 2 * V.seifertConwayDeterminant := by
  rw [seifertConwayDeterminant_def, seifertConwayMatrix_mul_mul_transpose, det_mul, det_mul,
    det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, seifertConwayDeterminant_def]
  ring

/-- **The Seifert determinant is a congruence invariant** as soon as the determinant of the
congruence matrix squares to `1`, as it does for a change of basis over `ℤ`. -/
theorem seifertConwayDeterminant_congruence_of_det_sq_eq_one {P : Matrix ι ι R}
    (V : Matrix ι ι R) (hP : P.det ^ 2 = 1) :
    (P * V * Pᵀ).seifertConwayDeterminant = V.seifertConwayDeterminant := by
  rw [seifertConwayDeterminant_congruence, ← map_pow, hP, map_one, one_mul]

/-- The half-power Seifert determinant is fixed by `s ↦ -s⁻¹`, in every matrix size. -/
@[simp] theorem signedInvert_seifertConwayDeterminant (V : Matrix ι ι R) :
    signedInvert V.seifertConwayDeterminant = V.seifertConwayDeterminant := by
  rw [seifertConwayDeterminant_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_signedInvert_seifertConwayMatrix, det_transpose]

/-- Every half-power Seifert determinant is a polynomial in `s⁻¹ - s`, including
odd-size matrices, with coefficients in the original commutative ring. -/
theorem exists_polynomial_eval₂_eq_seifertConwayDeterminant (V : Matrix ι ι R) :
    ∃ p : R[X], Polynomial.eval₂ C (T (-1) - T 1) p = V.seifertConwayDeterminant :=
  exists_eval₂_T_neg_sub_T (signedInvert_seifertConwayDeterminant V)

/-- For a matrix of size `2g`, the half-power determinant is the normalized Alexander
polynomial with its exponents doubled: `det(s V - s⁻¹ Vᵀ) = Δ_V(s²)`. -/
theorem seifertConwayDeterminant_eq_map_alexander (V : Matrix ι ι R) {g : ℕ}
    (hcard : Fintype.card ι = 2 * g) :
    V.seifertConwayDeterminant =
      AddMonoidAlgebra.mapDomainRingHom R (nsmulAddMonoidHom 2 : ℤ →+ ℤ)
        (TauCeti.KnotTheory.alexander V) := by
  rw [seifertConwayDeterminant_def, seifertConwayMatrix_eq_smul_map_alexanderMatrix,
    det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    TauCeti.KnotTheory.alexander_eq_of_card V hcard, map_mul, T_pow]
  congr 1
  simp only [T, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
    nsmulAddMonoidHom_apply, nsmul_eq_mul]
  congr 1
  simp only [hcard, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- Changing a diagonal entry by `r` changes the half-power Seifert matrix in that entry
by `r (s - s⁻¹)`. -/
private theorem seifertConwayMatrix_add_diagonal_single {n : ℕ}
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    (V + diagonal (Pi.single (Fin.last n) r)).seifertConwayMatrix =
      V.seifertConwayMatrix.updateCol (Fin.last n)
        (fun i => V.seifertConwayMatrix i (Fin.last n) +
          ((T 1 - T (-1)) * C r) * (Pi.single (Fin.last n) 1 : Fin (n + 1) → R[T;T⁻¹]) i) := by
  ext i j : 2
  by_cases hj : j = Fin.last n
  · subst j
    by_cases hi : i = Fin.last n
    · subst i
      simp only [seifertConwayMatrix_apply, add_apply, diagonal_apply_eq, updateCol_self,
        Pi.single_eq_same, map_add, mul_one]
      ring_nf
    · simp [seifertConwayMatrix_apply, hi, Ne.symm hi]
  · by_cases hi : i = j
    · subst i
      simp [seifertConwayMatrix_apply, hj]
    · simp [seifertConwayMatrix_apply, hi, Ne.symm hi, hj]

/-- The skein calculation for the last diagonal entry of a matrix indexed by `Fin (n + 1)`. -/
private theorem seifertConwayDeterminant_add_diagonal_single_last {n : ℕ}
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    (V + diagonal (Pi.single (Fin.last n) r)).seifertConwayDeterminant -
        V.seifertConwayDeterminant =
      (T 1 - T (-1)) * C r *
        (V.submatrix Fin.castSucc Fin.castSucc).seifertConwayDeterminant := by
  rw [seifertConwayDeterminant_def, seifertConwayMatrix_add_diagonal_single]
  have hcol : (fun i => V.seifertConwayMatrix i (Fin.last n) +
      ((T 1 - T (-1)) * C r) * (Pi.single (Fin.last n) 1 : Fin (n + 1) → R[T;T⁻¹]) i) =
      (fun i => V.seifertConwayMatrix i (Fin.last n)) +
        ((T 1 - T (-1)) * C r) • (Pi.single (Fin.last n) 1 : Fin (n + 1) → R[T;T⁻¹]) := by
    ext i
    simp
  rw [hcol, det_updateCol_add, det_updateCol_smul, updateCol_eq_self,
    det_updateCol_last_single, seifertConwayDeterminant_def,
    seifertConwayDeterminant_def, seifertConwayMatrix_submatrix]
  abel

/-- **The Seifert determinant skein calculation.** Increasing the diagonal entry of `V` at `x`
by `r` changes `det(s V - s⁻¹ Vᵀ)` by `r (s - s⁻¹)` times the determinant of the minor with the
row and column of `x` deleted. This includes rank one, where the minor is empty and its
determinant is one. -/
theorem seifertConwayDeterminant_add_diagonal_single (V : Matrix ι ι R) (x : ι) (r : R) :
    (V + diagonal (Pi.single x r)).seifertConwayDeterminant - V.seifertConwayDeterminant =
      (T 1 - T (-1)) * C r *
        (V.submatrix ((↑) : {y // y ≠ x} → ι) (↑)).seifertConwayDeterminant := by
  -- enumerate `ι` by `Fin (k + 1)` with `x` last, and apply the calculation for the last entry
  let E : Fin (Fintype.card {y // y ≠ x} + 1) ≃ ι := finSuccEquivLast.trans
    ((Equiv.optionCongr (Fintype.equivFin {y // y ≠ x}).symm).trans (Equiv.optionSubtypeNe x))
  have hlast : E (Fin.last _) = x := by
    simp only [E, Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionCongr_apply,
      Option.map_none, Equiv.optionSubtypeNe_none]
  have hcast (j : Fin (Fintype.card {y // y ≠ x})) :
      E j.castSucc = ((Fintype.equivFin {y // y ≠ x}).symm j : ι) := by
    simp only [E, Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionCongr_apply,
      Option.map_some, Equiv.optionSubtypeNe_some]
  have hsingle : (Pi.single x r : ι → R) ∘ E = Pi.single (Fin.last _) r := by
    ext j
    induction j using Fin.lastCases with
    | last => simp [hlast]
    | cast j =>
      have hj := ((Fintype.equivFin {y // y ≠ x}).symm j).2
      simp [hcast, hj, Fin.castSucc_ne_last]
  have hminor : (V.submatrix E E).submatrix Fin.castSucc Fin.castSucc =
      (V.submatrix ((↑) : {y // y ≠ x} → ι) (↑)).submatrix (Fintype.equivFin _).symm
        (Fintype.equivFin _).symm := by
    ext j k
    simp [hcast]
  have hsum : (V + diagonal (Pi.single x r)).submatrix E E =
      V.submatrix E E + diagonal (Pi.single (Fin.last _) r) := by
    rw [← hsingle, ← submatrix_diagonal_equiv, submatrix_add, Pi.add_apply, Pi.add_apply]
  rw [← seifertConwayDeterminant_submatrix_equiv_self (V + _) E,
    ← seifertConwayDeterminant_submatrix_equiv_self V E, hsum,
    seifertConwayDeterminant_add_diagonal_single_last, hminor,
    seifertConwayDeterminant_submatrix_equiv_self]

end Matrix
