/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Matrices of formal power series

Collecting coefficients degree by degree identifies a square matrix of formal power series
`Matrix n n R⟦X⟧` with a formal power series of square matrices `(Matrix n n R)⟦X⟧`, giving a ring
isomorphism `Matrix.powerSeriesRingEquiv` over any semiring `R` and an `S`-algebra isomorphism
`Matrix.powerSeriesAlgEquiv` over any commutative base `S` (the power-series counterpart of
`matPolyEquiv` in `Mathlib.RingTheory.MatrixPolynomialAlgebra`, without needing commutativity of
`R`).

Transporting `PowerSeries.isUnit_iff_constantCoeff` across `Matrix.powerSeriesRingEquiv` shows that
a square matrix of formal power series over an arbitrary ring `R` is a two-sided unit if and only if
its constant-coefficient matrix in `Matrix n n R` is a unit
(`Matrix.isUnit_iff_isUnit_map_constantCoeff`), without requiring commutativity or determinants. In
particular, reducing modulo `X` gives a split surjection `GL n R⟦X⟧ →* GL n R`
(`Matrix.GeneralLinearGroup.map_constantCoeff_surjective`).

Finally, for a square matrix `A` over a nontrivial ring `R`, no column of a right inverse of
`M = (1 + X²) I - X A` has polynomial entries
(`Matrix.exists_coeff_ne_zero_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one`).

## Main definitions

* `Matrix.powerSeriesRingEquiv`: the ring isomorphism `Matrix n n R⟦X⟧ ≃+* (Matrix n n R)⟦X⟧`.
* `Matrix.powerSeriesAlgEquiv`: the `S`-algebra isomorphism
  `Matrix n n R⟦X⟧ ≃ₐ[S] (Matrix n n R)⟦X⟧`.

## Main results

* `Matrix.isUnit_iff_isUnit_map_constantCoeff`: a square matrix over `R⟦X⟧` is a unit if and only
  if its entrywise constant-coefficient matrix over `R` is a unit.
* `Matrix.GeneralLinearGroup.map_constantCoeff_surjective`: `GL n R⟦X⟧ →* GL n R` is surjective.
* `Matrix.exists_coeff_ne_zero_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one`: every column of a
  right inverse of `(1 + X²) I - X A` has nonzero coefficients in arbitrarily high degree.

## References

* `matPolyEquiv` in `Mathlib.RingTheory.MatrixPolynomialAlgebra` for the polynomial analogue.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Section 3, where `(1 + X²) I - X A` is the Hilbert-series denominator of a
  preprojective algebra.
-/

public section

namespace Matrix

open PowerSeries

section RingEquiv

variable {n R : Type*} [Semiring R] [Fintype n] [DecidableEq n]

/-- **Ring isomorphism between square matrices of power series and power series of square
matrices.** Over any semiring `R`, `Matrix n n R⟦X⟧` and `(Matrix n n R)⟦X⟧` are isomorphic
rings. -/
noncomputable def powerSeriesRingEquiv : Matrix n n R⟦X⟧ ≃+* (Matrix n n R)⟦X⟧ where
  toFun M := PowerSeries.mk fun k => Matrix.of fun i j => coeff k (M i j)
  invFun P := Matrix.of fun i j => PowerSeries.mk fun k => coeff k P i j
  left_inv M := by
    ext i j k
    simp
  right_inv P := by
    refine PowerSeries.ext fun k => Matrix.ext fun i j => ?_
    simp
  map_add' M N := by
    refine PowerSeries.ext fun k => Matrix.ext fun i j => ?_
    simp
  map_mul' M N := by
    refine PowerSeries.ext fun k => Matrix.ext fun i j => ?_
    simp only [coeff_mk, of_apply, Matrix.mul_apply, map_sum, coeff_mul, Matrix.sum_apply]
    exact Finset.sum_comm

@[simp]
theorem coeff_powerSeriesRingEquiv (M : Matrix n n R⟦X⟧) (k : ℕ) :
    coeff k (powerSeriesRingEquiv M) = M.map (coeff k) := by
  ext i j
  simp [powerSeriesRingEquiv]

@[simp]
theorem coeff_powerSeriesRingEquiv_apply (M : Matrix n n R⟦X⟧) (k : ℕ) (i j : n) :
    coeff k (powerSeriesRingEquiv M) i j = coeff k (M i j) := by
  simp [coeff_powerSeriesRingEquiv]

@[simp]
theorem constantCoeff_powerSeriesRingEquiv (M : Matrix n n R⟦X⟧) :
    constantCoeff (powerSeriesRingEquiv M) = M.map constantCoeff := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_powerSeriesRingEquiv]
  ext i j
  simp

@[simp]
theorem coeff_powerSeriesRingEquiv_symm_apply (P : (Matrix n n R)⟦X⟧) (i j : n) (k : ℕ) :
    coeff k (powerSeriesRingEquiv.symm P i j) = coeff k P i j := by
  rw [← coeff_powerSeriesRingEquiv_apply (powerSeriesRingEquiv.symm P) k i j,
    RingEquiv.apply_symm_apply]

@[simp]
theorem constantCoeff_powerSeriesRingEquiv_symm_apply (P : (Matrix n n R)⟦X⟧) (i j : n) :
    constantCoeff (powerSeriesRingEquiv.symm P i j) = constantCoeff P i j := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_powerSeriesRingEquiv_symm_apply]

@[simp]
theorem powerSeriesRingEquiv_map_C (A : Matrix n n R) :
    powerSeriesRingEquiv (A.map C) = C A := by
  refine PowerSeries.ext fun k => Matrix.ext fun i j => ?_
  simp [coeff_C, apply_ite (fun M : Matrix n n R => M i j)]

@[simp]
theorem powerSeriesRingEquiv_symm_C (A : Matrix n n R) :
    powerSeriesRingEquiv.symm (C A) = A.map C :=
  powerSeriesRingEquiv.symm_apply_eq.mpr (powerSeriesRingEquiv_map_C A).symm

@[simp]
theorem powerSeriesRingEquiv_X_smul_one :
    powerSeriesRingEquiv ((X : R⟦X⟧) • (1 : Matrix n n R⟦X⟧)) = X := by
  refine PowerSeries.ext fun k => Matrix.ext fun i j => ?_
  by_cases hk : k = 1 <;> by_cases hij : i = j <;> simp [hk, hij, coeff_X]

@[simp]
theorem powerSeriesRingEquiv_symm_X :
    powerSeriesRingEquiv.symm (X : (Matrix n n R)⟦X⟧) = (X : R⟦X⟧) • (1 : Matrix n n R⟦X⟧) :=
  powerSeriesRingEquiv.symm_apply_eq.mpr powerSeriesRingEquiv_X_smul_one.symm

end RingEquiv

section AlgEquiv

variable (S : Type*) {n R : Type*} [CommSemiring S] [Semiring R] [Algebra S R]
  [Fintype n] [DecidableEq n]

/-- **Algebra isomorphism between square matrices of power series and power series of square
matrices.** Over any commutative base `S` and `S`-algebra `R` (not necessarily commutative),
`Matrix n n R⟦X⟧` and `(Matrix n n R)⟦X⟧` are isomorphic `S`-algebras. -/
noncomputable def powerSeriesAlgEquiv : Matrix n n R⟦X⟧ ≃ₐ[S] (Matrix n n R)⟦X⟧ :=
  { powerSeriesRingEquiv with
    commutes' r := by
      refine PowerSeries.ext fun k => Matrix.ext fun i j => ?_
      by_cases hk : k = 0 <;> by_cases hij : i = j <;>
        simp [Algebra.algebraMap_eq_smul_one, hk, hij, coeff_one] }

@[simp]
theorem coe_powerSeriesAlgEquiv (M : Matrix n n R⟦X⟧) :
    powerSeriesAlgEquiv S M = powerSeriesRingEquiv M :=
  (rfl)

@[simp]
theorem coe_powerSeriesAlgEquiv_symm (P : (Matrix n n R)⟦X⟧) :
    (powerSeriesAlgEquiv S).symm P = powerSeriesRingEquiv.symm P :=
  (rfl)

end AlgEquiv

section Units

variable {n R : Type*} [Ring R] [Fintype n] [DecidableEq n]

/-- **A square matrix of formal power series is invertible if and only if its constant-coefficient
matrix is invertible.** Over any (possibly noncommutative) ring `R`, `M : Matrix n n R⟦X⟧` is a
two-sided unit exactly when `M.map constantCoeff : Matrix n n R` is a two-sided unit. -/
theorem isUnit_iff_isUnit_map_constantCoeff {M : Matrix n n R⟦X⟧} :
    IsUnit M ↔ IsUnit (M.map constantCoeff) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using PowerSeries.isUnit_iff_constantCoeff.mp (h.map powerSeriesRingEquiv)
  · have hP : IsUnit (powerSeriesRingEquiv M) :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using h)
    simpa using hP.map powerSeriesRingEquiv.symm

end Units

namespace GeneralLinearGroup

/-- Evaluating a formal power-series matrix at `X = 0` is a surjective homomorphism
`GL n R⟦X⟧ →* GL n R`, split by constant matrices `GeneralLinearGroup.map C`. -/
theorem map_constantCoeff_surjective {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    Function.Surjective (GeneralLinearGroup.map (n := n) (constantCoeff (R := R))) := fun g₀ =>
  ⟨g₀.map C, by
    ext i j
    simp⟩

end GeneralLinearGroup

/-- **No column of a right inverse of `(1 + X²) I - X A` is polynomial.** If
`((1 + X²) I - X A) N = I` for a matrix `A` over a nontrivial ring `R`, then for every column `j`
and every degree `d`, some entry of the `j`-th column of `N` has a nonzero coefficient in a degree
`n ≥ d`. -/
theorem exists_coeff_ne_zero_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one {R ι : Type*} [Ring R]
    [Nontrivial R] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) {N : Matrix ι ι R⟦X⟧}
    (hN : (((1 : R⟦X⟧) + X ^ 2) • (1 : Matrix ι ι R⟦X⟧) - (X : R⟦X⟧) • A.map C) * N = 1)
    (j : ι) (d : ℕ) : ∃ n ≥ d, ∃ i, coeff n (N i j) ≠ 0 := by
  have happly (i : ι) :
      ((((1 : R⟦X⟧) + X ^ 2) • (1 : Matrix ι ι R⟦X⟧) - (X : R⟦X⟧) • A.map C) * N) i j =
        ((1 : R⟦X⟧) + X ^ 2) * N i j - X * ∑ l, C (A i l) * N l j := by
    rw [sub_mul]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.map_apply]
  -- The coefficients of the `j`-th column of `N` satisfy `N_{n+2} = A N_{n+1} - N_n`.
  have hrec (n : ℕ) (i : ι) : coeff (n + 2) (N i j) + coeff n (N i j) =
      ∑ l, A i l * coeff (n + 1) (N l j) := by
    have h := congrArg (fun P => coeff (n + 2) (P i j)) hN
    simp only [happly, Matrix.one_apply, apply_ite (coeff (n + 2)), coeff_one, map_zero] at h
    simpa [add_mul, coeff_X_pow_mul', coeff_C_mul, sub_eq_zero] using h
  -- Descending induction from degree `d` kills every coefficient of the `j`-th column.
  by_contra! hd
  have hzero (t : ℕ) : ∀ n, d ≤ n + t → ∀ i, coeff n (N i j) = 0 := by
    induction t with
    | zero => simpa using hd
    | succ t ih =>
      intro n hn i
      simpa [ih (n + 1) (by omega), ih (n + 2) (by omega)] using hrec n i
  -- But the constant term of `N` is the identity matrix.
  have h0 := hzero d 0 (by omega) j
  rw [coeff_zero_eq_constantCoeff_apply] at h0
  simpa [happly, h0] using congrArg (fun P => constantCoeff (P j j)) hN

end Matrix
