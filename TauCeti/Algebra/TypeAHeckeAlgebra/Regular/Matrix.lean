/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis
public import TauCeti.GroupTheory.Coxeter.Hecke.Matrix

/-!
# Type-A regular Hecke matrices and PBW multiplication

The general fixed-carrier matrices are defined in
`TauCeti.GroupTheory.Coxeter.Hecke.Matrix`. Here we identify them with left and right
multiplication by `g_i = q T_i` in the type-A PBW basis, and prove their adjacent braid
and distant commutation relations. The comparison reuses the regular representation and
its coordinate map `TauCeti.TypeAHeckeAlgebra.basisTw_repr_apply`.

For positive real parameters this PBW basis is orthonormal for the regular form of
`TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Form`. Together with the general continuity
results, this realizes the parameter-dependent regular modules on one fixed carrier.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

open Matrix

namespace CoxeterSystem

open TauCeti TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {W : Type*} [Group W] {n : ℕ}
variable (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) [Fintype W]

section Multiplication

variable (q : Rˣ)

open Classical in
/-- The explicit left matrix is the matrix of multiplication by `g_i = q T_i` in the
PBW basis. For a star-fixed real or complex parameter this basis is orthonormal for the
regular trace form. -/
theorem heckeLeftMatrix_eq_leftMulMatrix [DecidableEq W] (i : Fin (n - 1)) :
    heckeLeftMatrix cs (q : R) i =
      Algebra.leftMulMatrix (basisTw q cs) ((q : R) • T q i) := by
  rw [heckeLeftMatrix_eq_toMatrix_heckeLeftMul]
  ext v w
  simp [Algebra.leftMulMatrix_eq_repr_mul, LinearMap.toMatrix_apply, coe_basisTw,
    basisTw_repr_apply, map_mul, regularRep_T, mul_apply_eq_comp]

open Classical in
/-- The explicit right matrix is the matrix of right multiplication by `g_i = q T_i`
in the PBW basis. -/
theorem heckeRightMatrix_eq_toMatrix [DecidableEq W] (i : Fin (n - 1)) :
    heckeRightMatrix cs (q : R) i = LinearMap.toMatrix (basisTw q cs) (basisTw q cs)
      (LinearMap.mulRight R ((q : R) • T q i)) := by
  rw [heckeRightMatrix_eq_toMatrix_heckeRightMul]
  ext v w
  have hc := LinearMap.congr_fun
    (commute_regularRep_heckeRightMul cs (Tw q cs w) i).eq (Finsupp.single 1 1)
  simp only [mul_apply_eq_comp, regularRep_Tw_apply_single_one] at hc
  simpa [LinearMap.toMatrix_apply, coe_basisTw, basisTw_repr_apply, map_mul,
    regularRep_T, mul_apply_eq_comp, cs.not_isLeftDescent_one, cs.not_isRightDescent_one]
    using congrArg (fun f : W →₀ R ↦ (q : R) * f v) hc.symm

/-- The fixed-coordinate left action agrees with multiplication on every vector. -/
theorem heckeLeftMatrix_mulVec_repr (i : Fin (n - 1))
    (x : TypeAHeckeAlgebra R q n) :
    heckeLeftMatrix cs (q : R) i *ᵥ (basisTw q cs).repr x =
      (basisTw q cs).repr (((q : R) • T q i) * x) := by
  classical
  rw [heckeLeftMatrix_eq_leftMulMatrix, Algebra.leftMulMatrix_mulVec_repr]

/-- The fixed-coordinate right action agrees with multiplication on every vector. -/
theorem heckeRightMatrix_mulVec_repr (i : Fin (n - 1))
    (x : TypeAHeckeAlgebra R q n) :
    heckeRightMatrix cs (q : R) i *ᵥ (basisTw q cs).repr x =
      (basisTw q cs).repr (x * ((q : R) • T q i)) := by
  classical
  rw [heckeRightMatrix_eq_toMatrix, LinearMap.toMatrix_mulVec_repr,
    LinearMap.mulRight_apply]

end Multiplication

section TypeARelations

variable (s : R)

/-- The left regular Hecke matrices satisfy the adjacent braid relation. -/
theorem heckeLeftMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    heckeLeftMatrix cs s i * heckeLeftMatrix cs s j * heckeLeftMatrix cs s i =
      heckeLeftMatrix cs s j * heckeLeftMatrix cs s i * heckeLeftMatrix cs s j := by
  classical
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeLeftMatrix cs t i * heckeLeftMatrix cs t j * heckeLeftMatrix cs t i)
    (fun _ _ t ↦ heckeLeftMatrix cs t j * heckeLeftMatrix cs t i * heckeLeftMatrix cs t j)
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix])
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix]) ?_ s
  intro q
  simp only [heckeLeftMatrix_eq_leftMulMatrix, ← map_mul, smul_mul_smul, T_braid h]

/-- The right regular Hecke matrices satisfy the adjacent braid relation. -/
theorem heckeRightMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    heckeRightMatrix cs s i * heckeRightMatrix cs s j * heckeRightMatrix cs s i =
      heckeRightMatrix cs s j * heckeRightMatrix cs s i * heckeRightMatrix cs s j := by
  classical
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeRightMatrix cs t i * heckeRightMatrix cs t j * heckeRightMatrix cs t i)
    (fun _ _ t ↦ heckeRightMatrix cs t j * heckeRightMatrix cs t i * heckeRightMatrix cs t j)
    (by intros; simp [Matrix.map_mul, map_heckeRightMatrix])
    (by intros; simp [Matrix.map_mul, map_heckeRightMatrix]) ?_ s
  intro q
  simp only [heckeRightMatrix_eq_toMatrix, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp only [mul_apply_eq_comp, LinearMap.mulRight_apply]
  have hb : ((q : LaurentPolynomial R) • T q i) * ((q : LaurentPolynomial R) • T q j) *
      ((q : LaurentPolynomial R) • T q i) =
      ((q : LaurentPolynomial R) • T q j) * ((q : LaurentPolynomial R) • T q i) *
        ((q : LaurentPolynomial R) • T q j) := by
    simp only [smul_mul_smul, T_braid h]
  simpa only [mul_assoc] using congrArg (fun a ↦ x * a) hb

/-- Distant left regular Hecke matrices commute. -/
theorem commute_heckeLeftMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (heckeLeftMatrix cs s i) (heckeLeftMatrix cs s j) := by
  classical
  rw [commute_iff_eq]
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeLeftMatrix cs t i * heckeLeftMatrix cs t j)
    (fun _ _ t ↦ heckeLeftMatrix cs t j * heckeLeftMatrix cs t i)
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix])
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix]) ?_ s
  intro q
  rw [← commute_iff_eq, heckeLeftMatrix_eq_leftMulMatrix, heckeLeftMatrix_eq_leftMulMatrix]
  exact (((commute_T h).smul_left (q : LaurentPolynomial R)).smul_right
    (q : LaurentPolynomial R)).map _

/-- Distant right regular Hecke matrices commute. -/
theorem commute_heckeRightMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (heckeRightMatrix cs s i) (heckeRightMatrix cs s j) := by
  classical
  rw [commute_iff_eq]
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeRightMatrix cs t i * heckeRightMatrix cs t j)
    (fun _ _ t ↦ heckeRightMatrix cs t j * heckeRightMatrix cs t i)
    (by intros; simp [Matrix.map_mul, map_heckeRightMatrix])
    (by intros; simp [Matrix.map_mul, map_heckeRightMatrix]) ?_ s
  intro q
  rw [heckeRightMatrix_eq_toMatrix, heckeRightMatrix_eq_toMatrix,
    ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp [smul_smul, mul_assoc, (commute_T (q := q) h).eq]

end TypeARelations

end CoxeterSystem
