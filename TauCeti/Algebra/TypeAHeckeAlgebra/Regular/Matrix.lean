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
  have hij : i ≠ j := by rintro rfl; omega
  have hm : CoxeterMatrix.A (n - 1) i j = 3 := by
    simp [CoxeterMatrix.A, hij, or_comm, h]
  simpa [braidWord, ← (CoxeterMatrix.A (n - 1)).symmetric i j, hm,
    alternatingWord, mul_assoc] using (cs.prod_map_heckeLeftMatrix_braidWord s i j).symm

/-- The right regular Hecke matrices satisfy the adjacent braid relation. -/
theorem heckeRightMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    heckeRightMatrix cs s i * heckeRightMatrix cs s j * heckeRightMatrix cs s i =
      heckeRightMatrix cs s j * heckeRightMatrix cs s i * heckeRightMatrix cs s j := by
  classical
  have hij : i ≠ j := by rintro rfl; omega
  have hm : CoxeterMatrix.A (n - 1) i j = 3 := by
    simp [CoxeterMatrix.A, hij, or_comm, h]
  simpa [braidWord, ← (CoxeterMatrix.A (n - 1)).symmetric i j, hm,
    alternatingWord, mul_assoc] using (cs.prod_map_heckeRightMatrix_braidWord s i j).symm

/-- Distant left regular Hecke matrices commute. -/
theorem commute_heckeLeftMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (heckeLeftMatrix cs s i) (heckeLeftMatrix cs s j) := by
  classical
  have hij : i ≠ j := by rintro rfl; omega
  have hm : CoxeterMatrix.A (n - 1) i j = 2 := by
    simp only [CoxeterMatrix.A, Matrix.of_apply, ite_eq_right hij]
    split_ifs <;> omega
  simpa [commute_iff_eq, braidWord, ← (CoxeterMatrix.A (n - 1)).symmetric i j,
    hm, alternatingWord] using cs.prod_map_heckeLeftMatrix_braidWord s i j

/-- Distant right regular Hecke matrices commute. -/
theorem commute_heckeRightMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (heckeRightMatrix cs s i) (heckeRightMatrix cs s j) := by
  classical
  have hij : i ≠ j := by rintro rfl; omega
  have hm : CoxeterMatrix.A (n - 1) i j = 2 := by
    simp only [CoxeterMatrix.A, Matrix.of_apply, ite_eq_right hij]
    split_ifs <;> omega
  simpa [commute_iff_eq, braidWord, ← (CoxeterMatrix.A (n - 1)).symmetric i j,
    hm, alternatingWord] using cs.prod_map_heckeRightMatrix_braidWord s i j

end TypeARelations

end CoxeterSystem
