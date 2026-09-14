/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# A split quaternion algebra

This file gives an explicit splitting of the quaternion algebra `ℍ[R,a,-a]` when `a` is a
unit.  The generators act on a free module of rank two by

```text
i ↦ (0  a)       j ↦ (0  -a)
    (1  0)           (1   0).
```

Their squares are respectively `a` and `-a`, and they anticommute.  These matrices therefore
define a homomorphism from the quaternion algebra to `2 × 2` matrices.  Explicit coordinate
formulas show that this homomorphism is bijective when `a` is a unit.

The resulting algebra equivalence is one of the standard symbol relations for quaternion
algebras.  It is useful for reducing identities involving the symbol `(a, -a)` to computations
in a matrix algebra.

The main result is `TauCeti.QuaternionAlgebra.splitANegAEquiv`. Its coordinate formula and its
values on the three quaternion generators are provided without exposing the construction.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, §2.11.
-/

public section

noncomputable section

open scoped Matrix Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

/-- The standard quaternion basis of `2 × 2` matrices with parameters `a` and `-a`. -/
private def splitANegABasis (a : R) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) a 0 (-a) where
  i := !![0, a; 1, 0]
  j := !![0, -a; 1, 0]
  k := !![a, 0; 0, -a]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp

/-- The algebra homomorphism from `ℍ[R,a,-a]` to `2 × 2` matrices determined by the
standard split matrices. -/
private def splitANegAAlgHom (a : R) : ℍ[R,a,-a] →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (splitANegABasis a).liftHom

/-- The entries of the standard matrix representation of `ℍ[R,a,-a]`. -/
private theorem splitANegAAlgHom_apply (a : R) (x : ℍ[R,a,-a]) :
    splitANegAAlgHom a x =
      !![x.re + a * x.imK, a * (x.imI - x.imJ);
         x.imI + x.imJ, x.re - a * x.imK] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitANegAAlgHom, splitANegABasis, _root_.QuaternionAlgebra.Basis.liftHom,
      _root_.QuaternionAlgebra.Basis.lift, Matrix.algebraMap_matrix_apply] <;> ring

variable [Invertible (2 : R)]

/-- The coordinate inverse to the standard matrix representation. -/
private def splitANegAPreimage (a : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    ℍ[R,(a : R),-(a : R)] :=
  ⟨⅟ (2 : R) * (M 0 0 + M 1 1),
    ⅟ (2 : R) * (M 1 0 + (↑(a⁻¹) : R) * M 0 1),
    ⅟ (2 : R) * (M 1 0 - (↑(a⁻¹) : R) * M 0 1),
    ⅟ (2 : R) * ((↑(a⁻¹) : R) * (M 0 0 - M 1 1))⟩

private theorem splitANegAPreimage_apply_splitANegAAlgHom (a : Rˣ)
    (x : ℍ[R,(a : R),-(a : R)]) :
    splitANegAPreimage a (splitANegAAlgHom (a : R) x) = x := by
  have htwo (z : R) : ⅟ (2 : R) * z * 2 = z := by
    calc
      ⅟ (2 : R) * z * 2 = (⅟ (2 : R) * 2) * z := by ring
      _ = z := by rw [invOf_mul_self, one_mul]
  ext <;> simp [splitANegAPreimage, splitANegAAlgHom_apply] <;>
    ring_nf <;> simp [htwo]

private theorem splitANegAAlgHom_apply_splitANegAPreimage (a : Rˣ)
    (M : Matrix (Fin 2) (Fin 2) R) :
    splitANegAAlgHom (a : R) (splitANegAPreimage a M) = M := by
  have hunit (z : R) : (a : R) * z * (↑(a⁻¹) : R) = z := by
    calc
      (a : R) * z * (↑(a⁻¹) : R) = ((a : R) * (↑(a⁻¹) : R)) * z := by ring
      _ = z := by rw [a.mul_inv, one_mul]
  have htwo (z : R) : ⅟ (2 : R) * z * 2 = z := by
    calc
      ⅟ (2 : R) * z * 2 = (⅟ (2 : R) * 2) * z := by ring
      _ = z := by rw [invOf_mul_self, one_mul]
  have hhalf (z : R) : ⅟ (2 : R) * z + ⅟ (2 : R) * z = z := by
    calc
      ⅟ (2 : R) * z + ⅟ (2 : R) * z = (⅟ (2 : R) + ⅟ (2 : R)) * z := by ring
      _ = z := by rw [invOf_two_add_invOf_two, one_mul]
  rw [splitANegAAlgHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitANegAPreimage] <;> ring_nf <;> simp [hunit, htwo, hhalf]

/-- The explicit splitting `ℍ[R,a,-a] ≃ₐ[R] M₂(R)` for a unit `a`, over a commutative
ring in which `2` is invertible. -/
def splitANegAEquiv (a : Rˣ) :
    ℍ[R,(a : R),-(a : R)] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofBijective (splitANegAAlgHom (a : R)) ⟨
    Function.LeftInverse.injective (splitANegAPreimage_apply_splitANegAAlgHom a),
    Function.RightInverse.surjective (splitANegAAlgHom_apply_splitANegAPreimage a)⟩

/-- The splitting equivalence is the standard matrix representation. -/
theorem splitANegAEquiv_apply (a : Rˣ) (x : ℍ[R,(a : R),-(a : R)]) :
    splitANegAEquiv a x =
      !![x.re + (a : R) * x.imK, (a : R) * (x.imI - x.imJ);
         x.imI + x.imJ, x.re - (a : R) * x.imK] := by
  exact (AlgEquiv.ofBijective_apply _ _ x).trans (splitANegAAlgHom_apply (a : R) x)

/-- The inverse of the splitting equivalence, in matrix coordinates. -/
theorem splitANegAEquiv_symm_apply (a : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (splitANegAEquiv a).symm M =
      ⟨⅟ (2 : R) * (M 0 0 + M 1 1),
        ⅟ (2 : R) * (M 1 0 + (↑(a⁻¹) : R) * M 0 1),
        ⅟ (2 : R) * (M 1 0 - (↑(a⁻¹) : R) * M 0 1),
        ⅟ (2 : R) * ((↑(a⁻¹) : R) * (M 0 0 - M 1 1))⟩ := by
  apply (splitANegAEquiv a).symm_apply_eq.mpr
  exact ((AlgEquiv.ofBijective_apply _ _ _).trans
    (splitANegAAlgHom_apply_splitANegAPreimage a M)).symm

/-- The first quaternion generator maps to `!![0, a; 1, 0]`. -/
@[simp]
theorem splitANegAEquiv_apply_i (a : Rˣ) :
    splitANegAEquiv a ⟨0, 1, 0, 0⟩ = !![0, (a : R); 1, 0] := by
  rw [splitANegAEquiv_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The second quaternion generator maps to `!![0, -a; 1, 0]`. -/
@[simp]
theorem splitANegAEquiv_apply_j (a : Rˣ) :
    splitANegAEquiv a ⟨0, 0, 1, 0⟩ = !![0, -(a : R); 1, 0] := by
  rw [splitANegAEquiv_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The product of the two quaternion generators maps to `!![a, 0; 0, -a]`. -/
@[simp]
theorem splitANegAEquiv_apply_k (a : Rˣ) :
    splitANegAEquiv a ⟨0, 0, 0, 1⟩ = !![(a : R), 0; 0, -(a : R)] := by
  rw [splitANegAEquiv_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end QuaternionAlgebra

end TauCeti
