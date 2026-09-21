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
# The Steinberg relation for quaternion algebras

For any `a` in a commutative ring, this file constructs the Steinberg matrix representation.
When `2`, `a`, and `1 - a` are invertible, it gives the explicit splitting

`ℍ[K, a, 1 - a] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K`.

The construction sends the standard quaternion generators to

`!![0, a; 1, 0]` and `!![1, -a; 1, -1]`.

These matrices square to `a` and `1 - a`, respectively, and anticommute. This is the usual
matrix proof of the Steinberg relation for quaternion symbols; see Lam, *Introduction to
Quadratic Forms over Fields*, Chapter III, Section 2.

## Main definitions

* `TauCeti.QuaternionAlgebra.steinbergToMatrix`: the representation, including degenerate
  parameters.
* `TauCeti.QuaternionAlgebra.steinbergEquivMatrix`: the splitting equivalence.
-/

public section

namespace TauCeti

namespace QuaternionAlgebra

open scoped Quaternion

variable {K : Type*} [CommRing K]

/-- The matrices used in the standard proof of the Steinberg relation form a quaternion basis. -/
private def steinbergBasis (a : K) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K) a 0 (1 - a) where
  i := !![0, a; 1, 0]
  j := !![1, -a; 1, -1]
  k := !![a, -a; 1, -a]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The Steinberg matrix representation, defined for every parameter over a commutative ring. -/
def steinbergToMatrix (a : K) :
    ℍ[K,a,0,1 - a] →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  (steinbergBasis a).liftHom

/-- The entrywise formula for the Steinberg matrix representation. -/
theorem steinbergToMatrix_apply (a : K) (q : ℍ[K,a,0,1 - a]) :
    steinbergToMatrix a q =
      !![q.re + q.imJ + a * q.imK, a * (q.imI - q.imJ - q.imK);
        q.imI + q.imJ + q.imK, q.re - q.imJ - a * q.imK] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [steinbergToMatrix, steinbergBasis, _root_.QuaternionAlgebra.Basis.lift,
      Algebra.algebraMap_eq_smul_one] <;> ring

/-- The first quaternion generator maps to the standard Steinberg matrix. -/
@[simp]
theorem steinbergToMatrix_i (a : K) :
    steinbergToMatrix a { re := 0, imI := 1, imJ := 0, imK := 0 } = !![0, a; 1, 0] := by
  rw [steinbergToMatrix_apply]
  simp

/-- The second quaternion generator maps to the standard Steinberg matrix. -/
@[simp]
theorem steinbergToMatrix_j (a : K) :
    steinbergToMatrix a { re := 0, imI := 0, imJ := 1, imK := 0 } = !![1, -a; 1, -1] := by
  rw [steinbergToMatrix_apply]
  simp

variable [Invertible (2 : K)] (a : K) [Invertible a] [Invertible (1 - a)]

/-- An explicit inverse function for `steinbergToMatrix`. -/
private def steinbergPreimage (M : Matrix (Fin 2) (Fin 2) K) : ℍ[K,a,0,1 - a] :=
  let r := ⅟(2 : K) * (M 0 0 + M 1 1)
  let x := ⅟(2 : K) * (⅟a * M 0 1 + M 1 0)
  let s := M 1 0 - x
  let z := ⅟(1 - a) * (s - (M 0 0 - r))
  ⟨r, x, s - z, z⟩

private theorem steinbergToMatrix_preimage (M : Matrix (Fin 2) (Fin 2) K) :
    steinbergToMatrix a (steinbergPreimage a M) = M := by
  rw [steinbergToMatrix_apply]
  have h2 := invOf_mul_self (2 : K)
  have ha := invOf_mul_self a
  have hb := invOf_mul_self (1 - a)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [steinbergPreimage] <;> grind

private theorem steinbergPreimage_toMatrix (q : ℍ[K,a,0,1 - a]) :
    steinbergPreimage a (steinbergToMatrix a q) = q := by
  rw [steinbergToMatrix_apply]
  have h2 := invOf_mul_self (2 : K)
  have ha := invOf_mul_self a
  have hb := invOf_mul_self (1 - a)
  ext <;> simp [steinbergPreimage] <;> grind

/-- **The Steinberg relation for quaternion algebras.** If `2`, `a`, and `1 - a` are
invertible in a commutative ring, the quaternion algebra with symbol `(a, 1 - a)` is split.

The forward map sends the standard generators `i` and `j` to `!![0, a; 1, 0]` and
`!![1, -a; 1, -1]`, respectively. -/
def steinbergEquivMatrix : ℍ[K,a,0,1 - a] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  { steinbergToMatrix a with
    invFun := steinbergPreimage a
    left_inv := steinbergPreimage_toMatrix a
    right_inv := steinbergToMatrix_preimage a }

/-- The Steinberg equivalence has the Steinberg representation as its underlying homomorphism. -/
@[simp]
theorem steinbergEquivMatrix_toAlgHom :
    (steinbergEquivMatrix a).toAlgHom = steinbergToMatrix a := by
  rfl

/-- The entrywise formula for the forward direction of the Steinberg equivalence. -/
theorem steinbergEquivMatrix_apply (q : ℍ[K,a,0,1 - a]) :
    steinbergEquivMatrix a q =
      !![q.re + q.imJ + a * q.imK, a * (q.imI - q.imJ - q.imK);
        q.imI + q.imJ + q.imK, q.re - q.imJ - a * q.imK] :=
  steinbergToMatrix_apply a q

/-- The entrywise formula for the inverse of the Steinberg equivalence. -/
@[simp]
theorem steinbergEquivMatrix_symm_apply (M : Matrix (Fin 2) (Fin 2) K) :
    (steinbergEquivMatrix a).symm M =
      let r := ⅟(2 : K) * (M 0 0 + M 1 1)
      let x := ⅟(2 : K) * (⅟a * M 0 1 + M 1 0)
      let s := M 1 0 - x
      let z := ⅟(1 - a) * (s - (M 0 0 - r))
      ⟨r, x, s - z, z⟩ := by
  rfl

/-- The first quaternion generator maps to the standard Steinberg matrix. -/
@[simp]
theorem steinbergEquivMatrix_i :
    steinbergEquivMatrix a
        { re := 0, imI := 1, imJ := 0, imK := 0 } = !![0, a; 1, 0] := by
  rw [steinbergEquivMatrix_apply]
  simp

/-- The second quaternion generator maps to the standard Steinberg matrix. -/
@[simp]
theorem steinbergEquivMatrix_j :
    steinbergEquivMatrix a
        { re := 0, imI := 0, imJ := 1, imK := 0 } = !![1, -a; 1, -1] := by
  rw [steinbergEquivMatrix_apply]
  simp

end QuaternionAlgebra

end TauCeti
