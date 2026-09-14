/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# The Steinberg relation for quaternion algebras

For a nonzero `a` in a field such that `1 - a` is also nonzero, this file constructs the explicit
splitting

`ℍ[K, a, 1 - a] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K`.

The construction sends the standard quaternion generators to

`!![0, a; 1, 0]` and `!![1, -a; 1, -1]`.

These matrices square to `a` and `1 - a`, respectively, and anticommute. This is the usual
matrix proof of the Steinberg relation for quaternion symbols; see Lam, *Introduction to
Quadratic Forms over Fields*, Chapter III, Section 2.

## Main definition

* `TauCeti.QuaternionAlgebra.steinbergEquivMatrix`: the splitting equivalence.
-/

public section

namespace TauCeti

namespace QuaternionAlgebra

open scoped Quaternion

variable {K : Type*} [Field K]

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

/-- The algebra homomorphism underlying the Steinberg equivalence. -/
private def steinbergToMatrix (a : K) :
    ℍ[K,a,0,1 - a] →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  (steinbergBasis a).liftHom

private theorem steinbergToMatrix_apply (a : K) (q : ℍ[K,a,0,1 - a]) :
    steinbergToMatrix a q =
      !![q.re + q.imJ + a * q.imK, a * (q.imI - q.imJ - q.imK);
        q.imI + q.imJ + q.imK, q.re - q.imJ - a * q.imK] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [steinbergToMatrix, steinbergBasis, _root_.QuaternionAlgebra.Basis.lift,
      Algebra.algebraMap_eq_smul_one] <;> ring

/-- An explicit inverse function for `steinbergToMatrix`. -/
private noncomputable def steinbergPreimage (a : Kˣ) (M : Matrix (Fin 2) (Fin 2) K) :
    ℍ[K,(a : K),0,1 - (a : K)] :=
  let r := (2 : K)⁻¹ * (M 0 0 + M 1 1)
  let x := (2 : K)⁻¹ * (((a : K)⁻¹ * M 0 1) + M 1 0)
  let s := M 1 0 - x
  let z := (1 - (a : K))⁻¹ * (s - (M 0 0 - r))
  ⟨r, x, s - z, z⟩

private theorem steinbergToMatrix_preimage [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) K) :
    steinbergToMatrix (a : K) (steinbergPreimage a M) = M := by
  rw [steinbergToMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [steinbergPreimage]
  all_goals
    field_simp [Invertible.ne_zero (2 : K), a.ne_zero, ha]
    ring

private theorem steinbergToMatrix_bijective [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0) :
    Function.Bijective (steinbergToMatrix (a : K)) := by
  have hsurj : Function.Surjective (steinbergToMatrix (a : K)) :=
    fun M ↦ ⟨steinbergPreimage a M, steinbergToMatrix_preimage a ha M⟩
  have hrank : Module.finrank K ℍ[K,(a : K),0,1 - (a : K)] =
      Module.finrank K (Matrix (Fin 2) (Fin 2) K) := by
    rw [_root_.QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]
    simp
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (steinbergToMatrix (a : K)).toLinearMap) hrank).2 hsurj, hsurj⟩

/-- **The Steinberg relation for quaternion algebras.** If `a` and `1 - a` are nonzero in a
field in which `2` is invertible, then the quaternion algebra with symbol `(a, 1 - a)` is split.

The forward map sends the standard generators `i` and `j` to `!![0, a; 1, 0]` and
`!![1, -a; 1, -1]`, respectively. -/
noncomputable def steinbergEquivMatrix [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0) :
    ℍ[K,(a : K),0,1 - (a : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  AlgEquiv.ofBijective (steinbergToMatrix (a : K)) (steinbergToMatrix_bijective a ha)

/-- The entrywise formula for the forward direction of the Steinberg equivalence. -/
@[simp]
theorem steinbergEquivMatrix_apply [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0)
    (q : ℍ[K,(a : K),0,1 - (a : K)]) :
    steinbergEquivMatrix a ha q =
      !![q.re + q.imJ + (a : K) * q.imK, (a : K) * (q.imI - q.imJ - q.imK);
        q.imI + q.imJ + q.imK, q.re - q.imJ - (a : K) * q.imK] := by
  change steinbergToMatrix (a : K) q = _
  exact steinbergToMatrix_apply (a : K) q

/-- The entrywise formula for the inverse of the Steinberg equivalence. -/
@[simp]
theorem steinbergEquivMatrix_symm_apply [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) K) :
    (steinbergEquivMatrix a ha).symm M =
      let r := (2 : K)⁻¹ * (M 0 0 + M 1 1)
      let x := (2 : K)⁻¹ * (((a : K)⁻¹ * M 0 1) + M 1 0)
      let s := M 1 0 - x
      let z := (1 - (a : K))⁻¹ * (s - (M 0 0 - r))
      ⟨r, x, s - z, z⟩ := by
  change (steinbergEquivMatrix a ha).symm M = steinbergPreimage a M
  apply (steinbergEquivMatrix a ha).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (steinbergToMatrix_preimage a ha M).symm

/-- The first quaternion generator maps to the standard Steinberg matrix. -/
@[simp]
theorem steinbergEquivMatrix_i [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0) :
    steinbergEquivMatrix a ha
        (_root_.QuaternionAlgebra.Basis.self K).i = !![0, (a : K); 1, 0] := by
  rw [steinbergEquivMatrix_apply]
  simp

/-- The second quaternion generator maps to the standard Steinberg matrix. -/
@[simp]
theorem steinbergEquivMatrix_j [Invertible (2 : K)] (a : Kˣ)
    (ha : 1 - (a : K) ≠ 0) :
    steinbergEquivMatrix a ha
        (_root_.QuaternionAlgebra.Basis.self K).j = !![1, -(a : K); 1, -1] := by
  rw [steinbergEquivMatrix_apply]
  simp

end QuaternionAlgebra

end TauCeti
