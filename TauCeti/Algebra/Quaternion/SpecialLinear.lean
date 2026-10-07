/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

import TauCeti.Algebra.Quaternion.SplittingCriterion

/-!
# Split quaternion unitary groups

The norm-one group of a split quaternion algebra is the two-dimensional special linear group.
This file constructs the identification from an arbitrary algebra equivalence with a two-by-two
matrix algebra.

The key compatibility is intrinsic: quaternion conjugation is anti-multiplicative and the sum of
a quaternion and its conjugate is scalar. Transported to two-by-two matrices, those two properties
characterize matrix adjugation. Consequently, the quaternion unitary equation becomes
`adjugate A * A = 1`, which is equivalent to `det A = 1`.

Over a separably closed field of characteristic different from two, every quaternion algebra with
unit symbol parameters splits, so its unitary group is noncanonically isomorphic to `SL₂`.

## Main results

* `QuaternionAlgebra.map_star_eq_adjugate_of_algEquiv_matrix` shows that any splitting algebra
  equivalence carries quaternion conjugation to matrix adjugation.
* `QuaternionAlgebra.unitaryEquivSpecialLinearOfAlgEquiv` restricts a splitting equivalence to an
  equivalence from the quaternion unitary group to `SL₂`.
* `QuaternionAlgebra.nonempty_unitaryEquivSpecialLinear_of_isSepClosed` supplies such an
  equivalence over a separably closed field.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2.
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §1.1.
-/

public section

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

/-- Any algebra equivalence from a quaternion algebra to two-by-two matrices carries quaternion
conjugation to matrix adjugation. -/
theorem map_star_eq_adjugate_of_algEquiv_matrix {a b : R}
    (e : ℍ[R,a,0,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (q : ℍ[R,a,0,b]) :
    e (star q) = Matrix.adjugate (e q) := by
  let f : Matrix (Fin 2) (Fin 2) R → Matrix (Fin 2) (Fin 2) R :=
    fun A ↦ e (star (e.symm A))
  have hmul (A B : Matrix (Fin 2) (Fin 2) R) : f (A * B) = f B * f A := by
    simp only [f, map_mul, star_mul]
  have hscalar (A : Matrix (Fin 2) (Fin 2) R) : ∃ r : R, A + f A = r • 1 := by
    refine ⟨2 * (e.symm A).re, ?_⟩
    dsimp only [f]
    calc
      A + e (star (e.symm A)) = e (e.symm A) + e (star (e.symm A)) := by
        rw [e.apply_symm_apply]
      _ = e (e.symm A + star (e.symm A)) := (map_add e _ _).symm
      _ = (2 * (e.symm A).re) • 1 := by
        rw [self_add_star]
        have hscalarQuat :
            (2 * ((e.symm A).re : ℍ[R,a,0,b]) +
                (0 : R) * ((e.symm A).imI : ℍ[R,a,0,b])) =
              algebraMap R ℍ[R,a,0,b] (2 * (e.symm A).re) := by
          ext <;> simp
        rw [hscalarQuat]
        simpa only [Algebra.algebraMap_eq_smul_one] using
          e.commutes (2 * (e.symm A).re)
  simpa only [f, e.symm_apply_apply] using
    Matrix.eq_adjugate_of_antimultiplicative_of_exists_add_eq_smul_one f hmul hscalar (e q)

/-- A splitting algebra equivalence restricts to an equivalence from the quaternion norm-one group
to the two-dimensional special linear group. -/
noncomputable def unitaryEquivSpecialLinearOfAlgEquiv {a b : R}
    (e : ℍ[R,a,0,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) :
    unitary ℍ[R,a,0,b] ≃* Matrix.SpecialLinearGroup (Fin 2) R := by
  let f : unitary ℍ[R,a,0,b] →* Matrix.SpecialLinearGroup (Fin 2) R :=
    { toFun := fun q ↦
        ⟨e q, (Matrix.adjugate_mul_self_eq_one_iff_det_eq_one (e q)).mp <| by
          rw [← map_star_eq_adjugate_of_algEquiv_matrix e, ← map_mul]
          simpa only [map_one] using congrArg e (Unitary.mem_iff.mp q.2).1⟩
      map_one' := by
        apply Subtype.ext
        exact map_one e
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        exact map_mul e (x : ℍ[R,a,0,b]) (y : ℍ[R,a,0,b]) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  · intro A
    let q : ℍ[R,a,0,b] := e.symm A
    have hstar : e (star q) = Matrix.adjugate A := by
      rw [map_star_eq_adjugate_of_algEquiv_matrix, e.apply_symm_apply]
    have hunitary : q ∈ unitary ℍ[R,a,0,b] := (Unitary.mem_iff).mpr ⟨by
        apply e.injective
        rw [map_mul, hstar, e.apply_symm_apply, map_one,
          Matrix.adjugate_mul, A.det_coe, one_smul], by
        apply e.injective
        rw [map_mul, hstar, e.apply_symm_apply, map_one,
          Matrix.mul_adjugate, A.det_coe, one_smul]⟩
    refine ⟨⟨q, hunitary⟩, ?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply A

/-- The quaternion-to-`SL₂` equivalence evaluates the chosen splitting algebra equivalence. -/
@[simp]
theorem coe_unitaryEquivSpecialLinearOfAlgEquiv_apply {a b : R}
    (e : ℍ[R,a,0,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (q : unitary ℍ[R,a,0,b]) :
    ((unitaryEquivSpecialLinearOfAlgEquiv e q : Matrix.SpecialLinearGroup (Fin 2) R) :
      Matrix (Fin 2) (Fin 2) R) = e q := by
  rfl

/-- The inverse quaternion-to-`SL₂` equivalence evaluates the inverse splitting algebra
equivalence. -/
@[simp]
theorem coe_unitaryEquivSpecialLinearOfAlgEquiv_symm_apply {a b : R}
    (e : ℍ[R,a,0,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
    (A : Matrix.SpecialLinearGroup (Fin 2) R) :
    ((unitaryEquivSpecialLinearOfAlgEquiv e).symm A : ℍ[R,a,0,b]) = e.symm A := by
  apply e.injective
  rw [← coe_unitaryEquivSpecialLinearOfAlgEquiv_apply, e.apply_symm_apply]
  exact congrArg Subtype.val
    ((unitaryEquivSpecialLinearOfAlgEquiv e).apply_symm_apply A)

variable {K : Type*} [Field K]

/-- Over a separably closed field of characteristic different from two, the norm-one group of a
quaternion algebra with unit symbol parameters is noncanonically isomorphic to `SL₂`. -/
theorem nonempty_unitaryEquivSpecialLinear_of_isSepClosed
    [NeZero (2 : K)] [IsSepClosed K] (a b : Kˣ) :
    Nonempty (unitary ℍ[K,(a : K),0,(b : K)] ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨s, hs⟩ := IsSepClosed.exists_eq_mul_self (a : K)
  have ha : IsSquare (a : K) := ⟨s, by simpa [pow_two] using hs⟩
  obtain ⟨e⟩ :=
    (TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq a b).mpr
      (TauCeti.exists_eq_sq_sub_mul_sq_of_isSquare ha a.isUnit (b : K))
  exact ⟨unitaryEquivSpecialLinearOfAlgEquiv e⟩

end QuaternionAlgebra

end
