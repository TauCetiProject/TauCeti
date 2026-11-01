/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Positivity

/-!
# The positive-form adjoint as a matrix adjoint

Let `Q` be a real quadratic form with a real orthonormal basis `b`, that is, an orthogonal basis
with `Q (b i) = 1` for every `i`, as for the sum of squares on `ℝⁿ`. The complexified Clifford
algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` has the ordered-product basis `e_s` of the base-changed basis
`1 ⊗ b`, and its positive-form trace pairing `τ(a† * y)`, where

  `a† = complexConj (reverse a)`

is complex conjugation of the coefficients after reversal, is the Hermitian inner product for
which the `e_s` are orthonormal (`CliffordAlgebra.scalarTrace_complexConj_reverse_mul`). Since
`†` is an anti-automorphism, left multiplication by `a†` is the adjoint of left multiplication by
`a` for this inner product, so in the basis `e_s` the matrix of `y ↦ a† * y` is the conjugate
transpose of the matrix of `y ↦ a * y`. Thus `†` is the adjoint of the faithful left regular
representation of the Clifford algebra on itself, with its orthonormal monomial basis.

On the Spin group of `Q_ℂ` the adjoint is the inverse of the complex conjugate,
`g† = (conj g)⁻¹` (`CliffordAlgebra.complexConj_reverse_eq_coe_inv`, in
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Complexification`). Together with the positivity of
`g† * g` proved here, this is the algebraic input for the polar decomposition
`g = (g (g† g)^(-1/2)) (g† g)^(1/2)` of complex Spin elements.

## Main results

* `CliffordAlgebra.basis_repr_eq_scalarTrace_complexConj_reverse_mul` and
  `CliffordAlgebra.scalarTrace_complexConj_reverse_mul_basis`: the coordinates in an orthonormal
  basis are trace pairings against the basis elements.
* `CliffordAlgebra.toMatrix_mulLeft_complexConj_reverse`: the matrix of left multiplication by
  `complexConj (reverse a)` is the conjugate transpose of the matrix of left multiplication by `a`.
* `CliffordAlgebra.posDef_toMatrix_mulLeft_complexConj_reverse_mul_self`: for a unit `g`, the
  matrix of left multiplication by `complexConj (reverse g) * g` is positive definite.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

open scoped ComplexConjugate ComplexOrder Matrix

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-! ### The adjoint of left multiplication in an orthonormal basis -/

section Basis

variable {I : Type*} [LinearOrder I] {b : Module.Basis I ℝ V}

/-- In the ordered-product Clifford basis of a real orthonormal basis, the coordinate at `s` of
`y` is the positive-form trace pairing `τ(e_s† * y)` of `y` against the basis element `e_s`. -/
theorem basis_repr_eq_scalarTrace_complexConj_reverse_mul
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
    (y : CliffordAlgebra (Q.baseChange ℂ)) (s : Finset I) :
    (basis (Q.baseChange ℂ) (b.baseChange ℂ)).repr y s =
      scalarTrace (Q.baseChange ℂ)
        (complexConj Q (reverse (basis (Q.baseChange ℂ) (b.baseChange ℂ) s)) * y) := by
  rw [scalarTrace_complexConj_reverse_mul hb, Module.Basis.repr_self,
    Finsupp.sum_single_index (by simp)]
  simp [hQ]

/-- In the ordered-product Clifford basis of a real orthonormal basis, the positive-form trace
pairing `τ(x† * e_t)` of `x` against the basis element `e_t` is the complex conjugate of the
coordinate of `x` at `t`. -/
theorem scalarTrace_complexConj_reverse_mul_basis
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
    (x : CliffordAlgebra (Q.baseChange ℂ)) (t : Finset I) :
    scalarTrace (Q.baseChange ℂ)
        (complexConj Q (reverse x) * basis (Q.baseChange ℂ) (b.baseChange ℂ) t) =
      conj ((basis (Q.baseChange ℂ) (b.baseChange ℂ)).repr x t) := by
  rw [scalarTrace_complexConj_reverse_mul hb, Module.Basis.repr_self]
  simp +contextual [hQ, Finsupp.single_apply]

/-- **The positive-form adjoint is the matrix adjoint.** In the ordered-product Clifford basis of
a real orthonormal basis, the matrix of left multiplication by `complexConj (reverse a)` is the
conjugate transpose of the matrix of left multiplication by `a`. -/
theorem toMatrix_mulLeft_complexConj_reverse [Fintype I]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    LinearMap.toMatrix (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (LinearMap.mulLeft ℂ (complexConj Q (reverse a))) =
      (LinearMap.toMatrix (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (basis (Q.baseChange ℂ) (b.baseChange ℂ)) (LinearMap.mulLeft ℂ a))ᴴ := by
  ext s t
  simp only [LinearMap.toMatrix_apply, Matrix.conjTranspose_apply, LinearMap.mulLeft_apply,
    Complex.star_def]
  rw [basis_repr_eq_scalarTrace_complexConj_reverse_mul hb hQ,
    ← scalarTrace_complexConj_reverse_mul_basis hb hQ]
  simp [mul_assoc]

/-- **The positive-form norm of a unit is positive definite.** In the ordered-product Clifford basis
of a real orthonormal basis, left multiplication by `complexConj (reverse g) * g` has the positive
definite matrix `Mᴴ * M`, where `M` is the invertible matrix of left multiplication by the unit
`g`. -/
theorem posDef_toMatrix_mulLeft_complexConj_reverse_mul_self [Fintype I]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1)
    {g : CliffordAlgebra (Q.baseChange ℂ)} (hg : IsUnit g) :
    Matrix.PosDef (LinearMap.toMatrix (basis (Q.baseChange ℂ) (b.baseChange ℂ))
      (basis (Q.baseChange ℂ) (b.baseChange ℂ))
      (LinearMap.mulLeft ℂ (complexConj Q (reverse g) * g))) := by
  rw [LinearMap.mulLeft_mul, LinearMap.toMatrix_comp _ (basis (Q.baseChange ℂ) (b.baseChange ℂ)),
    toMatrix_mulLeft_complexConj_reverse hb hQ]
  exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit
    ((LinearMap.isUnit_toMatrix_iff _).2 (Algebra.lmul_isUnit_iff.2 hg)))

end Basis

end CliffordAlgebra
