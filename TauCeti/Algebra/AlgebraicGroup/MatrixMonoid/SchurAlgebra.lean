/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MatrixMonoid.Homogeneous
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Schur algebras as duals of homogeneous matrix coordinates

The Schur algebra `S_R(n, d)` is the convolution dual of the degree-`d` matrix-coordinate
coalgebra. It is finite free over any commutative ring. Its basis is dual to the monomial
basis of homogeneous coordinates, and its rank is `(n²).multichoose d` over a ring with the
strong rank condition.

In degree one, evaluation on the matrix-entry coordinates identifies convolution with
ordinary matrix multiplication. This gives `S_R(n, 1) ≃ₐ[R] Matrix (Fin n) (Fin n) R`,
including `n = 0`. No semisimplicity or characteristic hypothesis is used.

This uses the existing `ConvolutionDual` and its convolution algebra, rather than introducing
a second multiplication on the linear dual.

## References

* J. A. Green, *Polynomial Representations of GLₙ*, §2, the Schur algebra `S(n, d)`.
-/

public section

open scoped TensorProduct
open MvPolynomial

namespace TauCeti

/-- The Schur algebra, dual to homogeneous matrix coordinates with convolution multiplication. -/
abbrev SchurAlgebra (R : Type*) [CommRing R] (n d : ℕ) :=
  ConvolutionDual R (MatrixMonoid.homogeneousSubcoalgebra R n d).toSubmodule

namespace SchurAlgebra

open MatrixMonoid

variable (R : Type*) [CommRing R] (n d : ℕ)

/-- The finite set of exponent vectors of the prescribed matrix-coordinate degree. -/
@[instance_reducible]
private noncomputable def monomialIndexFintype :
    Fintype {s : (Fin n × Fin n) →₀ ℕ // s.degree = d} :=
  (Finsupp.finite_of_degree_eq d).fintype

/-- The Schur basis is the basis dual to the degree-`d` matrix monomials. -/
noncomputable def basis :
    Module.Basis {s : (Fin n × Fin n) →₀ ℕ // s.degree = d} R (SchurAlgebra R n d) := by
  letI := monomialIndexFintype n d
  exact (homogeneousSubcoalgebraBasis R n d).dualBasis.map (WithConv.linearEquiv R _).symm

/-- The Schur basis pairs with matrix monomials by the Kronecker delta. -/
@[simp]
theorem basis_apply (s t : {s : (Fin n × Fin n) →₀ ℕ // s.degree = d}) :
    basis R n d s (homogeneousSubcoalgebraBasis R n d t) = if t = s then 1 else 0 := by
  classical
  let := monomialIndexFintype n d
  exact Module.Basis.dualBasis_apply_self _ s t

/-- Schur-basis coordinates are evaluations on the corresponding matrix monomials. -/
@[simp]
theorem basis_repr_apply (f : SchurAlgebra R n d)
    (s : {s : (Fin n × Fin n) →₀ ℕ // s.degree = d}) :
    (basis R n d).repr f s = f (homogeneousSubcoalgebraBasis R n d s) := by
  let := monomialIndexFintype n d
  simp [basis]

instance : Module.Free R (SchurAlgebra R n d) := Module.Free.of_basis (basis R n d)

/-- The rank of the Schur algebra equals the number of degree-`d` matrix monomials. -/
@[simp]
theorem finrank [StrongRankCondition R] :
    Module.finrank R (SchurAlgebra R n d) = (n * n).multichoose d := by
  let := monomialIndexFintype n d
  rw [Module.finrank_eq_nat_card_basis (basis R n d),
    ← Module.finrank_eq_nat_card_basis (homogeneousSubcoalgebraBasis R n d)]
  exact finrank_homogeneousSubcoalgebra R n d

private theorem mul_homogeneousEntry (f g : SchurAlgebra R n 1) (i j : Fin n) :
    (f * g) (homogeneousEntry R n i j) =
      ∑ k, f (homogeneousEntry R n i k) * g (homogeneousEntry R n k j) := by
  rw [LinearMap.convMul_apply, comul_homogeneousEntry]
  simp

/-- Evaluating on degree-one matrix coordinates defines an algebra map to square matrices. -/
private noncomputable def toMatrix : SchurAlgebra R n 1 →ₐ[R] Matrix (Fin n) (Fin n) R where
  toFun f i j := f (homogeneousEntry R n i j)
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_mul' f g := by ext i j; exact mul_homogeneousEntry R n f g i j
  map_zero' := by ext i j; rfl
  map_add' f g := by ext i j; rfl
  commutes' r := by ext i j; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

/-- The matrix comparison evaluates a functional on the indicated matrix-entry coordinate. -/
@[simp]
private theorem toMatrix_apply (f : SchurAlgebra R n 1) (i j : Fin n) :
    toMatrix R n f i j = f (homogeneousEntry R n i j) := (rfl)

private theorem toMatrix_injective : Function.Injective (toMatrix R n) := by
  intro f g h
  apply WithConv.ext
  apply (homogeneousSubcoalgebraBasis R n 1).ext
  intro s
  obtain ⟨⟨i, j⟩, hs⟩ : ∃ ij, Finsupp.single ij 1 = s.1 := by
    exact (Set.ext_iff.mp Finsupp.range_single_one s.1).mpr s.2
  have hb : homogeneousSubcoalgebraBasis R n 1 s = homogeneousEntry R n i j := by
    apply Subtype.ext
    simp [← hs, ← MvPolynomial.X_pow_eq_monomial]
  rw [hb]
  exact congrArg (fun A : Matrix (Fin n) (Fin n) R ↦ A i j) h

private theorem toMatrix_surjective : Function.Surjective (toMatrix R n) := by
  classical
  intro A
  let e := (coordinateBialgebraAlgEquiv R n).symm.toLinearMap.comp
    (homogeneousSubcoalgebra R n 1).toSubmodule.subtype
  refine ⟨WithConv.toConv (∑ ij : Fin n × Fin n,
    A ij.1 ij.2 • (MvPolynomial.lcoeff R (Finsupp.single ij 1)).comp e), ?_⟩
  ext i j
  simp [toMatrix_apply, e, coeff_X, Finsupp.single_left_inj]

/-- The first Schur algebra is the full matrix algebra, with its usual multiplication. -/
noncomputable def equivMatrix : SchurAlgebra R n 1 ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
  AlgEquiv.ofBijective (toMatrix R n) ⟨toMatrix_injective R n, toMatrix_surjective R n⟩

/-- The degree-one Schur comparison evaluates on matrix-entry coordinates. -/
@[simp]
theorem equivMatrix_apply (f : SchurAlgebra R n 1) (i j : Fin n) :
    equivMatrix R n f i j = f (homogeneousEntry R n i j) := (rfl)

/-- The inverse comparison is the unique functional with the prescribed matrix-entry values. -/
@[simp]
theorem equivMatrix_symm_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (equivMatrix R n).symm A (homogeneousEntry R n i j) = A i j :=
  congrArg (fun B : Matrix (Fin n) (Fin n) R ↦ B i j)
    ((equivMatrix R n).apply_symm_apply A)

end SchurAlgebra
end TauCeti
