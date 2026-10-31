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

For a finite type `ι`, the Schur algebra `S_R(ι, d)` is the convolution dual of the degree-`d`
coalgebra of coordinates on matrices indexed by `ι`. It is finite free over any commutative
ring. Its basis is dual to the monomial basis of homogeneous coordinates, and its rank is
`(|ι|²).multichoose d` over a ring with the strong rank condition. Green's `S(n, d)` is the case
`ι = Fin n`.

In degree one, evaluation on the matrix-entry coordinates identifies convolution with
ordinary matrix multiplication. This gives `S_R(ι, 1) ≃ₐ[R] Matrix ι ι R`,
including empty `ι`. No semisimplicity or characteristic hypothesis is used.

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
abbrev SchurAlgebra (R : Type*) [CommRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ) :=
  ConvolutionDual R (MatrixMonoid.homogeneousSubcoalgebra R ι d).toSubmodule

namespace SchurAlgebra

open MatrixMonoid

variable (R : Type*) [CommRing R] (ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ)

omit [DecidableEq ι] in
/-- The finite set of exponent vectors of the prescribed matrix-coordinate degree. -/
@[instance_reducible]
private noncomputable def monomialIndexFintype :
    Fintype {s : (ι × ι) →₀ ℕ // s.degree = d} :=
  (Finsupp.finite_of_degree_eq d).fintype

/-- The Schur basis is the basis dual to the degree-`d` matrix monomials. -/
noncomputable def basis :
    Module.Basis {s : (ι × ι) →₀ ℕ // s.degree = d} R (SchurAlgebra R ι d) := by
  letI := monomialIndexFintype ι d
  exact (homogeneousSubcoalgebraBasis R ι d).dualBasis.map (WithConv.linearEquiv R _).symm

/-- The Schur basis pairs with matrix monomials by the Kronecker delta. -/
@[simp]
theorem basis_apply (s t : {s : (ι × ι) →₀ ℕ // s.degree = d}) :
    basis R ι d s (homogeneousSubcoalgebraBasis R ι d t) = if t = s then 1 else 0 := by
  classical
  let := monomialIndexFintype ι d
  exact Module.Basis.dualBasis_apply_self _ s t

/-- Schur-basis coordinates are evaluations on the corresponding matrix monomials. -/
@[simp]
theorem basis_repr_apply (f : SchurAlgebra R ι d)
    (s : {s : (ι × ι) →₀ ℕ // s.degree = d}) :
    (basis R ι d).repr f s = f (homogeneousSubcoalgebraBasis R ι d s) := by
  let := monomialIndexFintype ι d
  simp [basis]

instance : Module.Free R (SchurAlgebra R ι d) := Module.Free.of_basis (basis R ι d)

/-- The rank of the Schur algebra equals the number of degree-`d` matrix monomials. -/
@[simp]
theorem finrank [StrongRankCondition R] :
    Module.finrank R (SchurAlgebra R ι d) = (Fintype.card ι * Fintype.card ι).multichoose d := by
  let := monomialIndexFintype ι d
  rw [Module.finrank_eq_nat_card_basis (basis R ι d),
    ← Module.finrank_eq_nat_card_basis (homogeneousSubcoalgebraBasis R ι d)]
  exact finrank_homogeneousSubcoalgebra R ι d

private theorem mul_homogeneousEntry (f g : SchurAlgebra R ι 1) (i j : ι) :
    (f * g) (homogeneousEntry R ι i j) =
      ∑ k, f (homogeneousEntry R ι i k) * g (homogeneousEntry R ι k j) := by
  rw [LinearMap.convMul_apply, comul_homogeneousEntry]
  simp

/-- Evaluating on degree-one matrix coordinates defines an algebra map to square matrices. -/
private noncomputable def toMatrix : SchurAlgebra R ι 1 →ₐ[R] Matrix ι ι R where
  toFun f i j := f (homogeneousEntry R ι i j)
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_mul' f g := by ext i j; exact mul_homogeneousEntry R ι f g i j
  map_zero' := by ext i j; rfl
  map_add' f g := by ext i j; rfl
  commutes' r := by ext i j; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

/-- The matrix comparison evaluates a functional on the indicated matrix-entry coordinate. -/
@[simp]
private theorem toMatrix_apply (f : SchurAlgebra R ι 1) (i j : ι) :
    toMatrix R ι f i j = f (homogeneousEntry R ι i j) := (rfl)

private theorem toMatrix_injective : Function.Injective (toMatrix R ι) := by
  intro f g h
  apply WithConv.ext
  apply (homogeneousSubcoalgebraBasis R ι 1).ext
  intro s
  obtain ⟨⟨i, j⟩, hs⟩ : ∃ ij, Finsupp.single ij 1 = s.1 := by
    exact (Set.ext_iff.mp Finsupp.range_single_one s.1).mpr s.2
  have hb : homogeneousSubcoalgebraBasis R ι 1 s = homogeneousEntry R ι i j := by
    apply Subtype.ext
    simp [← hs, ← MvPolynomial.X_pow_eq_monomial]
  rw [hb]
  exact congrArg (fun A : Matrix ι ι R ↦ A i j) h

private theorem toMatrix_surjective : Function.Surjective (toMatrix R ι) := by
  classical
  intro A
  let e := (coordinateBialgebraAlgEquiv R ι).symm.toLinearMap.comp
    (homogeneousSubcoalgebra R ι 1).toSubmodule.subtype
  refine ⟨WithConv.toConv (∑ ij : ι × ι,
    A ij.1 ij.2 • (MvPolynomial.lcoeff R (Finsupp.single ij 1)).comp e), ?_⟩
  ext i j
  simp [toMatrix_apply, e, coeff_X, Finsupp.single_left_inj]

/-- The first Schur algebra is the full matrix algebra, with its usual multiplication. -/
noncomputable def equivMatrix : SchurAlgebra R ι 1 ≃ₐ[R] Matrix ι ι R :=
  AlgEquiv.ofBijective (toMatrix R ι) ⟨toMatrix_injective R ι, toMatrix_surjective R ι⟩

/-- The degree-one Schur comparison evaluates on matrix-entry coordinates. -/
@[simp]
theorem equivMatrix_apply (f : SchurAlgebra R ι 1) (i j : ι) :
    equivMatrix R ι f i j = f (homogeneousEntry R ι i j) := (rfl)

/-- The inverse comparison is the unique functional with the prescribed matrix-entry values. -/
@[simp]
theorem equivMatrix_symm_apply (A : Matrix ι ι R) (i j : ι) :
    (equivMatrix R ι).symm A (homogeneousEntry R ι i j) = A i j :=
  congrArg (fun B : Matrix ι ι R ↦ B i j)
    ((equivMatrix R ι).apply_symm_apply A)

end SchurAlgebra
end TauCeti
