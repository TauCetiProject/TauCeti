/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.Polynomial
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Descent
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Extending polynomial general-linear representations to the matrix monoid

A rational `GLₙ` representation extends uniquely to a rational matrix-monoid
representation exactly when its coaction factors through polynomial matrix coordinates.
For a finite-dimensional representation, this is equivalent to every entry of a
coefficient matrix being polynomial. These are coactions on the actual coordinate
bialgebras, so the extension satisfies both the unit and multiplication laws; a
pointwise action of `GLₙ(k)` alone is insufficient, especially over finite fields.

The extension criterion uses `CoalgHom.existsUnique_comoduleFactor_iff` and the
determinant-localization inclusion `GeneralLinear.polynomialCoordinateBialgHom`.
The point-action comparison applies to every commutative value algebra.

## References

* J. A. Green, *Polynomial Representations of GLₙ*, §1.
-/

public section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

section Field

variable (k : Type*) [Field k] (n : ℕ)
variable (M : Type*) [AddCommGroup M] [Module k M]
  [Comodule k (coordinateHopfAlgebra k n) M]

/-- A rational `GLₙ` coaction extends uniquely to the matrix monoid if and only if
it takes values in polynomial matrix coordinates. This also applies to infinite modules. -/
theorem existsUnique_matrixMonoidComodule_iff :
    (∃! σ : Comodule k (MatrixMonoid.coordinateBialgebra k n) M,
      (polynomialCoordinateBialgHom k n).toCoalgHom.toLinearMap.lTensor M ∘ₗ σ.coact =
        Comodule.coact (R := k) (C := coordinateHopfAlgebra k n)) ↔
      ∀ m, Comodule.coact (R := k) (C := coordinateHopfAlgebra k n) m ∈
        LinearMap.range ((polynomialCoordinateBialgHom k n).toCoalgHom.toLinearMap.lTensor M) :=
  CoalgHom.existsUnique_comoduleFactor_iff _ (polynomialCoordinateBialgHom_injective k n)

/-- A finite rational `GLₙ` representation extends uniquely to the matrix monoid exactly
when each entry of its coefficient matrix lies in the polynomial coordinate subalgebra.
The criterion works with any finite basis, over every field and in size zero. -/
theorem existsUnique_matrixMonoidComodule_iff_coefficientMatrix
    {ι : Type*} [Finite ι] (b : Module.Basis ι k M) :
    (∃! σ : Comodule k (MatrixMonoid.coordinateBialgebra k n) M,
      (polynomialCoordinateBialgHom k n).toCoalgHom.toLinearMap.lTensor M ∘ₗ σ.coact =
        Comodule.coact (R := k) (C := coordinateHopfAlgebra k n)) ↔
      ∀ i j, Comodule.coefficientMatrix (C := coordinateHopfAlgebra k n) b i j ∈
        LinearMap.range (polynomialCoordinateBialgHom k n).toCoalgHom.toLinearMap :=
  Module.Basis.existsUnique_comoduleFactor_iff b _
    (polynomialCoordinateBialgHom_injective k n)

end Field

variable (k : Type*) [CommRing k] (n : ℕ)
variable (M : Type*) [AddCommMonoid M] [Module k M]
  [Comodule k (coordinateHopfAlgebra k n) M]

/-- The extended matrix-monoid action agrees with the original rational action on
every algebra-valued general-linear point. The coaction factorization determines this
comparison without requiring a chosen basis. -/
theorem endOfPoint_matrixMonoidComodule
    (σ : Comodule k (MatrixMonoid.coordinateBialgebra k n) M)
    (hσ : (polynomialCoordinateBialgHom k n).toCoalgHom.toLinearMap.lTensor M ∘ₗ σ.coact =
      Comodule.coact (R := k) (C := coordinateHopfAlgebra k n))
    {A : Type*} [CommRing A] [Algebra k A]
    (g : coordinateHopfAlgebra k n →ₐ[k] A) :
    (letI := σ;
      Comodule.endOfPoint M (g.comp (polynomialCoordinateBialgHom k n).toAlgHom)) =
        Comodule.endOfPoint M g := by
  let := σ
  have heq : Comodule.Corestrict (polynomialCoordinateBialgHom k n).toCoalgHom =
      (inferInstance : Comodule k (coordinateHopfAlgebra k n) M) := Comodule.ext hσ
  rw [← Comodule.endOfPoint_corestrict, heq]

end TauCeti.GeneralLinear
