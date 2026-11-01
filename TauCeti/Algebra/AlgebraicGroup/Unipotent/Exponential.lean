/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Local nilpotence of invariant vector fields on unipotent groups

Every tangent vector at the identity of a reduced finite-type unipotent affine group over
an algebraically closed field has a locally nilpotent invariant derivation on its coordinate
ring. A faithful upper-unitriangular representation makes its tangent matrix nilpotent;
local nilpotence on the coordinate ring of the general linear group then descends along the
surjective coordinate map of the faithful representation.

The local-nilpotence statement holds in every characteristic. In characteristic zero,
Cartier's theorem removes the reducedness assumption, and every tangent vector consequently
defines the intrinsic polynomial exponential curve `Bialgebra.expPointPolynomial` and its
one-parameter homomorphisms `Bialgebra.expPointHom`. Local nilpotence is a conclusion here,
rather than an additional hypothesis on the tangent vector. No connectedness hypothesis or
choice of a matrix realization occurs in that conclusion.

The proof uses the faithful upper-unitriangular embedding and the invariant-vector-field
calculation on `GLₙ`, together with descent of local nilpotence along surjective bialgebra maps.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 14.
-/

public section

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} {H : Type v} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- Every invariant tangent derivation on a reduced finite-type affine group with unipotent
rational points is locally nilpotent. The group need not be connected, and the field may have
positive characteristic. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint
    [IsReduced H] (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  obtain ⟨M, n, b, hsurj⟩ := Comodule.exists_coordinateBialgHom_surjective (k := k) (H := H)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k M := Module.Finite.of_basis b
  obtain ⟨m, c, hc⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperUnitriangular_of_forall_isUnipotentPoint
      (M := M) hH
  have hcsurj : Function.Surjective (Comodule.coordinateBialgHom (H := H) c) := by
    rw [Comodule.coordinateBialgHom_surjective_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top]
      at hsurj ⊢
    exact hsurj
  exact d.exists_iterate_leftInvariantDerivation_eq_zero_of_isUpperUnitriangular c hc hcsurj

/-- In characteristic zero, invariant tangent derivations of a finite-type affine group with
unipotent rational points are locally nilpotent without any reducedness assumption.
Thus every tangent vector is an admissible input to the intrinsic polynomial exponential. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint_of_charZero
    [CharZero k] (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  have := isReduced_of_charZero k H
  exact exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint hH d

end TauCeti.HopfAlgebra
