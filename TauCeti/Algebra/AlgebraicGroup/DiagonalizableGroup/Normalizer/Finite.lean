/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Character
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Weight
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.PointSeparation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Finiteness of the normalizer action on characters

The rational scheme normalizer of a closed diagonalizable subgroup of a finite-type affine
group over a field has finite image in the automorphisms of its character group. Consequently,
the quotient of the normalizer's rational points by the kernel of this action is finite.
By `BialgHom.normalizerCharacterHom_eq_one_iff`, this kernel is exactly the points whose
conjugation restricts to the identity on the subgroup scheme, its rational centralizer.
This is the finiteness step for the Weyl group of a maximal torus; identifying its centralizer
with the torus and identifying the resulting finite group with the reflection group require
further structure theory.

A finite-dimensional coefficient-generating representation exists by the affine-group
embedding theorem. The normalizer permutes its finite set of weights, and agreement on those
weights determines the character automorphism. The more general criterion below works over
a commutative ring with connected spectrum, given a finite coefficient-generating comodule.

The ambient group and diagonalizable subgroup may be nonreduced. These statements concern
rational points of the scheme normalizer, not the normalizer of the rational-point subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a and 21.1.
* T. A. Springer, *Linear Algebraic Groups*, §7.1.
-/

public section

open TauCeti WithConv

namespace BialgHom

noncomputable section

variable {R H X : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
  [ConnectedSpace (PrimeSpectrum R)]

/-- A finite coefficient-generating representation detects the character action of the
normalizer on its finite set of weights, so the character action has finite image. -/
theorem finite_range_normalizerCharacterHom_of_matrixCoefficientSubalgebra_eq_top
    (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)
    {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R H V] [Module.Finite R V]
    (hV : Comodule.matrixCoefficientSubalgebra (R := R) (C := H) (M := V) = ⊤) :
    (Set.range (normalizerCharacterHom π hπ)).Finite := by
  classical
  let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let S := {x : X | DiagonalizableGroup.weightSpace V π.toCoalgHom x ≠ ⊥}
  let : Finite S :=
    (DiagonalizableGroup.finite_setOf_weightSpace_ne_bot V π.toCoalgHom).to_subtype
  let restrict : Set.range (normalizerCharacterHom π hπ) → (S → S) := fun w x ↦
    ⟨w.val x.val, by
      obtain ⟨g, hg⟩ := w.property
      rw [← hg]
      exact (DiagonalizableGroup.weightSpace_apply_ne_bot_iff π g.val
        (normalizerCharacterHom π hπ g) (normalizerCharacterHom_comp π hπ g) x.val).mpr
          x.property⟩
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective restrict
  intro w w' h
  apply Subtype.ext
  apply mulEquiv_eq_of_eqOn_weights π hπ hV
  intro x hx
  exact congrArg Subtype.val (congrFun h (⟨x, hx⟩ : S))

end

section Field

variable {k H X : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]
  [Algebra.FiniteType k H]

/-- The rational scheme normalizer of a closed diagonalizable subgroup of a finite-type
affine group over a field has finite image on the character group. -/
theorem finite_range_normalizerCharacterHom
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π) :
    (Set.range (normalizerCharacterHom π hπ)).Finite := by
  obtain ⟨V, hfinite, hV⟩ :=
    Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := k) (C := H)
  let : Module.Finite k V := hfinite
  exact finite_range_normalizerCharacterHom_of_matrixCoefficientSubalgebra_eq_top π hπ hV

/-- The rational normalizer modulo the kernel of its character action is finite. The kernel
is the rational centralizer of the diagonalizable subgroup scheme, as characterized by
`normalizerCharacterHom_eq_one_iff`. -/
instance finite_normalizerPoints_quotient_ker_normalizerCharacterHom
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π) :
    Finite (normalizerPoints π hπ ⧸ (normalizerCharacterHom π hπ).ker) := by
  let : Finite (normalizerCharacterHom π hπ).range :=
    (finite_range_normalizerCharacterHom π hπ).to_subtype
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange
    (normalizerCharacterHom π hπ)).symm.toEquiv

end Field

end BialgHom
