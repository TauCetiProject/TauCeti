/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Generated.StandardComodule

/-!
# Simple-coroot differentials of the generated Geck group

The coordinate cocharacters of the Geck weight torus factor through the group generated over
any commutative base ring. They are indexed by the simple coroots of the named simply connected
root datum. Their differential matrices are diagonal, with entries given by pairing the Geck
weights with those coroots, over every coefficient algebra.

When the weights span the full character lattice, these differentials are independent and give
a basis of the toral tangent image. This hypothesis holds for E₈, F₄ and G₂, but is deliberately
not imposed on the cocharacter construction or its matrix formula. In particular no injectivity
is asserted for the full-weight torus parametrization of other Geck representations.

This concerns the subgroup generated over the base ring, not merely the scalar extension of the
integral carrier. Neither equality of those groups, maximality of the weight torus, nor an
identification with an independently pinned simply connected group is asserted.

## Main declarations

* `TauCeti.DynkinType.geckGeneratedCorootCocharacter`: the numbered simple cocharacters.
* `TauCeti.DynkinType.geckGeneratedCorootVector`: their normalized differentials.
* `TauCeti.DynkinType.tangentMatrix_geckGeneratedCorootVector`: their weight-pairing matrices.
* `TauCeti.DynkinType.linearIndependent_geckGeneratedCorootVector`: independence under full span.
* `TauCeti.DynkinType.geckGeneratedCorootBasis`: a basis of their span, the toral tangent image.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233–3247.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The interface follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot` and the integral
Geck calculation in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Coroot`.
The represented-cocharacter matrix formula and split-torus tangent basis are reused directly.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid) (R : Type*) [CommRing R]

/-- The simple cocharacter obtained by evaluating a fundamental-weight coordinate and including
its weight torus into the Geck group generated over `R`. -/
def geckGeneratedCorootCocharacter (i : Fin t.rank) :
    t.geckGeneratedCoordinateHopfAlgebra ht R →ₐc[R] LaurentPolynomial R :=
  (t.geckGeneratedWeightTorusCoordinateMap ht R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The generated simple cocharacter is the indicated coordinate of the existing weight torus. -/
theorem geckGeneratedCorootCocharacter_def (i : Fin t.rank) :
    t.geckGeneratedCorootCocharacter ht R i =
      (t.geckGeneratedWeightTorusCoordinateMap ht R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The cocharacter is the numbered simple coroot of the named simply connected root datum. -/
theorem geckGeneratedCorootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin t.rank) :
    t.geckGeneratedCorootCocharacter ht R i =
      (t.geckGeneratedWeightTorusCoordinateMap ht R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          ((t.simplyConnectedRootDatum ht).coroot (t.simpleIndex ht i))) := by
  rw [geckGeneratedCorootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  exact (SplitTorus.cocharEquiv_applyAddHom i).trans (t.coroot_simpleIndex ht i).symm

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The matrix differential of a simple cocharacter is diagonal, with weight–coroot pairings
multiplied by its multiplicative tangent parameter. -/
@[simp↓]
theorem tangentMatrix_derivationComp_geckGeneratedCorootCocharacter (i : Fin t.rank)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    GeneralLinear.tangentMatrix (t.geckDim ht)
        (derivationComp (t.geckGeneratedCoordinateMap ht R).hom
          (derivationComp (t.geckGeneratedCorootCocharacter ht R i) d)) =
      Matrix.diagonal (fun a ↦ t.geckWeightFin ht a i •
        MultiplicativeGroup.tangentLinearEquiv d) := by
  have hπ : (t.geckGeneratedWeightTorusCoordinateMap ht R).hom.comp
      (t.geckGeneratedCoordinateMap ht R).hom =
        GeneralLinear.weightTorusCoordinateBialgHom (S := R) (t.geckWeightFin ht) := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      geckGeneratedCoordinateMap_comp_geckGeneratedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [geckGeneratedCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  simp

/-- The differential of the numbered simple coroot at the tangent vector of `𝔾ₘ` with value one
on its standard character. -/
def geckGeneratedCorootVector (i : Fin t.rank) :
    Derivation R (t.geckGeneratedCoordinateHopfAlgebra ht R)
      (Bialgebra.CounitAlgebra R (t.geckGeneratedCoordinateHopfAlgebra ht R) B) :=
  derivationComp (t.geckGeneratedCorootCocharacter ht R i)
    (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B))

/-- The simple-coroot vector is its normalized cocharacter differential. -/
theorem geckGeneratedCorootVector_def (i : Fin t.rank) :
    t.geckGeneratedCorootVector ht R (B := B) i =
      derivationComp (t.geckGeneratedCorootCocharacter ht R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) :=
  (rfl)

/-- The weight-torus differential sends a coordinate tangent vector to its simple-coroot vector. -/
theorem derivationCompLieHom_geckGeneratedWeightTorusCoordinateMap_tangentBasis
    (i : Fin t.rank) :
    derivationCompLieHom (B := B) (t.geckGeneratedWeightTorusCoordinateMap ht R).hom
        (SplitTorus.tangentBasis (R := R) (B := B) i) =
      t.geckGeneratedCorootVector ht R (B := B) i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    geckGeneratedCorootVector_def, geckGeneratedCorootCocharacter_def,
    derivationCompLieHom_apply]

/-- The normalized simple-coroot differential has diagonal entries given by the corresponding
fundamental-weight coordinates of the Geck weights. -/
@[simp]
theorem tangentMatrix_geckGeneratedCorootVector (i : Fin t.rank) :
    GeneralLinear.tangentMatrix (t.geckDim ht)
        (derivationComp (t.geckGeneratedCoordinateMap ht R).hom
          (t.geckGeneratedCorootVector ht R (B := B) i)) =
      Matrix.diagonal (fun a ↦ (t.geckWeightFin ht a i : B)) := by
  rw [geckGeneratedCorootVector_def,
    tangentMatrix_derivationComp_geckGeneratedCorootCocharacter]
  simp

/-- The toral tangent image is spanned by the numbered simple-coroot differentials, whether or
not the weight-torus parametrization is an immersion. -/
theorem range_derivationCompLieHom_geckGeneratedWeightTorusCoordinateMap_eq_span :
    LinearMap.range (derivationCompLieHom (B := B)
        (t.geckGeneratedWeightTorusCoordinateMap ht R).hom).toLinearMap =
      Submodule.span B (Set.range (t.geckGeneratedCorootVector ht R (B := B))) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [← SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_geckGeneratedWeightTorusCoordinateMap_tangentBasis]

/-- Full character-lattice span makes the generated weight-torus differential injective over
any coefficient algebra, including nonreduced algebras in bad characteristic. -/
theorem derivationCompLieHom_geckGeneratedWeightTorusCoordinateMap_injective
    (hwt : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤) :
    Function.Injective (derivationCompLieHom (B := B)
      (t.geckGeneratedWeightTorusCoordinateMap ht R).hom) := by
  apply derivationCompLieHom_injective_of_surjective
  have h : Function.Surjective
      (GeneralLinear.weightTorusCoordinateBialgHom (S := R) (t.geckWeightFin ht)) := by
    rw [GeneralLinear.weightTorusCoordinateBialgHom_def]
    apply DiagonalizableGroup.surjective_diagonalCoordinateMap
    exact SplitTorus.closure_range_weightCharacter_eq_top _ hwt
  rw [← GeneralLinear.hom_weightTorusBaseChangeCoordinateMap ℤ R,
    ← geckGeneratedCoordinateMap_comp_geckGeneratedWeightTorusCoordinateMap,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at h
  exact Function.Surjective.of_comp h

/-- The numbered simple-coroot differentials are independent when the Geck weights span the full
character lattice. No characteristic or reducedness hypothesis is needed. -/
theorem linearIndependent_geckGeneratedCorootVector
    (hwt : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤) :
    LinearIndependent B (t.geckGeneratedCorootVector ht R (B := B)) := by
  convert SplitTorus.linearIndependent_derivationComp_cocharacter (B := B)
    (t.geckGeneratedWeightTorusCoordinateMap ht R).hom
    (t.derivationCompLieHom_geckGeneratedWeightTorusCoordinateMap_injective ht R hwt) using 1
  funext i
  rw [← SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_geckGeneratedWeightTorusCoordinateMap_tangentBasis]

/-- A basis of the span of the numbered simple-coroot differentials, equivalently the toral
tangent image, when the Geck weights span the full character lattice. -/
def geckGeneratedCorootBasis
    (hwt : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤) :
    Module.Basis (Fin t.rank) B
      (Submodule.span B (Set.range (t.geckGeneratedCorootVector ht R (B := B)))) :=
  Module.Basis.span (t.linearIndependent_geckGeneratedCorootVector ht R hwt)

/-- A simple-coroot basis vector includes as the corresponding normalized differential. -/
@[simp]
theorem coe_geckGeneratedCorootBasis
    (hwt : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤) (i : Fin t.rank) :
    (t.geckGeneratedCorootBasis ht R (B := B) hwt i :
      Derivation R (t.geckGeneratedCoordinateHopfAlgebra ht R)
        (Bialgebra.CounitAlgebra R (t.geckGeneratedCoordinateHopfAlgebra ht R) B)) =
      t.geckGeneratedCorootVector ht R (B := B) i :=
  Module.Basis.coe_span_apply (t.linearIndependent_geckGeneratedCorootVector ht R hwt) i

end

end TauCeti.DynkinType
