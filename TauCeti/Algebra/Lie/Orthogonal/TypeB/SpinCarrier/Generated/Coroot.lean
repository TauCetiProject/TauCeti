/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Root.Coordinates

/-!
# Simple-coroot differentials in the generated type-B spin group

The fundamental-weight coordinates of the spin weight torus give actual cocharacters of the
subgroup generated over the coefficient ring. They are the numbered simple coroots of the
simply connected type-B root datum. Their differentials are diagonal matrices of spin-weight
coordinates and form a basis of the toral tangent image over every coefficient algebra,
including in characteristic two. Independence uses the full weight lattice rather than
invertibility of the Cartan matrix.

These are cocharacters of the generated subgroup, not just of the specialization of the
integral spin carrier. No equality of those groups, maximality of the torus, or identification
with an independently pinned group is asserted. The comparison with opposite-root brackets
is separate from the toral differential calculation here.

The construction follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot` and the
integral-carrier calculation in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Root.Coroot`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.
-/

public section

open CategoryTheory

namespace TauCeti.TypeBSpinCarrier

noncomputable section

variable (n : ℕ) (R : Type*) [CommRing R]

/-- The numbered coordinate cocharacter of the spin weight torus, included in the subgroup
generated over `R`. -/
def generatedCorootCocharacter (i : Fin (n + 1)) :
    generatedCoordinateHopfAlgebra n R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap n R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The simple cocharacter is evaluation at its fundamental-weight coordinate. -/
theorem generatedCorootCocharacter_def (i : Fin (n + 1)) :
    generatedCorootCocharacter n R i =
      (generatedWeightTorusCoordinateMap n R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The cocharacter agrees with the named simple coroot in Bourbaki numbering. Only this
comparison requires validity of the named Dynkin type; the tangent formulas include rank one. -/
theorem generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : (DynkinType.B (n + 1)).Valid) (i : Fin (n + 1)) :
    generatedCorootCocharacter n R i =
      (generatedWeightTorusCoordinateMap n R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          (((DynkinType.B (n + 1)).simplyConnectedRootDatum ht).coroot
            ((DynkinType.B (n + 1)).simpleIndex ht i))) := by
  rw [generatedCorootCocharacter_def]
  congr 1
  exact (cocharEquiv_symm_coroot_simpleIndex n ht i).symm

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The coroot differential is diagonal, with entries the simple-coroot coordinates of the
spin weights multiplied by the multiplicative tangent parameter. -/
@[simp↓]
theorem tangentMatrix_derivationComp_generatedCorootCocharacter (i : Fin (n + 1))
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (generatedCoordinateMap n R).hom
          (derivationComp (B := B) (generatedCorootCocharacter n R i) d)) =
      Matrix.diagonal (fun a ↦ basisWeight n a i • MultiplicativeGroup.tangentLinearEquiv d) := by
  have hπ : (generatedWeightTorusCoordinateMap n R).hom.comp
      (generatedCoordinateMap n R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) (basisWeight n) := by
    rw [← CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [generatedCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  simp

/-- The unit tangent vector of the numbered simple-coroot cocharacter in the generated group. -/
def generatedCartanVector (i : Fin (n + 1)) :
    Derivation R (generatedCoordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra n R) B) :=
  derivationComp (generatedCorootCocharacter n R i)
    (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B))

/-- The normalized simple-coroot vector is the differential at the unit tangent parameter. -/
theorem generatedCartanVector_def (i : Fin (n + 1)) :
    generatedCartanVector n R (B := B) i =
      derivationComp (generatedCorootCocharacter n R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) :=
  (rfl)

/-- The matrix of the normalized coroot vector is the diagonal of its spin-weight coordinates. -/
@[simp↓]
theorem tangentMatrix_generatedCartanVector (i : Fin (n + 1)) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (generatedCoordinateMap n R).hom
          (generatedCartanVector n R (B := B) i)) =
      Matrix.diagonal (fun a ↦ (basisWeight n a i : B)) := by
  simp [generatedCartanVector_def, zsmul_eq_mul]

/-- The generated weight-torus differential sends its coordinate basis to the coroot vectors. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis (i : Fin (n + 1)) :
    derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n R).hom
        (SplitTorus.tangentBasis (R := R) (B := B) i) =
      generatedCartanVector n R (B := B) i := by
  simpa only [generatedCartanVector_def, generatedCorootCocharacter_def,
    derivationCompLieHom_apply] using
    (SplitTorus.derivationCompLieHom_tangentBasis
      (B := B) (generatedWeightTorusCoordinateMap n R).hom i)

/-- The toral tangent image is exactly the span of the numbered simple-coroot vectors. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n R).hom).toLinearMap =
      Submodule.span B (Set.range (generatedCartanVector n R (B := B))) := by
  simpa only [derivationCompLieHom_apply, ← generatedCorootCocharacter_def n R,
    ← generatedCartanVector_def n R] using
    (SplitTorus.range_derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n R).hom)

/-- The generated weight-torus differential is injective over every coefficient algebra. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_injective :
    Function.Injective
      (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n R).hom) :=
  derivationCompLieHom_injective_of_surjective _ (generatedWeightTorusCoordinateMap_surjective n R)

/-- The numbered simple-coroot vectors are independent over every coefficient algebra,
including in characteristic two. -/
theorem linearIndependent_generatedCartanVector :
    LinearIndependent B (generatedCartanVector n R (B := B)) := by
  simpa only [derivationCompLieHom_apply, ← generatedCorootCocharacter_def n R,
    ← generatedCartanVector_def n R] using
    (SplitTorus.linearIndependent_derivationComp_cocharacter
      (B := B) (generatedWeightTorusCoordinateMap n R).hom
      (derivationCompLieHom_generatedWeightTorusCoordinateMap_injective n R (B := B)))

/-- The simple-coroot differentials form a basis of their span, the toral tangent image. -/
def generatedCartanBasis :
    Module.Basis (Fin (n + 1)) B
      (Submodule.span B (Set.range (generatedCartanVector n R (B := B)))) :=
  Module.Basis.span (linearIndependent_generatedCartanVector n R)

/-- The coroot basis includes into the tangent algebra as the numbered coroot vectors. -/
@[simp↓]
theorem coe_generatedCartanBasis (i : Fin (n + 1)) :
    (generatedCartanBasis n R (B := B) i :
      Derivation R (generatedCoordinateHopfAlgebra n R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra n R) B)) =
      generatedCartanVector n R (B := B) i :=
  Module.Basis.coe_span_apply (linearIndependent_generatedCartanVector n R) i

end

end TauCeti.TypeBSpinCarrier
