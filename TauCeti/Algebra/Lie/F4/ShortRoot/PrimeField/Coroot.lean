/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Differential
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.WeightTorus
public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Serre
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent

/-!
# Coroot differentials of the short-root F₄ carrier over 𝔽₂

The numbered root differentials satisfy the transposed Bourbaki F₄ Serre relations.
Their opposite-root brackets are the differentials of the actual simple-coroot cocharacters
through the weight torus. These coroot differentials are independent, even in characteristic
two, and form a basis of the toral tangent image. All statements allow arbitrary commutative
𝔽₂-algebras as tangent coefficients.

The Serre comparison recovers the existing matrix representation under the injective tangent
inclusion. It does not assert that the simple-root differentials generate the entire tangent
Lie algebra, or identify the carrier with an independently pinned simply connected group.
In particular the Serre image is not identified with the reduction of the full Chevalley lattice.

The construction adapts `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Serre` and
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using the existing integral short-root
matrix relations and the prime-field root differentials.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

open CategoryTheory
open scoped Matrix

namespace TauCeti.F4ShortRoot.PrimeField

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

local notation "Q" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator

variable (B : Type*) [CommRing B] [Algebra (ZMod 2) B]

/-- The bracket of the normalized opposite-root differentials. -/
def cartanDerivation (i : Fin 4) :
    Derivation (ZMod 2) Q (Bialgebra.CounitAlgebra (ZMod 2) Q B) :=
  ⁅rootDerivation B (.inl i), rootDerivation B (.inr i)⁆

/-- The Cartan differential is the bracket of the two opposite root differentials. -/
theorem cartanDerivation_def (i : Fin 4) :
    cartanDerivation B i = ⁅rootDerivation B (.inl i), rootDerivation B (.inr i)⁆ :=
  (rfl)

/-- The opposite-root bracket has the integral diagonal Cartan matrix. -/
@[simp]
theorem tangentMatrixLieHom_cartanDerivation (i : Fin 4) :
    tangentMatrixLieHom B (cartanDerivation B i) = cartanMatrixBaseChange B i := by
  rw [cartanDerivation_def, LieHom.map_lie, tangentMatrixLieHom_rootDerivation,
    tangentMatrixLieHom_rootDerivation, rootMatrix_inl, rootMatrix_inr]
  simpa only [raisingMatrixBaseChange_eq_map, loweringMatrixBaseChange_eq_map] using
    (isSerreSystemBaseChange B).lie_E_F_self i

/-- The actual root differentials satisfy the F₄ Serre relations, with Cartan rows indexed by
coroots, including in characteristic two. -/
theorem isSerreSystem_rootDerivation :
    IsSerreSystem B CartanMatrix.F₄ᵀ (cartanDerivation B)
      (fun i ↦ rootDerivation B (.inl i)) (fun i ↦ rootDerivation B (.inr i)) := by
  apply IsSerreSystem.of_injective (tangentMatrixLieHom B) (tangentMatrixLieHom_injective B)
  have hH : tangentMatrixLieHom B ∘ cartanDerivation B = cartanMatrixBaseChange B := by
    funext i
    exact tangentMatrixLieHom_cartanDerivation B i
  have hE : tangentMatrixLieHom B ∘ (fun i ↦ rootDerivation B (.inl i)) =
      raisingMatrixBaseChange B := by
    funext i
    rw [Function.comp_apply, tangentMatrixLieHom_rootDerivation, rootMatrix_inl,
      raisingMatrixBaseChange_eq_map]
  have hF : tangentMatrixLieHom B ∘ (fun i ↦ rootDerivation B (.inr i)) =
      loweringMatrixBaseChange B := by
    funext i
    rw [Function.comp_apply, tangentMatrixLieHom_rootDerivation, rootMatrix_inr,
      loweringMatrixBaseChange_eq_map]
  rw [hH, hE, hF]
  exact isSerreSystemBaseChange B

/-- The comparison from the F₄ Serre presentation to the carrier's tangent Lie algebra. -/
def tangentSerreLift : Matrix.ToLieAlgebra B CartanMatrix.F₄ᵀ →ₗ⁅B⁆
    Derivation (ZMod 2) Q (Bialgebra.CounitAlgebra (ZMod 2) Q B) :=
  serreLift (isSerreSystem_rootDerivation B)

/-- The Serre comparison sends a Cartan generator to its opposite-root bracket. -/
@[simp]
theorem tangentSerreLift_serreH (i : Fin 4) :
    tangentSerreLift B (serreH B CartanMatrix.F₄ᵀ i) = cartanDerivation B i :=
  serreLift_serreH _ i

/-- The Serre comparison sends a positive generator to its normalized differential. -/
@[simp]
theorem tangentSerreLift_serreE (i : Fin 4) :
    tangentSerreLift B (serreE B CartanMatrix.F₄ᵀ i) = rootDerivation B (.inl i) :=
  serreLift_serreE _ i

/-- The Serre comparison sends a negative generator to its normalized differential. -/
@[simp]
theorem tangentSerreLift_serreF (i : Fin 4) :
    tangentSerreLift B (serreF B CartanMatrix.F₄ᵀ i) = rootDerivation B (.inr i) :=
  serreLift_serreF _ i

/-- The matrix realization of the tangent comparison is the existing short-root representation. -/
theorem tangentMatrixLieHom_comp_tangentSerreLift :
    (tangentMatrixLieHom B).comp (tangentSerreLift B) = serreRepresentationBaseChange B := by
  apply serre_hom_ext
  · intro i
    rw [LieHom.comp_apply, tangentSerreLift_serreH, tangentMatrixLieHom_cartanDerivation,
      serreRepresentationBaseChange_serreH]
  · intro i
    rw [LieHom.comp_apply, tangentSerreLift_serreE, tangentMatrixLieHom_rootDerivation,
      serreRepresentationBaseChange_serreE, rootMatrix_inl, raisingMatrixBaseChange_eq_map]
  · intro i
    rw [LieHom.comp_apply, tangentSerreLift_serreF, tangentMatrixLieHom_rootDerivation,
      serreRepresentationBaseChange_serreF, rootMatrix_inr, loweringMatrixBaseChange_eq_map]

/-- The simple-coroot cocharacter defined by evaluation in fundamental-weight coordinates. -/
def corootCocharacter (i : Fin 4) : Q →ₐc[ZMod 2] LaurentPolynomial (ZMod 2) :=
  weightTorusRestriction.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative

/-- The coroot cocharacter factors through the actual closed weight torus. -/
theorem corootCocharacter_def (i : Fin 4) :
    corootCocharacter i =
      weightTorusRestriction.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The cocharacter corresponds to the named simple coroot of the simply connected root datum. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin 4) :
    corootCocharacter i = weightTorusRestriction.hom.cocharacter
      (SplitTorus.cocharEquiv.symm
        ((DynkinType.F4.simplyConnectedRootDatum DynkinType.valid_F4).coroot
          (DynkinType.F4.simpleIndex DynkinType.valid_F4 i))) := by
  rw [corootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  have heval : SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
      (Pi.single i 1 : Fin 4 → ℤ) := by
    ext j
    simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  exact heval.trans (DynkinType.coroot_simpleIndex DynkinType.F4 DynkinType.valid_F4 i).symm

/-- The differential of a coroot has the diagonal matrix of weight–coroot pairings. -/
theorem tangentMatrixLieHom_derivationComp_corootCocharacter (i : Fin 4) :
    tangentMatrixLieHom B
        (derivationComp (corootCocharacter i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B))) =
      cartanMatrixBaseChange B i := by
  have hπ : weightTorusRestriction.hom.comp (Bialgebra.Quotient.mkBialgHom (J).toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ZMod 2)
        DynkinType.f4ShortRootWeight := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [tangentMatrixLieHom_apply, HopfIdeal.quotientLieHom_apply, corootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  ext a b
  simp [cartanMatrixBaseChange_apply, cartanMatrix_apply, Matrix.diagonal_apply]

/-- The opposite-root bracket is the differential of the actual simple-coroot cocharacter. -/
theorem cartanDerivation_eq_derivationComp_corootCocharacter (i : Fin 4) :
    cartanDerivation B i = derivationComp (corootCocharacter i)
      (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) := by
  apply tangentMatrixLieHom_injective B
  rw [tangentMatrixLieHom_cartanDerivation,
    tangentMatrixLieHom_derivationComp_corootCocharacter]

/-- The weight-torus differential sends its coordinate tangent basis to the Cartan brackets. -/
theorem derivationCompLieHom_weightTorusRestriction_tangentBasis (i : Fin 4) :
    derivationCompLieHom (B := B) weightTorusRestriction.hom
        (SplitTorus.tangentBasis (R := ZMod 2) (B := B) i) = cartanDerivation B i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    cartanDerivation_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The toral tangent image is exactly the span of the numbered Cartan brackets. -/
theorem range_derivationCompLieHom_weightTorusRestriction_eq_span :
    LinearMap.range (derivationCompLieHom (B := B) weightTorusRestriction.hom).toLinearMap =
      Submodule.span B (Set.range (cartanDerivation B)) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [cartanDerivation_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The simple-coroot differentials are independent over every coefficient algebra. -/
theorem linearIndependent_cartanDerivation : LinearIndependent B (cartanDerivation B) := by
  have h := (SplitTorus.tangentBasis (R := ZMod 2) (B := B) (I := Fin 4)).linearIndependent
    |>.map_injOn (derivationCompLieHom (B := B) weightTorusRestriction.hom).toLinearMap
    (derivationCompLieHom_injective_of_surjective _ weightTorusRestriction_surjective).injOn
  have heq :
      ⇑(derivationCompLieHom (B := B) weightTorusRestriction.hom).toLinearMap ∘
        SplitTorus.tangentBasis (R := ZMod 2) (B := B) (I := Fin 4) = cartanDerivation B := by
    funext i
    exact derivationCompLieHom_weightTorusRestriction_tangentBasis B i
  rwa [heq] at h

/-- The simple-coroot differentials form a basis of the toral tangent image, written as a span. -/
def cartanBasis : Module.Basis (Fin 4) B (Submodule.span B (Set.range (cartanDerivation B))) :=
  Module.Basis.span (linearIndependent_cartanDerivation B)

/-- A Cartan basis vector includes as the corresponding coroot differential. -/
@[simp]
theorem coe_cartanBasis (i : Fin 4) :
    (cartanBasis B i : Derivation (ZMod 2) Q (Bialgebra.CounitAlgebra (ZMod 2) Q B)) =
      cartanDerivation B i :=
  Module.Basis.coe_span_apply (linearIndependent_cartanDerivation B) i

end

end TauCeti.F4ShortRoot.PrimeField
