/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.Matrix.IntegralCast

/-!
# Coroot differentials of the short-root G₂ carrier over 𝔽₃

The two fundamental-weight coordinates of the weight torus define the numbered simple-coroot
cocharacters of the short-root carrier. Their differentials are the brackets of the normalized
opposite simple-root differentials. This identifies the root parameters and coroot normalization
in the actual tangent Lie algebra, not just in an abstract root datum.

The calculation holds over every commutative 𝔽₃-algebra, including nonreduced algebras. The two
coroot differentials form a basis of the tangent image of the weight torus. No identification
with an independently constructed pinned simply connected group scheme is asserted.

## Main declarations

* `corootCocharacter`: the numbered simple-coroot cocharacters through the weight torus.
* `corootVector`: their differentials at the unit tangent vector of `𝔾ₘ`.
* `lie_rootSubgroup_differentials_eq_corootVector`: opposite-root bracket normalization.
* `range_derivationCompLieHom_weightTorusCoordinateMap_eq_span`: the toral tangent image.
* `corootBasis`: a basis of that image, expressed as the span of the coroot vectors.

The construction follows the E₇ coroot calculation in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using the integral short-root matrices
of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The cocharacter obtained by evaluating the `i`-th fundamental-weight coordinate and
including the weight torus in the short-root carrier. -/
def corootCocharacter (i : Fin 2) :
    carrierAlgebra →ₐc[ZMod 3] LaurentPolynomial (ZMod 3) :=
  weightTorusCoordinateMap.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative

/-- The numbered coroot cocharacter is induced by its fundamental-weight coordinate. -/
theorem corootCocharacter_def (i : Fin 2) :
    corootCocharacter i =
      weightTorusCoordinateMap.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- These are the named simple coroots of the simply connected G₂ root datum, in Bourbaki
numbering (short root first). -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin 2) :
    corootCocharacter i = weightTorusCoordinateMap.hom.cocharacter
      (SplitTorus.cocharEquiv.symm
        ((DynkinType.G2.simplyConnectedRootDatum DynkinType.valid_G2).coroot
          (DynkinType.G2.simpleIndex DynkinType.valid_G2 i))) := by
  rw [corootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  have heval : SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
      (Pi.single i 1 : Fin 2 → ℤ) := by
    ext j
    simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  exact heval.trans (DynkinType.G2.coroot_simpleIndex DynkinType.valid_G2 i).symm

variable (B : Type*) [CommRing B] [Algebra (ZMod 3) B]

/-- The differential of a numbered simple-coroot cocharacter at the unit multiplicative
tangent vector, with values in any commutative 𝔽₃-algebra. -/
def corootVector (i : Fin 2) :
    Derivation (ZMod 3) carrierAlgebra (Bialgebra.CounitAlgebra (ZMod 3) carrierAlgebra B) :=
  derivationComp (corootCocharacter i)
    (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B))

/-- The coroot vector is the differential of its cocharacter at tangent parameter one. -/
theorem corootVector_def (i : Fin 2) :
    corootVector B i = derivationComp (corootCocharacter i)
      (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) :=
  (rfl)

/-- The matrix of a coroot differential is the diagonal matrix of the corresponding integral
weight coordinates, reduced in the coefficient algebra. -/
@[simp]
theorem tangentMatrix_corootVector (i : Fin 2) :
    GeneralLinear.tangentMatrix 7
        (HopfIdeal.quotientLieHom (B := B) (CommHopfAlgCat.commonKernelHopfIdeal generator)
          (corootVector B i)) =
      (cartanMatrix i).map (Int.cast : ℤ → B) := by
  have hπ : weightTorusCoordinateMap.hom.comp
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
        (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ZMod 3) weight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [corootVector_def, corootCocharacter_def, HopfIdeal.quotientLieHom_apply,
    ← CommHopfAlgCat.hom_mkQuotient,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  ext a b
  simp [Matrix.diagonal_apply, cartanMatrix_apply]

/-- The normalized opposite root vectors have bracket equal to the actual simple-coroot
differential over the prime field. -/
theorem lie_rootVector_eq_corootVector (i : Fin 2) :
    ⁅Derivation.cotangentLinearEquiv (B := ZMod 3) (rootVector (.inl i)),
      Derivation.cotangentLinearEquiv (B := ZMod 3) (rootVector (.inr i))⁆ =
        corootVector (ZMod 3) i := by
  apply (Derivation.cotangentLinearEquiv (B := ZMod 3)).symm.injective
  apply tangentMatrix_injective
  rw [tangentMatrix_symm_lie, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    tangentMatrix_rootVector, tangentMatrix_rootVector]
  have h : ⁅(raisingMatrix i).map (Int.cast : ℤ → ZMod 3),
      (loweringMatrix i).map (Int.cast : ℤ → ZMod 3)⁆ =
        (cartanMatrix i).map (Int.cast : ℤ → ZMod 3) := by
    simpa only [Function.comp_apply, matrixIntCastLieHom_eq_map] using
      (G2ShortRoot.isSerreSystem.map (matrixIntCastLieHom (ZMod 3))).lie_E_F_self i
  rw [rootMatrix_inl, rootMatrix_inr, h, tangentMatrix_apply,
    LinearEquiv.apply_symm_apply, tangentMatrix_corootVector]

/-- Changing the coefficient algebra preserves the normalized coroot differential. -/
-- Match before simplification changes the counit-algebra presentation.
@[simp↓]
theorem mapValue_corootVector {C : Type*} [CommRing C] [Algebra (ZMod 3) C]
    (φ : B →ₐ[ZMod 3] C) (i : Fin 2) :
    Derivation.mapValue φ (corootVector B i) = corootVector C i :=
  MultiplicativeGroup.mapValue_derivationComp_tangentLinearEquiv_symm_one φ (corootCocharacter i)

/-- **Opposite-root bracket normalization over every coefficient algebra.** The positive and
negative root-subgroup differentials at additive tangent parameter one bracket to the
simple-coroot differential at multiplicative tangent parameter one. -/
theorem lie_rootSubgroup_differentials_eq_corootVector (i : Fin 2) :
    ⁅derivationComp (B := B) (CommHopfAlgCat.commonKernelLift generator (.inl (.inl i))).hom
        (AdditiveGroup.gaTangentLinearEquiv.symm (1 : B)),
      derivationComp (B := B) (CommHopfAlgCat.commonKernelLift generator (.inl (.inr i))).hom
        (AdditiveGroup.gaTangentLinearEquiv.symm (1 : B))⁆ = corootVector B i := by
  have h := congrArg (Derivation.mapValue (Algebra.ofId (ZMod 3) B))
    (lie_rootVector_eq_corootVector i)
  rw [Derivation.mapValue_lie, cotangentLinearEquiv_rootVector,
    cotangentLinearEquiv_rootVector,
    AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one,
    AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one,
    mapValue_corootVector] at h
  exact h

/-- The weight-torus differential sends its coordinate tangent basis to the coroot vectors. -/
theorem derivationCompLieHom_weightTorusCoordinateMap_tangentBasis (i : Fin 2) :
    derivationCompLieHom (B := B) weightTorusCoordinateMap.hom
        (SplitTorus.tangentBasis (R := ZMod 3) (B := B) i) = corootVector B i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis, corootVector_def,
    corootCocharacter_def, derivationCompLieHom_apply]

/-- The tangent image of the weight torus is precisely the span of the numbered coroot
vectors, over every coefficient algebra. -/
theorem range_derivationCompLieHom_weightTorusCoordinateMap_eq_span :
    LinearMap.range (derivationCompLieHom (B := B) weightTorusCoordinateMap.hom).toLinearMap =
      Submodule.span B (Set.range (corootVector B)) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [corootVector_def, corootCocharacter_def, derivationCompLieHom_apply]

/-- The numbered coroot differentials are linearly independent, also over nonreduced algebras. -/
theorem linearIndependent_corootVector : LinearIndependent B (corootVector B) := by
  convert SplitTorus.linearIndependent_derivationComp_cocharacter (B := B)
    weightTorusCoordinateMap.hom
    (derivationCompLieHom_injective_of_surjective _ weightTorusCoordinateMap_surjective) using 1
  funext i
  rw [corootVector_def, corootCocharacter_def, derivationCompLieHom_apply]

/-- The coroot differentials form a basis of the toral tangent image, expressed as their span. -/
def corootBasis : Module.Basis (Fin 2) B (Submodule.span B (Set.range (corootVector B))) :=
  Module.Basis.span (linearIndependent_corootVector B)

/-- Including a coroot basis vector into the tangent algebra recovers the numbered coroot
vector. -/
-- Match the subtype coercion before simplification changes its carrier presentation.
@[simp↓]
theorem coe_corootBasis (i : Fin 2) :
    (corootBasis B i :
      Derivation (ZMod 3) carrierAlgebra (Bialgebra.CounitAlgebra (ZMod 3) carrierAlgebra B)) =
        corootVector B i :=
  Module.Basis.coe_span_apply (linearIndependent_corootVector B) i

end

end TauCeti.G2ShortRoot.PrimeField
