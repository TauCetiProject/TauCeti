/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.IntegralMatrix

/-!
# Root differentials and adjoint weights of the generated type-D spin group

For `4 ≤ n`, the numbered root subgroups of the subgroup generated over the base ring by the
full spin root matrices and weight torus are closed immersions. Their differentials are
injective over every coefficient algebra and send the additive unit tangent vector to the
integral root matrix. The normalized vectors span the differential images and are preserved
by coefficient change.

When the augmentation cotangent module is projective, these vectors have their integral
signed simple-root characters under the generated weight torus. Over a nontrivial ring the
characters are nontrivial adjoint weights. The weight-space results use base rings in `Type`,
as does the closed-subgroup adjoint-weight criterion; the differential results allow
independent universes for the base ring and coefficient algebra.

These are the root-vector normalizations needed to compare root parametrizations with a
pinning. This does not identify root lines with full weight spaces, construct a maximal torus
or a Borel, or identify the generated group with the specialized integral carrier or an
independently pinned simply connected group scheme.

## Main declarations

* `generatedRootVector`: the normalized numbered root differential.
* `tangentMatrix_derivationComp_generatedCoordinateLift`: its matrix over any value algebra.
* `range_derivationCompLieHom_generatedCoordinateLift_eq_span`: its image is the root line.
* `generatedRootVector_mem_adjointWeightSpace`: its signed simple-root character.
* `weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights`: the signed simple
  roots occur as actual nontrivial adjoint weights.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The generated-subgroup differential and weight-space arguments follow
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RootWeight`; the matrix normalization uses
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.IntegralMatrix`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.TypeDSpinCarrier

universe u v

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

section Differential

variable (R : Type u) [CommRing R]

private theorem map_genericMatrix_generatedCoordinateLift (k : Fin n ⊕ Fin n) :
    (GeneralLinear.genericMatrix R (dimension n)).map
        ((generatedCoordinateLift n hn R (.inl k)).hom.toAlgHom.comp
          (generatedCoordinateMap n hn R).hom.toAlgHom) =
      1 + SymmetricAlgebra.ι R R 1 •
        (rootIntMatrix n hn k).map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra R) := by
  apply GeneralLinear.map_genericMatrix_eq_of_pointToGeneralLinear
    ((generatedCoordinateLift n hn R (.inl k)).hom.comp (generatedCoordinateMap n hn R).hom)
  rw [BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    BialgHom.mapDomain_apply (generatedCoordinateLift n hn R (.inl k)).hom,
    pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints n hn R k
      (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R))
      (toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))),
    coe_rootSubgroupPoints_eq_one_add_smul]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Each numbered root-subgroup differential of the generated group is injective over every
commutative coefficient algebra, including nonreduced algebras. -/
theorem derivationComp_generatedCoordinateLift_injective (k : Fin n ⊕ Fin n) :
    Function.Injective
      (derivationComp (B := B) (generatedCoordinateLift n hn R (.inl k)).hom) :=
  derivationComp_injective_of_surjective _ (generatedCoordinateLift_inl_surjective n hn R k)

/-- The differential of a numbered root subgroup, read in the full spin basis, is the additive
tangent parameter times the integral root matrix. -/
theorem tangentMatrix_derivationComp_generatedCoordinateLift (k : Fin n ⊕ Fin n)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (B := B) (generatedCoordinateMap n hn R).hom
          (derivationComp (B := B) (generatedCoordinateLift n hn R (.inl k)).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d • (rootIntMatrix n hn k).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp]
  exact GeneralLinear.tangentMatrix_derivationComp_eq_smul_of_map_genericMatrix _ _
    (map_genericMatrix_generatedCoordinateLift n hn R k) d

/-- The normalized numbered root vector of the generated full spin group, with values in `B`:
the differential of its root subgroup at the additive unit tangent vector. -/
def generatedRootVector (k : Fin n ⊕ Fin n) :
    Derivation R (generatedCoordinateHopfAlgebra n hn R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra n hn R) B) :=
  derivationComp (B := B) (generatedCoordinateLift n hn R (.inl k)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- The normalized root vector is the differential of the numbered root subgroup at parameter
one in the additive tangent space. -/
theorem generatedRootVector_def (k : Fin n ⊕ Fin n) :
    generatedRootVector n hn R (B := B) k =
      derivationComp (B := B) (generatedCoordinateLift n hn R (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1) :=
  (rfl)

/-- A root-subgroup differential is its additive tangent parameter times the normalized vector. -/
theorem derivationComp_generatedCoordinateLift_eq_smul_generatedRootVector
    (k : Fin n ⊕ Fin n)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (generatedCoordinateLift n hn R (.inl k)).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • generatedRootVector n hn R (B := B) k :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- The image of each numbered root-subgroup differential is exactly the normalized root line. -/
theorem range_derivationCompLieHom_generatedCoordinateLift_eq_span (k : Fin n ⊕ Fin n) :
    (derivationCompLieHom (B := B)
        (generatedCoordinateLift n hn R (.inl k)).hom).range.toSubmodule =
      B ∙ generatedRootVector n hn R (B := B) k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- The ambient matrix of a normalized root vector is its integral spin root matrix. -/
@[simp]
theorem tangentMatrix_generatedRootVector (k : Fin n ⊕ Fin n) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (B := B) (generatedCoordinateMap n hn R).hom
          (generatedRootVector n hn R (B := B) k)) =
      (rootIntMatrix n hn k).map (Int.cast : ℤ → B) := by
  rw [generatedRootVector_def, tangentMatrix_derivationComp_generatedCoordinateLift,
    LinearEquiv.apply_symm_apply, one_smul]

/-- Coefficient change preserves the normalization of the generated root vectors. -/
@[simp]
theorem mapValue_generatedRootVector {C : Type*} [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (k : Fin n ⊕ Fin n) :
    Derivation.mapValue φ (generatedRootVector n hn R (B := B) k) =
      generatedRootVector n hn R (B := C) k :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one φ _

/-- A normalized numbered root vector is nonzero over every nontrivial coefficient algebra. -/
theorem generatedRootVector_ne_zero [Nontrivial B] (k : Fin n ⊕ Fin n) :
    generatedRootVector n hn R (B := B) k ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_generatedCoordinateLift_injective n hn R k)

end Differential

section Weights

-- The torus-index universe in the closed-subgroup weight criterion fixes the base universe.
variable (R : Type) [CommRing R]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra n hn R))]

/-- A tangent vector of the generated spin group has weight `α` precisely when its matrix has
no entries at other integral spin-weight differences. -/
theorem mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff
    (α : Multiplicative (Fin n →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra n hn R))) :
    x ∈ Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap n hn R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (basisWeight n a - basisWeight n b) ≠ α →
        GeneralLinear.tangentMatrix (dimension n)
          (derivationComp (B := R) (generatedCoordinateMap n hn R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  have hπ := generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap n hn R
  rw [GeneralLinear.weightTorusBaseChangeCoordinateMap_eq] at hπ
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus_of_eq
    (generatedDefiningIdeal n hn R) (basisWeight n)
    (generatedCoordinateHopfAlgebra_def n hn R) (generatedCoordinateMap n hn R)
    (generatedCoordinateMap_comp_eqToHom n hn R) _ hπ α x

/-- The normalized numbered root differential has its integral signed simple-root character
under the weight torus of the generated spin group. -/
theorem generatedRootVector_mem_adjointWeightSpace (k : Fin n ⊕ Fin n) :
    (Derivation.cotangentLinearEquiv (B := R)).symm
        (generatedRootVector n hn R (B := R) k) ∈
      Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap n hn R).hom
        (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight n k)) := by
  apply (mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff n hn R _ _).2
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_generatedRootVector, Matrix.map_apply,
    rootIntMatrix_eq_zero_of_weight_ne n hn k
      (fun h ↦ hab (congrArg SplitTorus.weightCharacter h)), Int.cast_zero]

/-- Over every nontrivial base ring with projective augmentation cotangent module, each numbered
signed simple-root character is a nontrivial adjoint weight of the generated full spin group. -/
theorem weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights [Nontrivial R]
    (k : Fin n ⊕ Fin n) :
    SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight n k) ∈
      Derivation.nontrivialAdjointWeights (generatedWeightTorusCoordinateMap n hn R).hom := by
  apply Derivation.mem_nontrivialAdjointWeights.mpr
  refine ⟨?_, fun hbot ↦ ?_⟩
  · intro h
    have hdiag := congrArg
      (fun c : Multiplicative (Fin n →₀ ℤ) ↦ Multiplicative.toAdd c (Sum.elim id id k)) h
    simp only [SplitTorus.toAdd_weightCharacter, toAdd_one, Finsupp.zero_apply] at hdiag
    cases k <;> simp [TypeDStd.rootGeneratorWeight_inl, TypeDStd.rootGeneratorWeight_inr,
      CartanMatrix.D_diag] at hdiag
  · have hv := generatedRootVector_mem_adjointWeightSpace n hn R k
    rw [hbot, Submodule.mem_bot] at hv
    apply generatedRootVector_ne_zero n hn R (B := R) k
    simpa only [LinearEquiv.map_eq_zero_iff] using hv

end Weights

end

end TauCeti.TypeDSpinCarrier
