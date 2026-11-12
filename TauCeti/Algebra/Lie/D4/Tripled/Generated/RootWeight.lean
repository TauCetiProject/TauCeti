/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.StandardComodule
public import TauCeti.Algebra.Lie.D4.Tripled.Root.Differential

/-!
# Root differentials and adjoint weights of the generated tripled D₄ subgroup

The subgroup of `GL₂₄` generated over a commutative ring by the eight numbered root subgroups
and the weight torus has injective root differentials. Their matrices are the tangent parameter
times the integral tripled raising or lowering matrix. The image of the additive unit tangent
vector defines `TauCeti.D4Tripled.generatedRootVector`. It generates the differential's image
and is nonzero over every nontrivial value algebra, including nonreduced algebras.

When the augmentation cotangent module is projective, these vectors have the integral signed
simple-root characters for the generated weight torus. In particular, all eight characters are
nontrivial adjoint weights over every field in `Type`, including characteristic two. The
differential statements allow arbitrary universes for the base ring and value algebra.

This concerns the subgroup generated over the base ring, not the specialization of the integral
toral closure. It does not identify those groups or either with the independently pinned simply
connected group of type D₄. Nor does it assert that the root lines exhaust the weight spaces,
that the torus is maximal, or that the group has a Borel or a pinning.

The differential and quotient-weight interface follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RootWeight`. The integral matrix normalization and
weight support come from `TauCeti.Algebra.Lie.D4.Tripled.Root.Differential`.

## Main declarations

* `TauCeti.D4Tripled.generatedRootVector`: the normalized numbered root vector.
* `TauCeti.D4Tripled.tangentMatrix_derivationComp_generatedCoordinateLift`: its differential
  matrix over every value algebra.
* `TauCeti.D4Tripled.range_derivationCompLieHom_generatedCoordinateLift_eq_span`: the exact
  root-line image.
* `TauCeti.D4Tripled.generatedRootVector_mem_adjointWeightSpace`: the signed simple-root weight.
* `TauCeti.D4Tripled.weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights`:
  occurrence of all eight signed simple-root characters.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe u v

noncomputable section

section Differential

variable (R : Type u) [CommRing R]

/-- Each numbered root-subgroup coordinate map of the generated subgroup is surjective. -/
theorem generatedCoordinateLift_inl_surjective (k : Fin 4 ⊕ Fin 4) :
    Function.Surjective (generatedCoordinateLift R (.inl k)).hom := by
  apply Function.Surjective.of_comp (g := (generatedCoordinateMap R).hom)
  rw [← BialgHom.coe_comp, ← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl,
    ← coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (rootSubgroupToBaseChangeCoordinateMap_surjective R k).comp
    (coordinateMap_surjective R)

private theorem map_genericMatrix_generatedCoordinateLift (k : Fin 4 ⊕ Fin 4) :
    (GeneralLinear.genericMatrix R 24).map
        ((generatedCoordinateLift R (.inl k)).hom.toAlgHom.comp
          (generatedCoordinateMap R).hom.toAlgHom) =
      1 + SymmetricAlgebra.ι R R 1 •
        (rootMatrix k).map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra R) := by
  apply GeneralLinear.map_genericMatrix_eq_of_pointToGeneralLinear
    ((generatedCoordinateLift R (.inl k)).hom.comp (generatedCoordinateMap R).hom)
  rw [BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    BialgHom.mapDomain_apply (generatedCoordinateLift R (.inl k)).hom,
    pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints R k
      (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R))
      (toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R)))]
  rcases k with i | i
  · rw [coe_rootSubgroupPoints_inl, rootMatrix_inl]
  · rw [coe_rootSubgroupPoints_inr, rootMatrix_inr]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Every numbered root-subgroup differential of the generated group is injective over every
commutative value algebra. -/
theorem derivationComp_generatedCoordinateLift_injective (k : Fin 4 ⊕ Fin 4) :
    Function.Injective (derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom) :=
  derivationComp_injective_of_surjective _ (generatedCoordinateLift_inl_surjective R k)

/-- The differential of a numbered generated root subgroup is its tangent parameter times the
integral tripled root matrix. -/
theorem tangentMatrix_derivationComp_generatedCoordinateLift (k : Fin 4 ⊕ Fin 4)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix 24
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d • (rootMatrix k).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp]
  exact GeneralLinear.tangentMatrix_derivationComp_eq_smul_of_map_genericMatrix _ _
    (map_genericMatrix_generatedCoordinateLift R k) d

/-- The normalized root vector of the generated tripled subgroup, with values in `B`, is the
image of the additive unit tangent vector under its numbered root-subgroup differential. -/
def generatedRootVector (k : Fin 4 ⊕ Fin 4) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) B) :=
  derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- The normalized root vector is the differential at the additive unit tangent vector. -/
theorem generatedRootVector_def (k : Fin 4 ⊕ Fin 4) :
    generatedRootVector (B := B) R k =
      derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1) :=
  (rfl)

/-- A root-subgroup differential is its parameter times the normalized root vector. -/
theorem derivationComp_generatedCoordinateLift_eq_smul_generatedRootVector
    (k : Fin 4 ⊕ Fin 4)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • generatedRootVector (B := B) R k :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- Each numbered root-subgroup differential has precisely its normalized root line as image. -/
theorem range_derivationCompLieHom_generatedCoordinateLift_eq_span (k : Fin 4 ⊕ Fin 4) :
    (derivationCompLieHom (B := B) (generatedCoordinateLift R (.inl k)).hom).range.toSubmodule =
      B ∙ generatedRootVector (B := B) R k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- The matrix of a normalized generated root vector is its integral tripled root matrix. -/
@[simp]
theorem tangentMatrix_generatedRootVector (k : Fin 4 ⊕ Fin 4) :
    GeneralLinear.tangentMatrix 24
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (generatedRootVector (B := B) R k)) =
      (rootMatrix k).map (Int.cast : ℤ → B) := by
  rw [generatedRootVector_def, tangentMatrix_derivationComp_generatedCoordinateLift,
    LinearEquiv.apply_symm_apply, one_smul]

/-- Change of value algebra preserves the normalized generated root vector. -/
@[simp↓]
theorem mapValue_generatedRootVector {C : Type*} [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (k : Fin 4 ⊕ Fin 4) :
    Derivation.mapValue φ (generatedRootVector (B := B) R k) =
      generatedRootVector (B := C) R k :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one φ _

/-- A normalized generated root vector is nonzero over every nontrivial value algebra. -/
theorem generatedRootVector_ne_zero [Nontrivial B] (k : Fin 4 ⊕ Fin 4) :
    generatedRootVector (B := B) R k ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_generatedCoordinateLift_injective (B := B) R k)

end Differential

section Weights

-- The closed-subgroup weight criterion uses the universe of the finite torus index.
variable (R : Type) [CommRing R]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra R))]

/-- A generated tangent vector has character `α` exactly when its matrix is supported on pairs
of tripled weights with difference `α`. -/
theorem mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff
    (α : Multiplicative (Fin 4 →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra R))) :
    x ∈ Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (d4TripledWeight a - d4TripledWeight b) ≠ α →
        GeneralLinear.tangentMatrix 24
          (derivationComp (B := R) (generatedCoordinateMap R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  have hπ := generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap R
  rw [GeneralLinear.weightTorusBaseChangeCoordinateMap_eq] at hπ
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus_of_eq
    (generatedDefiningIdeal R) d4TripledWeight (generatedCoordinateHopfAlgebra_def R)
    (generatedCoordinateMap R) (generatedCoordinateMap_comp_eqToIso_hom R) _ hπ α x

/-- Each normalized generated root vector has its integral signed simple-root character. -/
theorem generatedRootVector_mem_adjointWeightSpace (k : Fin 4 ⊕ Fin 4) :
    (Derivation.cotangentLinearEquiv (B := R)).symm (generatedRootVector (B := R) R k) ∈
      Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 k)) := by
  apply (mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff R _ _).2
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_generatedRootVector, Matrix.map_apply,
    rootMatrix_eq_zero_of_weight_ne k (fun h ↦ hab (congrArg SplitTorus.weightCharacter h)),
    Int.cast_zero]

/-- All eight signed simple-root characters are nontrivial adjoint weights of the generated
tripled subgroup over every nontrivial ring with projective augmentation cotangent module. -/
theorem weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights [Nontrivial R]
    (k : Fin 4 ⊕ Fin 4) :
    SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 k) ∈
      Derivation.nontrivialAdjointWeights (generatedWeightTorusCoordinateMap R).hom := by
  apply Derivation.mem_nontrivialAdjointWeights.mpr
  refine ⟨SplitTorus.weightCharacter_eq_one_iff.not.2
    (TypeDStd.rootGeneratorWeight_ne_zero 4 k), ?_⟩
  · intro hbot
    have hv := generatedRootVector_mem_adjointWeightSpace R k
    rw [hbot, Submodule.mem_bot] at hv
    apply generatedRootVector_ne_zero (B := R) R k
    simpa only [LinearEquiv.map_eq_zero_iff] using hv

end Weights

end

end TauCeti.D4Tripled
