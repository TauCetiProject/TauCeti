/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Generated.StandardComodule
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Root.Differential

/-!
# Root differentials and adjoint weights of the generated Geck subgroup

For a valid Dynkin type, the numbered positive and negative root subgroups of the subgroup
generated over a commutative ring by Geck's root subgroups and weight torus are closed copies of
`𝔾ₐ`. Their differentials are injective over every value algebra, including nonreduced ones.
The image of the unit additive tangent vector is the normalized root vector
`TauCeti.DynkinType.geckGeneratedRootVector`. Its matrix is the integral Geck root matrix,
and its differential image is exactly the line it spans. Coefficient change preserves it.

With projective augmentation cotangent module, these vectors have the integral signed
simple-root characters for the generated weight torus. Over a nontrivial ring those characters
are actual nontrivial adjoint weights. The weight-space statements use base rings in `Type`;
the differential statements allow independently sized base and value algebras.

No assertion of torus maximality, exhaustion of weight spaces by these lines, or existence of
a Borel is made. The generated subgroup is not identified with the specialized integral carrier
or with an independently pinned simply connected group. In particular the full-weight torus
need not embed for every Dynkin type; the weight statements concern its specified morphism.

The construction follows the generated E₇ root-vector interface in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RootWeight`. The matrix normalization and weight
support use the integral Geck root vectors, rather than a new matrix calculation.

## Main declarations

* `TauCeti.DynkinType.geckGeneratedRootVector`: the normalized root differential.
* `TauCeti.DynkinType.tangentMatrix_geckGeneratedRootVector`: its integral matrix.
* `TauCeti.DynkinType.range_derivationCompLieHom_geckGeneratedCoordinateLift_eq_span`:
  the exact image of a numbered root differential.
* `TauCeti.DynkinType.geckGeneratedRootVector_mem_adjointWeightSpace`: its root character.
* `TauCeti.DynkinType.rootGeneratorWeight_mem_nontrivialAdjointWeights_geckGeneratedWeightTorus`:
  every signed simple root occurs as a nontrivial adjoint weight.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

universe u v

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

section Differential

variable (R : Type u) [CommRing R]

/-- The numbered root subgroups of the generated Geck subgroup are closed copies of `𝔾ₐ`. -/
theorem geckGeneratedCoordinateLift_inl_surjective (i : Fin t.rank ⊕ Fin t.rank) :
    Function.Surjective (t.geckGeneratedCoordinateLift ht R (.inl i)).hom := by
  have h : Function.Surjective
      (t.geckGeneratedCoordinateMap ht R ≫ t.geckGeneratedCoordinateLift ht R (.inl i)).hom := by
    rw [geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateLift,
      geckGeneratorCoordinateMap_inl,
      ← mkQuotient_comp_geckRootSubgroupToBaseChangeCoordinateMap,
      _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact (t.geckRootSubgroupToBaseChangeCoordinateMap_surjective ht R i).comp
      (CommHopfAlgCat.mkQuotient_surjective _ _)
  rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at h
  exact Function.Surjective.of_comp h

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Each numbered root differential is injective with values in every commutative algebra. -/
theorem derivationComp_geckGeneratedCoordinateLift_injective (i : Fin t.rank ⊕ Fin t.rank) :
    Function.Injective (derivationComp (B := B)
      (t.geckGeneratedCoordinateLift ht R (.inl i)).hom) :=
  derivationComp_injective_of_surjective _ (t.geckGeneratedCoordinateLift_inl_surjective ht R i)

/-- The normalized root vector of the generated Geck subgroup, with values in `B`, is the
image of the unit tangent vector of its numbered additive root subgroup. -/
def geckGeneratedRootVector (i : Fin t.rank ⊕ Fin t.rank) :
    Derivation R (t.geckGeneratedCoordinateHopfAlgebra ht R)
      (Bialgebra.CounitAlgebra R (t.geckGeneratedCoordinateHopfAlgebra ht R) B) :=
  derivationComp (B := B) (t.geckGeneratedCoordinateLift ht R (.inl i)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- A normalized root vector is the root-subgroup differential at the unit additive tangent. -/
theorem geckGeneratedRootVector_def (i : Fin t.rank ⊕ Fin t.rank) :
    t.geckGeneratedRootVector ht R (B := B) i =
      derivationComp (B := B) (t.geckGeneratedCoordinateLift ht R (.inl i)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1) :=
  (rfl)

/-- Coefficient change preserves the normalized root vector of the generated subgroup. -/
@[simp]
theorem mapValue_geckGeneratedRootVector {C : Type*} [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (i : Fin t.rank ⊕ Fin t.rank) :
    Derivation.mapValue φ (t.geckGeneratedRootVector ht R (B := B) i) =
      t.geckGeneratedRootVector ht R (B := C) i :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one φ _

/-- The root differential sends an additive tangent to its parameter times the normalized
root vector. -/
theorem derivationComp_geckGeneratedCoordinateLift_eq_smul_geckGeneratedRootVector
    (i : Fin t.rank ⊕ Fin t.rank)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (t.geckGeneratedCoordinateLift ht R (.inl i)).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • t.geckGeneratedRootVector ht R (B := B) i :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- Each root differential has precisely its normalized root line as image. -/
theorem range_derivationCompLieHom_geckGeneratedCoordinateLift_eq_span
    (i : Fin t.rank ⊕ Fin t.rank) :
    (derivationCompLieHom (B := B)
        (t.geckGeneratedCoordinateLift ht R (.inl i)).hom).range.toSubmodule =
      B ∙ t.geckGeneratedRootVector ht R (B := B) i :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- A normalized root vector is nonzero over every nontrivial value algebra. -/
theorem geckGeneratedRootVector_ne_zero [Nontrivial B] (i : Fin t.rank ⊕ Fin t.rank) :
    t.geckGeneratedRootVector ht R (B := B) i ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (t.derivationComp_geckGeneratedCoordinateLift_injective ht R i)

/-- The matrix of a numbered root differential is its tangent parameter times the integral
Geck root matrix. -/
theorem tangentMatrix_derivationComp_geckGeneratedCoordinateLift (i : Fin t.rank ⊕ Fin t.rank)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix (t.geckDim ht)
        (derivationComp (B := B) (t.geckGeneratedCoordinateMap ht R).hom
          (derivationComp (B := B) (t.geckGeneratedCoordinateLift ht R (.inl i)).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d •
        (t.geckRootIntMatrix ht i).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp, ← _root_.CommHopfAlgCat.hom_comp,
    geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateLift,
    geckGeneratorCoordinateMap_inl,
    tangentMatrix_derivationComp_geckRootSubgroupBaseChangeCoordinateMap]

/-- The matrix of a normalized root vector is the integral Geck root matrix, over every
commutative value algebra. -/
@[simp]
theorem tangentMatrix_geckGeneratedRootVector (i : Fin t.rank ⊕ Fin t.rank) :
    GeneralLinear.tangentMatrix (t.geckDim ht)
        (derivationComp (B := B) (t.geckGeneratedCoordinateMap ht R).hom
          (t.geckGeneratedRootVector ht R (B := B) i)) =
      (t.geckRootIntMatrix ht i).map (Int.cast : ℤ → B) := by
  rw [geckGeneratedRootVector_def, tangentMatrix_derivationComp_geckGeneratedCoordinateLift,
    LinearEquiv.apply_symm_apply, one_smul]

end Differential

section Weights

-- The closed-subgroup weight criterion uses a base ring in the universe of the torus index.
variable (R : Type) [CommRing R]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (t.geckGeneratedCoordinateHopfAlgebra ht R))]

/-- A generated Geck tangent vector has character `α` exactly when its matrix has support
only at coordinate pairs with Geck weight difference `α`. -/
theorem mem_adjointWeightSpace_geckGeneratedWeightTorus_iff
    (α : Multiplicative (Fin t.rank →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R
      (t.geckGeneratedCoordinateHopfAlgebra ht R))) :
    x ∈ Derivation.adjointWeightSpace (t.geckGeneratedWeightTorusCoordinateMap ht R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (t.geckWeightFin ht a - t.geckWeightFin ht b) ≠ α →
        GeneralLinear.tangentMatrix (t.geckDim ht)
          (derivationComp (B := R) (t.geckGeneratedCoordinateMap ht R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  have hπ := t.geckGeneratedCoordinateMap_comp_geckGeneratedWeightTorusCoordinateMap ht R
  rw [GeneralLinear.weightTorusBaseChangeCoordinateMap_eq] at hπ
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus_of_eq
    (t.geckGeneratedDefiningIdeal ht R) (t.geckWeightFin ht)
    (t.geckGeneratedCoordinateHopfAlgebra_def ht R) (t.geckGeneratedCoordinateMap ht R)
    (by rw [geckGeneratedCoordinateMap_def]; simp) _ hπ α x

/-- Each normalized generated root vector has its integral signed simple-root character. -/
theorem geckGeneratedRootVector_mem_adjointWeightSpace (i : Fin t.rank ⊕ Fin t.rank) :
    (Derivation.cotangentLinearEquiv (B := R)).symm
        (t.geckGeneratedRootVector ht R (B := R) i) ∈
      Derivation.adjointWeightSpace (t.geckGeneratedWeightTorusCoordinateMap ht R).hom
        (SplitTorus.weightCharacter (t.rootGeneratorWeight ht i)) := by
  apply (t.mem_adjointWeightSpace_geckGeneratedWeightTorus_iff ht R _ _).2
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_geckGeneratedRootVector, Matrix.map_apply,
    geckRootIntMatrix_eq_zero_of_weight_ne t ht i
      (fun h ↦ hab (congrArg SplitTorus.weightCharacter h)), Int.cast_zero]

/-- Every numbered signed simple root is a nontrivial adjoint weight of the generated subgroup
over a nontrivial base ring with projective augmentation cotangent module. -/
theorem rootGeneratorWeight_mem_nontrivialAdjointWeights_geckGeneratedWeightTorus [Nontrivial R]
    (i : Fin t.rank ⊕ Fin t.rank) :
    SplitTorus.weightCharacter (t.rootGeneratorWeight ht i) ∈
      Derivation.nontrivialAdjointWeights (t.geckGeneratedWeightTorusCoordinateMap ht R).hom := by
  have hα : t.rootGeneratorWeight ht i ≠ 0 := by
    intro h
    have hdiag := congrFun h (Sum.elim id id i)
    cases i <;> simp at hdiag
  apply Derivation.mem_nontrivialAdjointWeights.mpr
  refine ⟨SplitTorus.weightCharacter_eq_one_iff.not.2 hα, fun hbot ↦ ?_⟩
  have hz := t.geckGeneratedRootVector_mem_adjointWeightSpace ht R i
  have hz' : (Derivation.cotangentLinearEquiv (B := R)).symm
      (t.geckGeneratedRootVector ht R (B := R) i) ∈ (⊥ : Submodule R _) := hbot ▸ hz
  apply t.geckGeneratedRootVector_ne_zero ht R (B := R) i
  simpa only [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] using hz'

end Weights

end

end TauCeti.DynkinType
