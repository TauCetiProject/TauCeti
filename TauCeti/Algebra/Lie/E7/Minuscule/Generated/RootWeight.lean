/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.E7.Minuscule.ClosedGenerators
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.StandardComodule
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Support
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Coordinates

/-!
# Root vectors and adjoint weights of the generated E₇ subgroup

The subgroup of `GL₅₆` generated over a commutative ring by the fourteen numbered root subgroups
and the weight torus has injective root differentials. Their matrices are the tangent parameter
times the integral raising or lowering matrix. The image of the unit tangent vector defines
`TauCeti.E7Minuscule.generatedRootVector`, a nonzero generator of the corresponding root line
when the ring is nontrivial.

If the augmentation cotangent module is projective, each normalized vector has its signed
simple-root character under the generated weight torus. Over a nontrivial base ring, these
fourteen integral characters are actual nontrivial adjoint weights. The weight-space interface uses
base rings in `Type`;
the differential statements allow arbitrary universes for both the base and value algebra.
In particular the weight statements apply over every field in `Type`, in every characteristic.

These are the normalized numbered root vectors of the generated subgroup. This does not identify
the generated group with the specialized integral carrier, prove maximality of its torus,
construct a Borel, or identify a root line with a full weight space.

The differential and quotient-weight arguments follow the generated E₆ construction in
`TauCeti.Algebra.Lie.E6.Minuscule.Generated.RootWeight`. The matrix support argument uses the
generic minuscule weight-table criterion; symmetry of the E₇ Cartan matrix converts its column
convention to the row convention for the numbered root characters.

## Main declarations

* `TauCeti.E7Minuscule.generatedRootVector`: the normalized numbered root vector.
* `TauCeti.E7Minuscule.tangentMatrix_derivationComp_generatedCoordinateLift`: the differential
  matrix over every value algebra.
* `TauCeti.E7Minuscule.range_derivationCompLieHom_generatedCoordinateLift_eq_span`: its image
  is the normalized root line.
* `TauCeti.E7Minuscule.generatedRootVector_mem_adjointWeightSpace`: its signed root character.
* `TauCeti.E7Minuscule.weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights`:
  the fourteen signed simple roots are actual nontrivial adjoint weights.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

universe u v

noncomputable section

/-! ## The numbered root differentials -/

section Differential

variable (R : Type u) [CommRing R]

/-- The numbered root-subgroup coordinate maps of the generated subgroup are surjective, so the
root subgroups are closed subgroups of it. -/
theorem generatedCoordinateLift_inl_surjective (k : Fin 7 ⊕ Fin 7) :
    Function.Surjective (generatedCoordinateLift R (.inl k)).hom := by
  have h : Function.Surjective
      (generatedCoordinateMap R ≫ generatedCoordinateLift R (.inl k)).hom := by
    rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl,
      ← coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap,
      _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact (rootSubgroupToBaseChangeCoordinateMap_surjective R k).comp
      (coordinateMap_surjective R)
  rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at h
  exact Function.Surjective.of_comp h

/-- The generic matrix of `GL₅₆`, restricted to the `k`th numbered root subgroup, is
`1 + t X_k` for the coordinate `t` of `𝔾ₐ` and the integral raising or lowering matrix `X_k`. -/
private theorem map_genericMatrix_generatedCoordinateLift (k : Fin 7 ⊕ Fin 7) :
    (GeneralLinear.genericMatrix R 56).map
        ((generatedCoordinateLift R (.inl k)).hom.toAlgHom.comp
          (generatedCoordinateMap R).hom.toAlgHom) =
      1 + SymmetricAlgebra.ι R R 1 •
        (Sum.elim raisingMatrix loweringMatrix k).map
          (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra R) := by
  let A := CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)
  let q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A :=
    toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))
  have hu : AdditiveGroup.gaPointsMulEquiv (R := R) q =
      Multiplicative.ofAdd (SymmetricAlgebra.ι R R 1) := by
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) q),
      AdditiveGroup.toAdd_gaPointsMulEquiv]
    simp [q]
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 56) A =>
    (g : Matrix (Fin 56) (Fin 56) A))
    (pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints R k A q)
  rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    BialgHom.mapDomain_apply] at h
  simp only [q, AlgHom.id_comp] at h
  rw [h, hu]
  rcases k with i | i
  · rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, Sum.elim_inl]
  · rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, Sum.elim_inr]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Each numbered root-subgroup differential of the generated subgroup is injective, with
coefficients in every commutative algebra, including nonreduced ones. -/
theorem derivationComp_generatedCoordinateLift_injective (k : Fin 7 ⊕ Fin 7) :
    Function.Injective (derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom) :=
  derivationComp_injective_of_surjective _ (generatedCoordinateLift_inl_surjective R k)

/-- **The differential of a numbered root subgroup of the generated subgroup.** In the minuscule
basis, the tangent vector obtained by differentiating the `k`th root subgroup along a tangent
vector of `𝔾ₐ` is its parameter times the integral raising or lowering matrix. -/
theorem tangentMatrix_derivationComp_generatedCoordinateLift (k : Fin 7 ⊕ Fin 7)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix 56
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d •
        (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp]
  exact GeneralLinear.tangentMatrix_derivationComp_eq_smul_of_map_genericMatrix _ _
    (map_genericMatrix_generatedCoordinateLift R k) d

/-- The normalized tangent vector of the `k`th numbered root subgroup of the generated
subgroup: the image of the unit tangent vector of `𝔾ₐ`. -/
def generatedRootVector (k : Fin 7 ⊕ Fin 7) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) :=
  derivationComp (B := R) (generatedCoordinateLift R (.inl k)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1)

/-- The normalized root vector is the differential of the root subgroup at the unit tangent
vector of `𝔾ₐ`. -/
theorem generatedRootVector_def (k : Fin 7 ⊕ Fin 7) :
    generatedRootVector R k =
      derivationComp (B := R) (generatedCoordinateLift R (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1) :=
  (rfl)

/-- The differential of the `k`th root subgroup along a tangent vector of `𝔾ₐ` is its parameter
times the normalized root vector. -/
theorem derivationComp_generatedCoordinateLift_eq_smul_generatedRootVector
    (k : Fin 7 ⊕ Fin 7)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) R)) :
    derivationComp (B := R) (generatedCoordinateLift R (.inl k)).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • generatedRootVector R k :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- Each numbered root-subgroup differential of the generated subgroup has precisely the
normalized root line as its image. -/
theorem range_derivationCompLieHom_generatedCoordinateLift_eq_span (k : Fin 7 ⊕ Fin 7) :
    (derivationCompLieHom (B := R) (generatedCoordinateLift R (.inl k)).hom).range.toSubmodule =
      R ∙ generatedRootVector R k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span R _

/-- The matrix of a normalized root vector is its integral raising or lowering matrix. -/
@[simp]
theorem tangentMatrix_generatedRootVector (k : Fin 7 ⊕ Fin 7) :
    GeneralLinear.tangentMatrix 56
        (derivationComp (B := R) (generatedCoordinateMap R).hom (generatedRootVector R k)) =
      (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → R) := by
  rw [generatedRootVector_def, tangentMatrix_derivationComp_generatedCoordinateLift,
    LinearEquiv.apply_symm_apply, one_smul]

/-- A normalized root vector is nonzero over every nontrivial commutative ring. -/
theorem generatedRootVector_ne_zero [Nontrivial R] (k : Fin 7 ⊕ Fin 7) :
    generatedRootVector R k ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_generatedCoordinateLift_injective (B := R) R k)

end Differential

/-! ## Adjoint weights -/

section Weights

-- The closed-subgroup weight criterion takes the base ring in the universe of the torus index.
variable (R : Type) [CommRing R]

variable [Module.Projective R
  (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra R))]

/-- **The entrywise criterion for the adjoint weight spaces of the generated subgroup.** A tangent
vector has weight `α` for the weight torus exactly when its matrix vanishes at every entry
`(a, b)` whose minuscule weight difference is a different character. -/
theorem mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff
    (α : Multiplicative (Fin 7 →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra R))) :
    x ∈ Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (e7MinusculeWeight a - e7MinusculeWeight b) ≠ α →
        GeneralLinear.tangentMatrix 56
          (derivationComp (B := R) (generatedCoordinateMap R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  have hπ := generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap R
  rw [GeneralLinear.weightTorusBaseChangeCoordinateMap_eq] at hπ
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus_of_eq
    (generatedDefiningIdeal R) e7MinusculeWeight (generatedCoordinateHopfAlgebra_def R)
    (generatedCoordinateMap R) (generatedCoordinateMap_comp_eqToIso_hom R) _ hπ α x

/-- **Each normalized root vector has its signed simple-root character.** The tangent vector of
the `k`th numbered root subgroup lies in the adjoint weight space of
`TauCeti.DynkinType.E7.rootGeneratorWeight valid_E7 k` for the weight torus of the generated
subgroup. -/
theorem generatedRootVector_mem_adjointWeightSpace (k : Fin 7 ⊕ Fin 7) :
    (Derivation.cotangentLinearEquiv (B := R)).symm (generatedRootVector R k) ∈
      Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.weightCharacter (E7.rootGeneratorWeight valid_E7 k)) := by
  apply (mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff R _ _).2
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_generatedRootVector, Matrix.map_apply,
    rootMatrix_apply_eq_zero_of_weight_sub_ne k a b
      (fun h ↦ hab (congrArg SplitTorus.weightCharacter h)), Int.cast_zero]

/-- **The fourteen signed simple roots are nontrivial adjoint weights of the generated subgroup.**
Over every nontrivial ring with projective augmentation cotangent module, in particular over
every field, the adjoint weight space of each signed simple-root character contains the nonzero
normalized root vector. -/
theorem weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights [Nontrivial R]
    (k : Fin 7 ⊕ Fin 7) :
    SplitTorus.weightCharacter (E7.rootGeneratorWeight valid_E7 k) ∈
      Derivation.nontrivialAdjointWeights (generatedWeightTorusCoordinateMap R).hom := by
  apply Derivation.mem_nontrivialAdjointWeights.mpr
  refine ⟨SplitTorus.weightCharacter_eq_one_iff.not.2 (rootGeneratorWeight_ne_zero k),
    fun hbot ↦ ?_⟩
  have hz := generatedRootVector_mem_adjointWeightSpace R k
  have hz' : (Derivation.cotangentLinearEquiv (B := R)).symm (generatedRootVector R k) ∈
      (⊥ : Submodule R _) := hbot ▸ hz
  apply generatedRootVector_ne_zero R k
  simpa only [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] using hz'

end Weights

end

end TauCeti.E7Minuscule
