/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.ClosedRootSubgroup
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.StandardComodule

/-!
# Root vectors and adjoint weights of the generated doubled E₆ subgroup

The subgroup of `GL₅₄` generated over a commutative ring by the twelve numbered root subgroups
and weight torus has injective root differentials. Their matrices are the additive tangent
parameter times `rootIntMatrix`, in the carrier's `Fin 54` coordinates. The image of the unit
tangent vector defines `generatedRootVector`. Each differential has the normalized root line
as its image, and change of value algebra preserves the normalization, including for nonreduced
algebras.

Over a nontrivial base ring with projective augmentation cotangent module, each signed
simple-root character is a nontrivial adjoint weight. In particular these statements apply
over every field, including characteristics two and three. The weight labels are
integral characters, not Lie eigenvalues reduced modulo the characteristic.

These vectors give the differential and weight normalization of the numbered root subgroups.
They do not identify the root lines with entire weight spaces, prove maximality of the torus,
or construct a Borel. The subgroup generated over the base ring is not identified with the
specialized integral carrier or with an independently pinned simply connected E₆ group scheme.

The construction follows `TauCeti.Algebra.Lie.E6.Minuscule.Generated.RootWeight` and
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RootWeight`, using the doubled carrier's integral
root matrices and their existing weight-support theorem. The generic additive differential
and closed-subgroup adjoint-weight criteria supply the line and weight-space calculations.

## Main declarations

* `generatedRootVector`: the normalized numbered root differential with arbitrary value algebra.
* `tangentMatrix_derivationComp_generatedCoordinateLift`: its matrix formula.
* `range_derivationCompLieHom_generatedCoordinateLift_eq_span`: its image is a root line.
* `generatedRootVector_mem_adjointWeightSpace`: its signed simple-root character.
* `weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights`: occurrence of all twelve
  signed simple roots as actual nontrivial adjoint weights.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.E6DoubledMinuscule

universe u v

noncomputable section

section Differential

variable (R : Type u) [CommRing R]

/-- Each numbered root subgroup is a closed copy of the additive group in the generated group. -/
theorem generatedCoordinateLift_inl_surjective (k : Fin 6 ⊕ Fin 6) :
    Function.Surjective (generatedCoordinateLift R (.inl k)).hom := by
  have h : Function.Surjective
      (generatedCoordinateMap R ≫ generatedCoordinateLift R (.inl k)).hom := by
    rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inl,
      ← mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap,
      _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact (rootSubgroupToBaseChangeCoordinateMap_surjective R k).comp
      (CommHopfAlgCat.mkQuotient_surjective _ _)
  rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at h
  exact Function.Surjective.of_comp h

private theorem map_genericMatrix_generatedCoordinateLift (k : Fin 6 ⊕ Fin 6) :
    (GeneralLinear.genericMatrix R 54).map
        ((generatedCoordinateLift R (.inl k)).hom.toAlgHom.comp
          (generatedCoordinateMap R).hom.toAlgHom) =
      1 + SymmetricAlgebra.ι R R 1 •
        (rootIntMatrix k).map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra R) := by
  apply GeneralLinear.map_genericMatrix_eq_of_pointToGeneralLinear
    ((generatedCoordinateLift R (.inl k)).hom.comp (generatedCoordinateMap R).hom)
  rw [BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    BialgHom.mapDomain_apply (generatedCoordinateLift R (.inl k)).hom,
    pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints R k
      (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R))
      (toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))),
    coe_rootSubgroupPoints_eq_one_add_smul]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Each numbered root differential is injective with values in every commutative algebra. -/
theorem derivationComp_generatedCoordinateLift_injective (k : Fin 6 ⊕ Fin 6) :
    Function.Injective (derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom) :=
  derivationComp_injective_of_surjective _ (generatedCoordinateLift_inl_surjective R k)

/-- The differential of a numbered root subgroup is its tangent parameter times the integral
root matrix in the doubled minuscule basis. -/
theorem tangentMatrix_derivationComp_generatedCoordinateLift (k : Fin 6 ⊕ Fin 6)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix 54
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d • (rootIntMatrix k).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp]
  exact GeneralLinear.tangentMatrix_derivationComp_eq_smul_of_map_genericMatrix _ _
    (map_genericMatrix_generatedCoordinateLift R k) d

/-- The normalized root vector is the differential of the numbered root subgroup at the
additive unit tangent vector, with values in `B`. -/
def generatedRootVector (k : Fin 6 ⊕ Fin 6) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) B) :=
  derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- The defining normalization of a numbered root vector. -/
theorem generatedRootVector_def (k : Fin 6 ⊕ Fin 6) :
    generatedRootVector (B := B) R k =
      derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1) :=
  (rfl)

/-- The root differential with parameter `c` is `c` times the normalized root vector. -/
theorem derivationComp_generatedCoordinateLift_eq_smul_generatedRootVector
    (k : Fin 6 ⊕ Fin 6)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (generatedCoordinateLift R (.inl k)).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • generatedRootVector (B := B) R k :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- Each numbered root differential has exactly the normalized root line as its image. -/
theorem range_derivationCompLieHom_generatedCoordinateLift_eq_span (k : Fin 6 ⊕ Fin 6) :
    (derivationCompLieHom (B := B) (generatedCoordinateLift R (.inl k)).hom).range.toSubmodule =
      B ∙ generatedRootVector (B := B) R k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- The matrix of a normalized root vector is its integral represented root matrix. -/
@[simp]
theorem tangentMatrix_generatedRootVector (k : Fin 6 ⊕ Fin 6) :
    GeneralLinear.tangentMatrix 54
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (generatedRootVector (B := B) R k)) =
      (rootIntMatrix k).map (Int.cast : ℤ → B) := by
  rw [generatedRootVector_def, tangentMatrix_derivationComp_generatedCoordinateLift,
    LinearEquiv.apply_symm_apply, one_smul]

/-- Change of value algebra preserves the normalization of each root vector. -/
@[simp]
theorem mapValue_generatedRootVector {C : Type*} [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (k : Fin 6 ⊕ Fin 6) :
    Derivation.mapValue φ (generatedRootVector (B := B) R k) =
      generatedRootVector (B := C) R k :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one φ _

/-- Every normalized root vector is nonzero over a nontrivial value algebra. -/
theorem generatedRootVector_ne_zero [Nontrivial B] (k : Fin 6 ⊕ Fin 6) :
    generatedRootVector (B := B) R k ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_generatedCoordinateLift_injective (B := B) R k)

end Differential

section Weights

variable (R : Type u) [CommRing R]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra R))]

/-- An adjoint weight vector has matrix entries only at the corresponding integral differences
of the doubled minuscule weights. -/
theorem mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff
    (α : Multiplicative (Fin 6 →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra R))) :
    x ∈ Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (matrixWeight a - matrixWeight b) ≠ α →
        GeneralLinear.tangentMatrix 54
          (derivationComp (B := R) (generatedCoordinateMap R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  have hG := generatedCoordinateHopfAlgebra_def R
  have hq := generatedCoordinateMap_comp_eqToIso_hom R
  have hπ := generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap R
  -- Abstract the named presentation and its finiteness proof before transporting to the quotient.
  generalize_proofs at *
  generalize generatedCoordinateMap R = q at *
  generalize generatedWeightTorusCoordinateMap R = π at *
  generalize generatedCoordinateHopfAlgebra R = G at *
  subst G
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id] at hq
  rw [hq] at hπ ⊢
  rw [CommHopfAlgCat.hom_mkQuotient]
  have hπ' : π.hom.comp (Bialgebra.Quotient.mkBialgHom (generatedDefiningIdeal R).toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← _root_.CommHopfAlgCat.hom_comp, hπ,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  simpa only [HopfIdeal.quotientLieHom_apply] using
    HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorusCoordinateBialgHom
      (generatedDefiningIdeal R) matrixWeight π.hom hπ' α x

/-- Each normalized numbered root vector has its signed simple-root character for the
weight torus of the generated subgroup. -/
theorem generatedRootVector_mem_adjointWeightSpace (k : Fin 6 ⊕ Fin 6) :
    (Derivation.cotangentLinearEquiv (B := R)).symm (generatedRootVector (B := R) R k) ∈
      Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.weightCharacter (E6.rootGeneratorWeight k)) := by
  rw [mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff]
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_generatedRootVector, Matrix.map_apply,
    rootIntMatrix_eq_zero_of_weight_ne k (fun h ↦ hab (congrArg _ h)), Int.cast_zero]

/-- All twelve signed simple-root characters are actual nontrivial adjoint weights over every
nontrivial base ring with projective augmentation cotangent module, in particular every field. -/
theorem weightCharacter_rootGeneratorWeight_mem_nontrivialAdjointWeights [Nontrivial R]
    (k : Fin 6 ⊕ Fin 6) :
    SplitTorus.weightCharacter (E6.rootGeneratorWeight k) ∈
      Derivation.nontrivialAdjointWeights (generatedWeightTorusCoordinateMap R).hom := by
  refine Derivation.mem_nontrivialAdjointWeights.2
    ⟨SplitTorus.weightCharacter_eq_one_iff.not.2 (E6.rootGeneratorWeight_ne_zero k),
      fun hbot ↦ ?_⟩
  have hz := generatedRootVector_mem_adjointWeightSpace R k
  rw [hbot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at hz
  exact generatedRootVector_ne_zero (B := R) R k hz

end Weights

end

end TauCeti.E6DoubledMinuscule
