/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.StandardComodule

/-!
# Root vectors and adjoint weights of the generated type-B spin subgroup

The subgroup of `GL_(2^(n+1))` generated over a commutative ring by the numbered type-`Bₙ₊₁`
spin root subgroups and weight torus has injective root differentials. In the spin weight basis,
their matrices are the additive tangent parameter times the integral root matrix. The image of
the unit tangent vector is the normalized root vector, and spans the differential's image over
every value algebra, including nonreduced algebras. Coefficient change preserves this normalization.

When the augmentation cotangent module is projective, each normalized vector has its integral
signed simple-root character for the generated weight torus. Over a nontrivial base these
characters occur as nontrivial adjoint weights, including in characteristic two. The comodule
weight criterion takes the base in `Type`; differential statements allow independently sized
base and value algebras.

This does not identify a root line with a full weight space, prove maximality of the torus,
or construct a Borel. The generated subgroup is not identified with the specialized integral
carrier or with an independently pinned simply connected group scheme of type `Bₙ₊₁`.

The differential and quotient-weight arguments adapt
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RootWeight`. The spin matrix and integral-character
normalizations are those of
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix` and
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Root.Weights`.

## Main declarations

* `TauCeti.TypeBSpinCarrier.generatedRootVector`: the normalized numbered root differential.
* `TauCeti.TypeBSpinCarrier.tangentMatrix_derivationComp_generatedCoordinateLift`: its matrix
  over every value algebra.
* `TauCeti.TypeBSpinCarrier.range_derivationCompLieHom_generatedCoordinateLift_eq_span`: the
  differential's image is the normalized root line.
* `TauCeti.TypeBSpinCarrier.generatedRootVector_mem_adjointWeightSpace`: the signed root character.
* `TauCeti.TypeBSpinCarrier.rootGeneratorWeight_mem_generatedNontrivialAdjointWeights`: the signed
  simple-root characters are actual nontrivial adjoint weights.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.TypeBSpinCarrier

universe u v

noncomputable section

variable (n : ℕ)

section Differential

variable (R : Type u) [CommRing R]

private theorem map_genericMatrix_generatedCoordinateLift (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (GeneralLinear.genericMatrix R (dimension n)).map
        ((generatedCoordinateLift n R (.inl k)).hom.toAlgHom.comp
          (generatedCoordinateMap n R).hom.toAlgHom) =
      1 + SymmetricAlgebra.ι R R 1 •
        (rootIntMatrix n k).map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra R) := by
  let A := CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)
  let q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A :=
    toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))
  have hu : AdditiveGroup.gaPointsMulEquiv (R := R) q =
      Multiplicative.ofAdd (SymmetricAlgebra.ι R R 1) := by
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) q),
      AdditiveGroup.toAdd_gaPointsMulEquiv]
    simp [q]
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (dimension n)) A =>
    (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A))
    (pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints n R k q)
  rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    BialgHom.mapDomain_apply] at h
  simp only [q, AlgHom.id_comp] at h
  rw [h, hu, coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Every numbered root differential of the generated subgroup is injective, with values in
any commutative algebra. -/
theorem derivationComp_generatedCoordinateLift_injective (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Function.Injective (derivationComp (B := B) (generatedCoordinateLift n R (.inl k)).hom) :=
  derivationComp_injective_of_surjective _ (generatedCoordinateLift_inl_surjective n R k)

/-- The matrix of a numbered root differential is the additive tangent parameter times its
integral spin root matrix. -/
theorem tangentMatrix_derivationComp_generatedCoordinateLift (k : Fin (n + 1) ⊕ Fin (n + 1))
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (B := B) (generatedCoordinateMap n R).hom
          (derivationComp (B := B) (generatedCoordinateLift n R (.inl k)).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d • (rootIntMatrix n k).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp]
  exact GeneralLinear.tangentMatrix_derivationComp_eq_smul_of_map_genericMatrix _ _
    (map_genericMatrix_generatedCoordinateLift n R k) d

/-- The normalized numbered root vector of the generated subgroup, with values in `B`: the
image of the unit tangent vector of the additive group. -/
def generatedRootVector (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Derivation R (generatedCoordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra n R) B) :=
  derivationComp (B := B) (generatedCoordinateLift n R (.inl k)).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- The normalized root vector is the differential at the additive unit tangent vector. -/
theorem generatedRootVector_def (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    generatedRootVector n R (B := B) k =
      derivationComp (B := B) (generatedCoordinateLift n R (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1) :=
  (rfl)

/-- A numbered root differential is its additive parameter times the normalized root vector. -/
theorem derivationComp_generatedCoordinateLift_eq_smul_generatedRootVector
    (k : Fin (n + 1) ⊕ Fin (n + 1))
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (generatedCoordinateLift n R (.inl k)).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • generatedRootVector n R (B := B) k :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- The image of each root differential is precisely its normalized root line. -/
theorem range_derivationCompLieHom_generatedCoordinateLift_eq_span
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (derivationCompLieHom (B := B) (generatedCoordinateLift n R (.inl k)).hom).range.toSubmodule =
      B ∙ generatedRootVector n R (B := B) k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- The matrix of a normalized root vector is its integral spin root matrix. -/
@[simp]
theorem tangentMatrix_generatedRootVector (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (B := B) (generatedCoordinateMap n R).hom
          (generatedRootVector n R (B := B) k)) =
      (rootIntMatrix n k).map (Int.cast : ℤ → B) := by
  rw [generatedRootVector_def, tangentMatrix_derivationComp_generatedCoordinateLift,
    LinearEquiv.apply_symm_apply, one_smul]

/-- Changing the value algebra preserves normalized root vectors. -/
@[simp]
theorem mapValue_generatedRootVector {C : Type*} [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Derivation.mapValue φ (generatedRootVector n R (B := B) k) =
      generatedRootVector n R (B := C) k :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one φ _

/-- A normalized root vector is nonzero over every nontrivial value algebra. -/
theorem generatedRootVector_ne_zero [Nontrivial B] (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    generatedRootVector n R (B := B) k ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_generatedCoordinateLift_injective n R (B := B) k)

end Differential

section Weights

-- The closed-subgroup weight criterion takes the base in the universe of the torus index.
variable (R : Type) [CommRing R]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra n R))]

/-- A tangent vector has adjoint weight `α` exactly when its matrix is supported at spin weight
differences equal to `α`. This does not assert that a root line is the entire weight space. -/
theorem mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff
    (α : Multiplicative (Fin (n + 1) →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (generatedCoordinateHopfAlgebra n R))) :
    x ∈ Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap n R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (basisWeight n a - basisWeight n b) ≠ α →
        GeneralLinear.tangentMatrix (dimension n)
          (derivationComp (B := R) (generatedCoordinateMap n R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  have hπ := generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap n R
  rw [GeneralLinear.weightTorusBaseChangeCoordinateMap_eq] at hπ
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus_of_eq
    (generatedDefiningIdeal n R) (basisWeight n) (generatedCoordinateHopfAlgebra_def n R)
    (generatedCoordinateMap n R) (generatedCoordinateMap_comp_eqToIso_hom n R) _ hπ α x

/-- Each normalized root vector has its integral signed simple-root character under the generated
weight torus, including in characteristic two. -/
theorem generatedRootVector_mem_adjointWeightSpace (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (Derivation.cotangentLinearEquiv (B := R)).symm (generatedRootVector n R (B := R) k) ∈
      Derivation.adjointWeightSpace (generatedWeightTorusCoordinateMap n R).hom
        (SplitTorus.weightCharacter (rootGeneratorWeight n k)) := by
  apply (mem_adjointWeightSpace_generatedWeightTorusCoordinateMap_iff n R _ _).2
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_generatedRootVector, Matrix.map_apply,
    rootIntMatrix_eq_zero_of_weight_ne n k
      (fun h ↦ hab (congrArg SplitTorus.weightCharacter h)), Int.cast_zero]

/-- Every numbered signed simple-root character occurs as a nontrivial adjoint weight of the
generated spin subgroup over a nontrivial base with projective augmentation cotangent module. -/
theorem rootGeneratorWeight_mem_generatedNontrivialAdjointWeights [Nontrivial R]
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    SplitTorus.weightCharacter (rootGeneratorWeight n k) ∈
      Derivation.nontrivialAdjointWeights (generatedWeightTorusCoordinateMap n R).hom := by
  apply Derivation.mem_nontrivialAdjointWeights.mpr
  refine ⟨?_, fun hbot ↦ ?_⟩
  · intro h
    have hdiag := congrArg
      (fun c : Multiplicative (Fin (n + 1) →₀ ℤ) ↦ Multiplicative.toAdd c (Sum.elim id id k)) h
    simp only [SplitTorus.toAdd_weightCharacter, toAdd_one, Finsupp.zero_apply] at hdiag
    cases k <;> simp at hdiag
  · have hz := generatedRootVector_mem_adjointWeightSpace n R k
    have hz' : (Derivation.cotangentLinearEquiv (B := R)).symm
        (generatedRootVector n R (B := R) k) ∈ (⊥ : Submodule R _) := hbot ▸ hz
    apply generatedRootVector_ne_zero n R (B := R) k
    simpa only [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] using hz'

end Weights

end

end TauCeti.TypeBSpinCarrier
