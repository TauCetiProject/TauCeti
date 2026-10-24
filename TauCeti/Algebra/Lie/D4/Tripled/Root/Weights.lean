/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace

/-!
# Adjoint characters of the integral tripled type-D4 root vectors

The normalized differentials of the eight numbered root subgroups of the integral tripled
type-`D₄` carrier are eigenvectors for its weight torus. The eigencharacters are the integral
signed simple roots `TauCeti.TypeDStd.rootGeneratorWeight`, the rows of the type-`D₄` Cartan
matrix and their negatives, not their reductions modulo the characteristic of a value ring, so
opposite roots stay distinct in characteristic two. The adjoint-action equation holds with values
in every commutative ring, including nonreduced rings, without a smoothness assumption on the
carrier.

When the integral augmentation cotangent module is projective, the same vectors, transported
through `Derivation.cotangentLinearEquiv`, belong to the corresponding adjoint comodule weight
spaces, and those characters are nontrivial adjoint weights. This is the weight compatibility of
the normalized differentials used in a pinning. It does not prove cotangent projectivity, that the
root lines exhaust their weight spaces, maximality of the torus, or the existence of a Borel
subgroup, and the carrier is not identified with an independently pinned simply connected group
scheme of type `D₄`. As in the generic adjoint API, projectivity refers to the cotangent algebra's
integer module.

## Main results

* `TauCeti.D4Tripled.adDerivation_weightTorus_rootVector`: torus points act on each normalized
  root differential through its signed simple-root character.
* `TauCeti.D4Tripled.mem_adjointWeightSpace_iff`: the integral carrier's adjoint weight-space
  criterion in matrix coordinates, assuming cotangent projectivity.
* `TauCeti.D4Tripled.rootVector_mem_adjointWeightSpace`: the normalized root differentials,
  viewed in the cotangent dual, have their prescribed adjoint weights.
* `TauCeti.D4Tripled.rootGeneratorWeight_mem_nontrivialAdjointWeights`: every signed simple root
  is a nontrivial adjoint weight.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.

The weight-space interpretation uses `TauCeti.HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus`,
and the argument follows the type-`D` spin carrier in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Weights`. The matrix support calculation is
`TauCeti.D4Tripled.rootMatrix_eq_zero_of_weight_ne`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

noncomputable section

-- Cotangent-projectivity hypotheses over `ℤ` are stated with `Algebra.toModule` and
-- `Ideal.instModuleCotangentOfAlgebra` given local priority over the additive-group module.
attribute [local instance high] Algebra.toModule
-- Keep the cotangent algebra module rather than the generic integer module on its additive group.
attribute [local instance high] Ideal.instModuleCotangentOfAlgebra

private theorem weightTorusIntegralCoordinateMap_comp_quotient :
    weightTorusIntegralCoordinateMap.hom.comp
        (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap d4TripledWeight).hom := by
  rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
    mkQuotient_comp_weightTorusIntegralCoordinateMap]

/-- Over any commutative value ring, the weight torus acts on each normalized integral root
vector through its signed simple-root character. This includes rings with nilpotents. -/
theorem adDerivation_weightTorus_rootVector {B : Type*} [CommRing B]
    (s : WithConv (MonoidAlgebra ℤ (Multiplicative (Fin 4 →₀ ℤ)) →ₐ[ℤ] B))
    (k : Fin 4 ⊕ Fin 4) :
    Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal) B
          (toConv (s.ofConv.comp weightTorusIntegralCoordinateMap.hom.toAlgHom)))
        (rootVector (B := B) k) =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 k)) : B) •
        rootVector (B := B) k := by
  apply HopfIdeal.quotientLieHom_injective definingIdeal
  apply (GeneralLinear.tangentLinearEquivMatrix (R := ℤ) (B := B) 24).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply,
    GeneralLinear.tangentLinearEquivMatrix_apply]
  ext a b
  rw [HopfIdeal.tangentMatrix_adDerivation_weightTorus_apply definingIdeal d4TripledWeight
    weightTorusIntegralCoordinateMap.hom weightTorusIntegralCoordinateMap_comp_quotient,
    map_smul, map_smul, Matrix.smul_apply, smul_eq_mul, tangentMatrix_rootVector]
  by_cases hab : d4TripledWeight a - d4TripledWeight b = TypeDStd.rootGeneratorWeight 4 k
  · rw [hab]
  · rw [Matrix.map_apply, rootMatrix_eq_zero_of_weight_ne k hab]
    simp

variable [Module.Projective ℤ (Bialgebra.CotangentSpace ℤ
  (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal))]

/-- An adjoint weight vector has matrix entries only at the corresponding integral weight
differences. Cotangent projectivity is needed for the adjoint comodule, not for the entrywise
torus-action equation. -/
theorem mem_adjointWeightSpace_iff (α : Multiplicative (Fin 4 →₀ ℤ))
    (x : Module.Dual ℤ (Bialgebra.CotangentSpace ℤ
      (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal))) :
    x ∈ Derivation.adjointWeightSpace weightTorusIntegralCoordinateMap.hom α ↔
      ∀ a b, SplitTorus.weightCharacter (d4TripledWeight a - d4TripledWeight b) ≠ α →
        GeneralLinear.tangentMatrix 24
          (HopfIdeal.quotientLieHom definingIdeal
            (Derivation.cotangentLinearEquiv (B := ℤ) x)) a b = 0 :=
  HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus definingIdeal d4TripledWeight
    weightTorusIntegralCoordinateMap.hom weightTorusIntegralCoordinateMap_comp_quotient α x

/-- A normalized root differential, viewed in the cotangent dual of the integral carrier, has
its prescribed signed simple-root character. -/
theorem rootVector_mem_adjointWeightSpace (k : Fin 4 ⊕ Fin 4) :
    (Derivation.cotangentLinearEquiv (B := ℤ)).symm (rootVector (B := ℤ) k) ∈
      Derivation.adjointWeightSpace weightTorusIntegralCoordinateMap.hom
        (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 k)) := by
  rw [mem_adjointWeightSpace_iff]
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_rootVector, Matrix.map_apply]
  simp only [Int.cast_id]
  exact rootMatrix_eq_zero_of_weight_ne k fun h ↦ hab (congrArg _ h)

/-- Every numbered signed simple-root character occurs as a nontrivial adjoint weight of the
integral tripled carrier, assuming its cotangent module is projective. -/
theorem rootGeneratorWeight_mem_nontrivialAdjointWeights (k : Fin 4 ⊕ Fin 4) :
    SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight 4 k) ∈
      Derivation.nontrivialAdjointWeights weightTorusIntegralCoordinateMap.hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨?_, ?_⟩
  · intro h
    have hdiag := congrArg
      (fun c : Multiplicative (Fin 4 →₀ ℤ) ↦ Multiplicative.toAdd c (Sum.elim id id k)) h
    simp only [SplitTorus.toAdd_weightCharacter, toAdd_one, Finsupp.zero_apply] at hdiag
    cases k <;> simp [TypeDStd.rootGeneratorWeight_inl, TypeDStd.rootGeneratorWeight_inr,
      CartanMatrix.D_diag] at hdiag
  · intro hbot
    have hv := rootVector_mem_adjointWeightSpace k
    rw [hbot, Submodule.mem_bot] at hv
    have hz := congrArg (Derivation.cotangentLinearEquiv (B := ℤ)) hv
    exact rootVector_ne_zero k
      (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hz)

end

end TauCeti.D4Tripled
