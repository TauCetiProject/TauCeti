/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Adjoint characters of the integral type-D spin root vectors

The normalized differentials of the `2n` numbered root subgroups of the integral full-weight
type-`Dₙ` spin carrier are eigenvectors for its weight torus. The eigencharacters are the integral
signed simple roots `TauCeti.TypeDStd.rootGeneratorWeight`, not their reductions modulo the
characteristic of a value ring, so opposite roots stay distinct in characteristic two. The
adjoint-action equation holds with values in every commutative ring, including nonreduced rings,
without a smoothness assumption on the carrier.

When the integral augmentation cotangent module is projective, the same vectors, transported
through `Derivation.cotangentLinearEquiv`, belong to the corresponding adjoint comodule weight
spaces, and those characters are nontrivial adjoint weights. This is the weight compatibility of
the normalized differentials used in a pinning. It does not prove cotangent projectivity, that the
root lines exhaust their weight spaces, maximality of the torus, or the existence of a Borel
subgroup, and the carrier is not identified with an independently pinned simply connected group
scheme of type `Dₙ`. As in the generic adjoint API, projectivity refers to the cotangent algebra's
integer module. When stating these hypotheses over `ℤ`, give `Algebra.toModule` and
`Ideal.instModuleCotangentOfAlgebra` local instance priority over the additive-group module.

## Main results

* `TauCeti.TypeDSpinCarrier.adDerivation_weightTorus_rootVector`: torus points act on each
  normalized root differential through its signed simple-root character.
* `TauCeti.TypeDSpinCarrier.mem_adjointWeightSpace_iff`: the integral carrier's adjoint
  weight-space criterion in matrix coordinates, assuming cotangent projectivity.
* `TauCeti.TypeDSpinCarrier.rootVector_mem_adjointWeightSpace`: the normalized root
  differentials, viewed in the cotangent dual, have their prescribed adjoint weights.
* `TauCeti.TypeDSpinCarrier.rootGeneratorWeight_mem_nontrivialAdjointWeights`: every signed
  simple root is a nontrivial adjoint weight.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.

The weight-space interpretation uses `TauCeti.HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus`,
and the argument follows the doubled `E₆` carrier in
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.Root.Weights`. The matrix support calculation is
`TauCeti.TypeDSpinCarrier.rootIntMatrix_eq_zero_of_weight_ne`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.TypeDSpinCarrier

noncomputable section

attribute [local instance high] Algebra.toModule
-- Keep the cotangent algebra module rather than the generic integer module on its additive group.
attribute [local instance high] Ideal.instModuleCotangentOfAlgebra

variable (n : ℕ) (hn : 4 ≤ n)

private theorem weightTorusIntegralCoordinateMap_comp_quotient :
    (weightTorusIntegralCoordinateMap n hn).hom.comp
        (Bialgebra.Quotient.mkBialgHom (definingIdeal n hn).toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap (basisWeight n)).hom := by
  rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
    mkQuotient_comp_weightTorusIntegralCoordinateMap]

/-- Over any commutative value ring, the weight torus acts on each normalized integral root
vector through its signed simple-root character. This includes rings with nilpotents. -/
theorem adDerivation_weightTorus_rootVector {B : Type*} [CommRing B]
    (s : WithConv (MonoidAlgebra ℤ (Multiplicative (Fin n →₀ ℤ)) →ₐ[ℤ] B))
    (k : Fin n ⊕ Fin n) :
    Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸
            (definingIdeal n hn).toIdeal) B
          (toConv (s.ofConv.comp (weightTorusIntegralCoordinateMap n hn).hom.toAlgHom)))
        (rootVector n hn (B := B) k) =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight n k)) : B) •
        rootVector n hn (B := B) k := by
  apply HopfIdeal.quotientLieHom_injective (definingIdeal n hn)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := ℤ) (B := B) (dimension n)).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply,
    GeneralLinear.tangentLinearEquivMatrix_apply]
  ext a b
  rw [HopfIdeal.tangentMatrix_adDerivation_weightTorus_apply (definingIdeal n hn) (basisWeight n)
    (weightTorusIntegralCoordinateMap n hn).hom
    (weightTorusIntegralCoordinateMap_comp_quotient n hn),
    map_smul, map_smul, Matrix.smul_apply, smul_eq_mul, tangentMatrix_rootVector]
  by_cases hab : basisWeight n a - basisWeight n b = TypeDStd.rootGeneratorWeight n k
  · rw [hab]
  · rw [Matrix.map_apply, rootIntMatrix_eq_zero_of_weight_ne n hn k hab]
    simp

variable [Module.Projective ℤ (Bialgebra.CotangentSpace ℤ
  (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n hn).toIdeal))]

/-- An adjoint weight vector has matrix entries only at the corresponding integral weight
differences. Cotangent projectivity is needed for the adjoint comodule, not for the entrywise
torus-action equation. -/
theorem mem_adjointWeightSpace_iff (α : Multiplicative (Fin n →₀ ℤ))
    (x : Module.Dual ℤ (Bialgebra.CotangentSpace ℤ
      (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n hn).toIdeal))) :
    x ∈ Derivation.adjointWeightSpace (weightTorusIntegralCoordinateMap n hn).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (basisWeight n a - basisWeight n b) ≠ α →
        GeneralLinear.tangentMatrix (dimension n)
          (HopfIdeal.quotientLieHom (definingIdeal n hn)
            (Derivation.cotangentLinearEquiv (B := ℤ) x)) a b = 0 :=
  HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus (definingIdeal n hn) (basisWeight n)
    (weightTorusIntegralCoordinateMap n hn).hom
    (weightTorusIntegralCoordinateMap_comp_quotient n hn) α x

/-- A normalized root differential, viewed in the cotangent dual of the integral carrier, has
its prescribed signed simple-root character. -/
theorem rootVector_mem_adjointWeightSpace (k : Fin n ⊕ Fin n) :
    (Derivation.cotangentLinearEquiv (B := ℤ)).symm (rootVector n hn (B := ℤ) k) ∈
      Derivation.adjointWeightSpace (weightTorusIntegralCoordinateMap n hn).hom
        (SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight n k)) := by
  rw [mem_adjointWeightSpace_iff]
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_rootVector, Matrix.map_apply]
  simp only [Int.cast_id]
  exact rootIntMatrix_eq_zero_of_weight_ne n hn k fun h ↦ hab (congrArg _ h)

/-- Every numbered signed simple-root character occurs as a nontrivial adjoint weight of the
integral spin carrier, assuming its cotangent module is projective. -/
theorem rootGeneratorWeight_mem_nontrivialAdjointWeights (k : Fin n ⊕ Fin n) :
    SplitTorus.weightCharacter (TypeDStd.rootGeneratorWeight n k) ∈
      Derivation.nontrivialAdjointWeights (weightTorusIntegralCoordinateMap n hn).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨?_, ?_⟩
  · intro h
    have hdiag := congrArg
      (fun c : Multiplicative (Fin n →₀ ℤ) ↦ Multiplicative.toAdd c (Sum.elim id id k)) h
    simp only [SplitTorus.toAdd_weightCharacter, toAdd_one, Finsupp.zero_apply] at hdiag
    cases k <;> simp [TypeDStd.rootGeneratorWeight_inl, TypeDStd.rootGeneratorWeight_inr,
      CartanMatrix.D_diag] at hdiag
  · intro hbot
    have hv := rootVector_mem_adjointWeightSpace n hn k
    rw [hbot, Submodule.mem_bot] at hv
    have hz := congrArg (Derivation.cotangentLinearEquiv (B := ℤ)) hv
    exact rootVector_ne_zero n hn k
      (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hz)

end

end TauCeti.TypeDSpinCarrier
