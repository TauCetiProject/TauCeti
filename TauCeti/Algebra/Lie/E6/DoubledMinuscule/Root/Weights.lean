/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Adjoint characters of the integral doubled E₆ root vectors

The normalized differentials of the twelve numbered root subgroups of the integral carrier on
`V(ϖ₁) ⊕ V(ϖ₆)` are eigenvectors for its weight torus. The eigencharacters are the integral
signed simple roots, not their reductions modulo the characteristic of a value ring.
The adjoint-action equation holds with values in every commutative ring, including nonreduced
rings, without a smoothness assumption on the carrier.

When the integral augmentation cotangent module is projective, the same vectors, transported
through `Derivation.cotangentLinearEquiv`, belong to the corresponding adjoint comodule weight
spaces. Those characters are nontrivial adjoint weights. This supplies the weight compatibility
of the normalized differentials used in a pinning; it does not prove cotangent projectivity,
that the root lines exhaust their weight spaces, maximality of the torus, or the existence of a
Borel. The carrier is not identified with an independently pinned simply connected group scheme.
As in the generic adjoint API, projectivity refers to the cotangent algebra's integer module.
When stating these hypotheses over `ℤ`, give `Algebra.toModule` and
`Ideal.instModuleCotangentOfAlgebra` local instance priority over the additive-group module.

## Main results

* `TauCeti.E6DoubledMinuscule.adDerivation_weightTorus_rootVector`: torus points act on each
  normalized root differential through its signed simple-root character.
* `TauCeti.E6DoubledMinuscule.mem_adjointWeightSpace_iff`: the integral carrier's adjoint
  weight-space criterion in matrix coordinates, assuming cotangent projectivity.
* `TauCeti.E6DoubledMinuscule.rootVector_mem_adjointWeightSpace`: the normalized root
  differentials, viewed in the cotangent dual, have their prescribed adjoint weights.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The normalization is `TauCeti.E6DoubledMinuscule.rootVector`; the weight-space interpretation
uses `TauCeti.HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus`, as in the short-root G₂ and
F₄ constructions. The matrix support calculation uses the general Kostant weight-basis lemma
`TauCeti.UniversalEnvelopingAlgebra.repr_eq_zero_of_isCartanWeightVector`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.E6DoubledMinuscule

noncomputable section

attribute [local instance high] Algebra.toModule
-- Keep the cotangent algebra module rather than the generic integer module on its additive group.
attribute [local instance high] Ideal.instModuleCotangentOfAlgebra

local notation "Q" => GeneralLinear.coordinateHopfAlgebra ℤ 54 ⧸ definingIdeal.toIdeal

private theorem weightTorusIntegralCoordinateMap_comp_quotient :
    weightTorusIntegralCoordinateMap.hom.comp
        (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap matrixWeight).hom := by
  rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
    mkQuotient_comp_weightTorusIntegralCoordinateMap]

/-- Over any commutative value ring, the weight torus acts on each normalized integral root
vector through its signed simple-root character. This includes rings with nilpotents. -/
theorem adDerivation_weightTorus_rootVector {B : Type*} [CommRing B]
    (s : WithConv (MonoidAlgebra ℤ (Multiplicative (Fin 6 →₀ ℤ)) →ₐ[ℤ] B))
    (k : Fin 6 ⊕ Fin 6) :
    Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra (H := Q) B
          (toConv (s.ofConv.comp weightTorusIntegralCoordinateMap.hom.toAlgHom)))
        (rootVector (B := B) k) =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (E6.rootGeneratorWeight k)) : B) •
        rootVector (B := B) k := by
  apply HopfIdeal.quotientLieHom_injective definingIdeal
  apply (GeneralLinear.tangentLinearEquivMatrix (R := ℤ) (B := B) 54).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply,
    GeneralLinear.tangentLinearEquivMatrix_apply]
  ext a b
  rw [HopfIdeal.tangentMatrix_adDerivation_weightTorus_apply definingIdeal matrixWeight
    weightTorusIntegralCoordinateMap.hom weightTorusIntegralCoordinateMap_comp_quotient,
    map_smul, map_smul, Matrix.smul_apply, smul_eq_mul, tangentMatrix_rootVector]
  by_cases hab : matrixWeight a - matrixWeight b = E6.rootGeneratorWeight k
  · rw [hab]
  · rw [Matrix.map_apply, rootIntMatrix_eq_zero_of_weight_ne k hab]
    simp

variable [Module.Projective ℤ (Bialgebra.CotangentSpace ℤ Q)]

/-- An adjoint weight vector has matrix entries only at the corresponding integral weight
differences. Cotangent projectivity is needed for the adjoint comodule, not for the entrywise
torus-action equation. -/
theorem mem_adjointWeightSpace_iff (α : Multiplicative (Fin 6 →₀ ℤ))
    (x : Module.Dual ℤ (Bialgebra.CotangentSpace ℤ Q)) :
    x ∈ Derivation.adjointWeightSpace weightTorusIntegralCoordinateMap.hom α ↔
      ∀ a b, SplitTorus.weightCharacter (matrixWeight a - matrixWeight b) ≠ α →
        GeneralLinear.tangentMatrix 54
          (HopfIdeal.quotientLieHom definingIdeal
            (Derivation.cotangentLinearEquiv (B := ℤ) x)) a b = 0 :=
  HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus definingIdeal matrixWeight
    weightTorusIntegralCoordinateMap.hom weightTorusIntegralCoordinateMap_comp_quotient α x

/-- A normalized root differential, viewed in the cotangent dual of the integral carrier, has
its prescribed signed simple-root character. -/
theorem rootVector_mem_adjointWeightSpace (k : Fin 6 ⊕ Fin 6) :
    (Derivation.cotangentLinearEquiv (B := ℤ)).symm (rootVector (B := ℤ) k) ∈
      Derivation.adjointWeightSpace weightTorusIntegralCoordinateMap.hom
        (SplitTorus.weightCharacter (E6.rootGeneratorWeight k)) := by
  rw [mem_adjointWeightSpace_iff]
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_rootVector, Matrix.map_apply]
  simp only [Int.cast_id]
  exact rootIntMatrix_eq_zero_of_weight_ne k fun h ↦ hab (congrArg _ h)

/-- Every numbered signed simple-root character occurs as a nontrivial adjoint weight of the
integral doubled carrier, assuming its cotangent module is projective. -/
theorem rootGeneratorWeight_mem_nontrivialAdjointWeights (k : Fin 6 ⊕ Fin 6) :
    SplitTorus.weightCharacter (E6.rootGeneratorWeight k) ∈
      Derivation.nontrivialAdjointWeights weightTorusIntegralCoordinateMap.hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨?_, ?_⟩
  · intro h
    have hdiag := congrArg
      (fun c : Multiplicative (Fin 6 →₀ ℤ) ↦ Multiplicative.toAdd c (Sum.elim id id k)) h
    simp only [SplitTorus.toAdd_weightCharacter, toAdd_one,
      Finsupp.zero_apply] at hdiag
    cases k <;> simp [E6.rootGeneratorWeight_inl, E6.rootGeneratorWeight_inr,
      CartanMatrix.E_diag] at hdiag
  · intro hbot
    have hv := rootVector_mem_adjointWeightSpace k
    rw [hbot, Submodule.mem_bot] at hv
    have hz := congrArg (Derivation.cotangentLinearEquiv (B := ℤ)) hv
    exact rootVector_ne_zero k (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hz)

end

end TauCeti.E6DoubledMinuscule
