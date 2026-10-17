/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Root.Differential

/-!
# Adjoint characters of the integral Geck root vectors

The normalized differentials of the `2 · rank` numbered root subgroups of the integral Geck
carrier of a valid Dynkin type are eigenvectors for its weight torus. The eigencharacters are the
integral signed simple roots `TauCeti.DynkinType.rootGeneratorWeight`, the Bourbaki rows of the
Cartan matrix and their negatives, not their reductions modulo the characteristic of a value
ring, so opposite roots stay distinct in characteristic two. The adjoint-action equation holds
with values in every commutative ring, including nonreduced rings, without a smoothness assumption
on the carrier.

When the integral augmentation cotangent module is projective, the same vectors, transported
through `Derivation.cotangentLinearEquiv`, belong to the corresponding adjoint comodule weight
spaces, and those characters are nontrivial adjoint weights. This is the weight compatibility of
the normalized differentials used in a pinning. It does not prove cotangent projectivity, that the
root lines exhaust their weight spaces, maximality of the torus, or the existence of a Borel
subgroup, and the carrier is not identified with an independently pinned simply connected group
scheme. As in the generic adjoint API, projectivity refers to the cotangent algebra's integer
module.

## Main results

* `TauCeti.DynkinType.adDerivation_geckWeightTorus_geckRootVector`: torus points act on each
  normalized root differential through its signed simple-root character.
* `TauCeti.DynkinType.mem_adjointWeightSpace_geckWeightTorus_iff`: the integral carrier's
  adjoint weight-space criterion in matrix coordinates, assuming cotangent projectivity.
* `TauCeti.DynkinType.geckRootVector_mem_adjointWeightSpace`: the normalized root differentials,
  viewed in the cotangent dual, have their prescribed adjoint weights.
* `TauCeti.DynkinType.rootGeneratorWeight_mem_nontrivialAdjointWeights_geckWeightTorus`: every
  signed simple root is a nontrivial adjoint weight.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The weight-space interpretation uses `TauCeti.HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus`,
and the argument follows the type-`D` spin carrier in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Weights`. The matrix support calculation is
`TauCeti.DynkinType.geckRootIntMatrix_eq_zero_of_weight_ne`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.DynkinType

noncomputable section

-- Cotangent-projectivity hypotheses over `ℤ` are stated with `Algebra.toModule` and
-- `Ideal.instModuleCotangentOfAlgebra` given local priority over the additive-group module.
attribute [local instance high] Algebra.toModule
-- Keep the cotangent algebra module rather than the generic integer module on its additive group.
attribute [local instance high] Ideal.instModuleCotangentOfAlgebra

variable (t : DynkinType) (ht : t.Valid)

private theorem geckWeightTorusIntegralCoordinateMap_comp_quotient :
    (t.geckWeightTorusIntegralCoordinateMap ht).hom.comp
        (Bialgebra.Quotient.mkBialgHom (t.geckDefiningIdeal ht).toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap (t.geckWeightFin ht)).hom := by
  rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
    geckWeightTorusIntegralCoordinateMap_def,
    UniversalEnvelopingAlgebra.mkQuotient_comp_kostantWeightTorusToralCoordinateMap]

/-- Over any commutative value ring, the weight torus acts on each normalized integral Geck root
vector through its signed simple-root character. This includes rings with nilpotents. -/
theorem adDerivation_geckWeightTorus_geckRootVector {B : Type*} [CommRing B]
    (s : WithConv (MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ)) →ₐ[ℤ] B))
    (i : Fin t.rank ⊕ Fin t.rank) :
    Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht) ⧸
            (t.geckDefiningIdeal ht).toIdeal) B
          (toConv (s.ofConv.comp (t.geckWeightTorusIntegralCoordinateMap ht).hom.toAlgHom)))
        (t.geckRootVector ht (B := B) i) =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (t.rootGeneratorWeight ht i)) : B) •
        t.geckRootVector ht (B := B) i := by
  apply HopfIdeal.quotientLieHom_injective (t.geckDefiningIdeal ht)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := ℤ) (B := B) (t.geckDim ht)).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply,
    GeneralLinear.tangentLinearEquivMatrix_apply]
  ext a b
  rw [HopfIdeal.tangentMatrix_adDerivation_weightTorus_apply (t.geckDefiningIdeal ht)
    (t.geckWeightFin ht) (t.geckWeightTorusIntegralCoordinateMap ht).hom
    (t.geckWeightTorusIntegralCoordinateMap_comp_quotient ht),
    map_smul, map_smul, Matrix.smul_apply, smul_eq_mul, tangentMatrix_geckRootVector]
  by_cases hab : t.geckWeightFin ht a - t.geckWeightFin ht b = t.rootGeneratorWeight ht i
  · rw [hab]
  · rw [Matrix.map_apply, t.geckRootIntMatrix_eq_zero_of_weight_ne ht i hab]
    simp

variable [Module.Projective ℤ (Bialgebra.CotangentSpace ℤ
  (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht) ⧸ (t.geckDefiningIdeal ht).toIdeal))]

/-- An adjoint weight vector of the integral Geck carrier has matrix entries only at the
corresponding integral weight differences. Cotangent projectivity is needed for the adjoint
comodule, not for the entrywise torus-action equation. -/
theorem mem_adjointWeightSpace_geckWeightTorus_iff (α : Multiplicative (Fin t.rank →₀ ℤ))
    (x : Module.Dual ℤ (Bialgebra.CotangentSpace ℤ
      (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht) ⧸
        (t.geckDefiningIdeal ht).toIdeal))) :
    x ∈ Derivation.adjointWeightSpace (t.geckWeightTorusIntegralCoordinateMap ht).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (t.geckWeightFin ht a - t.geckWeightFin ht b) ≠ α →
        GeneralLinear.tangentMatrix (t.geckDim ht)
          (HopfIdeal.quotientLieHom (t.geckDefiningIdeal ht)
            (Derivation.cotangentLinearEquiv (B := ℤ) x)) a b = 0 :=
  HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus (t.geckDefiningIdeal ht)
    (t.geckWeightFin ht) (t.geckWeightTorusIntegralCoordinateMap ht).hom
    (t.geckWeightTorusIntegralCoordinateMap_comp_quotient ht) α x

/-- A normalized Geck root differential, viewed in the cotangent dual of the integral carrier, has
its prescribed signed simple-root character. -/
theorem geckRootVector_mem_adjointWeightSpace (i : Fin t.rank ⊕ Fin t.rank) :
    (Derivation.cotangentLinearEquiv (B := ℤ)).symm (t.geckRootVector ht (B := ℤ) i) ∈
      Derivation.adjointWeightSpace (t.geckWeightTorusIntegralCoordinateMap ht).hom
        (SplitTorus.weightCharacter (t.rootGeneratorWeight ht i)) := by
  rw [mem_adjointWeightSpace_geckWeightTorus_iff]
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_geckRootVector, Matrix.map_apply]
  simp only [Int.cast_id]
  exact t.geckRootIntMatrix_eq_zero_of_weight_ne ht i fun h ↦ hab (congrArg _ h)

/-- Every numbered signed simple-root character occurs as a nontrivial adjoint weight of the
integral Geck carrier, assuming its cotangent module is projective. -/
theorem rootGeneratorWeight_mem_nontrivialAdjointWeights_geckWeightTorus
    (i : Fin t.rank ⊕ Fin t.rank) :
    SplitTorus.weightCharacter (t.rootGeneratorWeight ht i) ∈
      Derivation.nontrivialAdjointWeights (t.geckWeightTorusIntegralCoordinateMap ht).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨?_, ?_⟩
  · intro h
    have hdiag := congrArg
      (fun c : Multiplicative (Fin t.rank →₀ ℤ) ↦
        Multiplicative.toAdd c (Sum.elim id id i)) h
    simp only [SplitTorus.toAdd_weightCharacter, toAdd_one, Finsupp.zero_apply] at hdiag
    cases i <;> simp at hdiag
  · intro hbot
    have hv := t.geckRootVector_mem_adjointWeightSpace ht i
    rw [hbot, Submodule.mem_bot] at hv
    have hz := congrArg (Derivation.cotangentLinearEquiv (B := ℤ)) hv
    exact t.geckRootVector_ne_zero ht i
      (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hz)

end

end TauCeti.DynkinType
