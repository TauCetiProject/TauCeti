/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Root.Weights
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PointsFunctor

/-!
# All roots occur as adjoint weights of the Geck carrier

The integral Weyl representatives transport the signed simple-root adjoint weights to every
root of the named root datum. The transport uses inverse conjugation on characters, and hence
forward Weyl action on weights. These are integral characters, not their reductions to the
characteristic of a coefficient ring.

The adjoint-comodule statements retain the projectivity hypothesis on the integral augmentation
cotangent module. No exhaustion of the weight set, root-space dimension, maximality of the torus,
or identification with an independently pinned simply connected group scheme is asserted.

## Main results

* `TauCeti.DynkinType.geckWeightTorus_comp_pointConjugation_weylWord`: the coordinate-algebra
  equation for inverse conjugation by an integral Weyl representative.
* `TauCeti.DynkinType.geckWeylCharacterAut_mem_nontrivialAdjointWeights_iff`: Weyl invariance of
  the set of nontrivial adjoint weights.
* `TauCeti.DynkinType.root_mem_nontrivialAdjointWeights_geckWeightTorus`: every root occurs.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups* (2017).
* J. S. Milne, *Algebraic Groups* (2017), §21.1.

The transport uses `Derivation.mem_nontrivialAdjointWeights_apply_iff` and the existing
Geck Weyl-word torus-conjugation equation.
-/

public section

open WithConv

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance high] Algebra.toModule
attribute [local instance high] Ideal.instModuleCotangentOfAlgebra

variable (t : DynkinType) (ht : t.Valid)

/-- The Weyl action on the integral character group of the Geck weight torus. -/
def geckWeylCharacterAut : (t.simplyConnectedRootDatum ht).weylGroup →*
    MulAut (Multiplicative (Fin t.rank →₀ ℤ)) where
  toFun w := AddEquiv.toMultiplicative
    (Finsupp.addEquivFunOnFinite.trans
      ((DistribMulAction.toAddEquiv (Fin t.rank → ℤ) w).trans
        Finsupp.addEquivFunOnFinite.symm))
  map_one' := by
    ext α i
    simp
  map_mul' w₁ w₂ := by
    ext α i
    simp [mul_smul]

/-- On a weight written as an exponent vector, the character action is the usual Weyl action. -/
@[simp↓]
theorem geckWeylCharacterAut_weightCharacter
    (w : (t.simplyConnectedRootDatum ht).weylGroup) (μ : Fin t.rank → ℤ) :
    t.geckWeylCharacterAut ht w (SplitTorus.weightCharacter μ) =
      SplitTorus.weightCharacter (w • μ) := by
  rw [SplitTorus.weightCharacter_def, SplitTorus.weightCharacter_def]
  dsimp only [geckWeylCharacterAut]
  -- Project the underlying equivalences from the additive-equivalence constructors;
  -- no unfolding of the Weyl representation is needed.
  change Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm
      (w • Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm μ))) =
    Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (w • μ))
  rw [Equiv.apply_symm_apply]

private theorem coordinatePointMulEquiv_weightTorus (A : Type*) [CommRing A]
    (q : WithConv (MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ)) →ₐ[ℤ] A)) :
    t.geckCoordinatePointMulEquiv ht A
        (toConv (q.ofConv.comp (t.geckWeightTorusIntegralCoordinateMap ht).hom.toAlgHom)) =
      t.geckWeightTorusPoints ht A (SplitTorus.pointsMulEquiv q) := by
  apply Subtype.ext
  rw [coe_geckCoordinatePointMulEquiv, coe_geckWeightTorusPoints,
    CommHopfAlgCat.quotientPointsHom_apply]
  simp only [AlgHom.comp_assoc]
  rw [← BialgHom.comp_toAlgHom, ← CommHopfAlgCat.hom_comp,
    mkQuotient_comp_geckWeightTorusIntegralCoordinateMap]
  rw [UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
  have h := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
    (t.geckWeightFin ht) (CommAlgCat.of ℤ A) q
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (GeneralLinear.weightTorusCoordinateMap (t.geckWeightFin ht)) (CommAlgCat.of ℤ A) q] at h
  exact h

private theorem pointsMulEquiv_comp_geckWeylCharacterAut
    (w : (t.simplyConnectedRootDatum ht).weylGroup) (A : Type*) [CommRing A]
    (q : WithConv (MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ)) →ₐ[ℤ] A)) :
    SplitTorus.pointsMulEquiv
        (toConv (q.ofConv.comp (MonoidAlgebra.domCongr ℤ ℤ
          (t.geckWeylCharacterAut ht w)).toAlgHom)) =
      t.geckWeylTorusAction ht A w⁻¹ (SplitTorus.pointsMulEquiv q) := by
  have hchar (μ : Fin t.rank → ℤ) :
      torusCharacter (SplitTorus.pointsMulEquiv
        (toConv (q.ofConv.comp (MonoidAlgebra.domCongr ℤ ℤ
          (t.geckWeylCharacterAut ht w)).toAlgHom))) μ =
        torusCharacter (t.geckWeylTorusAction ht A w⁻¹ (SplitTorus.pointsMulEquiv q)) μ := by
    rw [torusCharacter_geckWeylTorusAction, inv_inv,
      ← SplitTorus.charOfPoint_weightCharacter, ← SplitTorus.charOfPoint_weightCharacter]
    apply Units.ext
    simp only [DiagonalizableGroup.charOfPoint_apply_coe,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MonoidAlgebra.domCongr_single,
      geckWeylCharacterAut_weightCharacter]
  funext i
  simpa only [← weightChar_apply, weightChar_single] using hchar (Pi.single i 1)

private theorem coordinatePointMulEquiv_weightTorus_id :
    t.geckCoordinatePointMulEquiv ht
        (MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ)))
        (toConv (t.geckWeightTorusIntegralCoordinateMap ht).hom.toAlgHom) =
      t.geckWeightTorusPoints ht _ (SplitTorus.pointsMulEquiv (toConv (AlgHom.id ℤ _))) := by
  have h := t.coordinatePointMulEquiv_weightTorus ht _
    (toConv (AlgHom.id ℤ (MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ)))))
  -- The coordinate map's target has the categorical carrier wrapper, whereas id
  -- uses the underlying monoid algebra; elaborated rewriting identifies the carriers.
  erw [AlgHom.id_comp] at h
  exact h

private theorem pointsMulEquiv_geckWeylCharacterAut
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    SplitTorus.pointsMulEquiv (toConv
        (MonoidAlgebra.domCongr ℤ ℤ (t.geckWeylCharacterAut ht w)).toAlgHom) =
      t.geckWeylTorusAction ht _ w⁻¹
        (SplitTorus.pointsMulEquiv (toConv (AlgHom.id ℤ _))) := by
  have h := t.pointsMulEquiv_comp_geckWeylCharacterAut ht w _
    (toConv (AlgHom.id ℤ (MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ)))))
  -- As in the coordinate-map specialization, the character algebra is presented
  -- both as a categorical carrier and as its underlying monoid algebra.
  erw [AlgHom.id_comp] at h
  exact h

/-- Inverse conjugation by an integral Weyl-word point induces the forward Weyl action on the
coordinate characters of the weight torus. This is a coordinate-algebra equality, not merely
an equality on integer-valued points. -/
theorem geckWeightTorus_comp_pointConjugation_weylWord (l : List (Fin t.rank)) :
    (t.geckWeightTorusIntegralCoordinateMap ht).hom.toAlgHom.comp
        (HopfAlgebra.pointConjugationAlgHom
          (t.geckCoordinatePoint ht (t.geckWeylWordPoint ht l ℤ))⁻¹) =
      (MonoidAlgebra.domCongr ℤ ℤ
        (t.geckWeylCharacterAut ht (t.geckWeylWordProd ht l))).toAlgHom.comp
          (t.geckWeightTorusIntegralCoordinateMap ht).hom.toAlgHom := by
  let K := MonoidAlgebra ℤ (Multiplicative (Fin t.rank →₀ ℤ))
  let π : t.geckCoordinateHopfAlgebra ht →ₐ[ℤ] K :=
    (t.geckWeightTorusIntegralCoordinateMap ht).hom.toAlgHom
  let g := t.geckCoordinatePoint ht (t.geckWeylWordPoint ht l ℤ)
  let q : WithConv (K →ₐ[ℤ] K) := toConv (AlgHom.id ℤ K)
  have he : (toConv (π.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹)) :
      WithConv (t.geckCoordinateHopfAlgebra ht →ₐ[ℤ] K)) =
      toConv ((MonoidAlgebra.domCongr ℤ ℤ
        (t.geckWeylCharacterAut ht (t.geckWeylWordProd ht l))).toAlgHom.comp π) := by
    apply (t.geckCoordinatePointMulEquiv ht K).injective
    have hmap : (Algebra.ofId ℤ K).mapValue g =
        HopfAlgebra.extendPoint (t.geckCoordinateHopfAlgebra ht) (CommAlgCat.of ℤ K) g := by
      rw [AlgHom.mapValue_apply, HopfAlgebra.extendPoint_apply]
    have hconst : t.geckCoordinatePointMulEquiv ht K ((Algebra.ofId ℤ K).mapValue g) =
        t.geckWeylWordPoint ht l K := by
      rw [hmap]
      dsimp only [g]
      -- extendPoint uses CommAlgCat's carrier, while the matrix-point map uses K;
      -- these are definitionally the same ring, so elaborated rewriting aligns them.
      erw [geckCoordinatePointMulEquiv_extendPoint_geckCoordinatePoint,
        map_geckWeylWordPoint]
    rw [HopfAlgebra.comp_pointConjugationAlgHom]
    -- The coordinate-ring presentation and its underlying monoid algebra have the same ring
    -- structure; elaborated rewriting crosses the categorical carrier wrappers here.
    erw [map_mul, map_mul]
    simp only [map_inv, inv_inv]
    -- The inverse point has the categorical convolution-group instance; use the
    -- equivalence's inverse law explicitly across that presentation boundary.
    erw [(t.geckCoordinatePointMulEquiv ht K).map_inv]
    -- The remaining comparisons cross the same CommAlgCat.of ℤ K / K boundary:
    -- first identify the constant Weyl point, then the universal torus point,
    -- and finally the universal point pulled back along the character automorphism.
    erw [hconst]
    erw [t.coordinatePointMulEquiv_weightTorus_id ht,
      t.coordinatePointMulEquiv_weightTorus ht K]
    erw [t.pointsMulEquiv_geckWeylCharacterAut ht]
    have hconj := t.geckWeylWordPoint_conj_geckWeightTorusPoints ht l K
      (t.geckWeylTorusAction ht K (t.geckWeylWordProd ht l)⁻¹
        (SplitTorus.pointsMulEquiv q))
    rw [geckWeylWordTorusAction_geckWeylTorusAction_inv] at hconj
    rw [← hconj]
    group
    dsimp only [K, q]
  exact congrArg WithConv.ofConv he

variable [Module.Projective ℤ (Bialgebra.CotangentSpace ℤ
  (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht) ⧸ (t.geckDefiningIdeal ht).toIdeal))]

/-- The Weyl action on integral characters preserves the nontrivial adjoint weights of the
Geck carrier. -/
theorem geckWeylCharacterAut_mem_nontrivialAdjointWeights_iff
    (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (α : Multiplicative (Fin t.rank →₀ ℤ)) :
    t.geckWeylCharacterAut ht w α ∈
        Derivation.nontrivialAdjointWeights (t.geckWeightTorusIntegralCoordinateMap ht).hom ↔
      α ∈ Derivation.nontrivialAdjointWeights (t.geckWeightTorusIntegralCoordinateMap ht).hom := by
  obtain ⟨l, rfl⟩ := t.geckWeylWordProd_surjective ht w
  exact Derivation.mem_nontrivialAdjointWeights_apply_iff
    (t.geckWeightTorusIntegralCoordinateMap ht).hom
    (t.geckCoordinatePoint ht (t.geckWeylWordPoint ht l ℤ))
    (t.geckWeylCharacterAut ht (t.geckWeylWordProd ht l))
    (t.geckWeightTorus_comp_pointConjugation_weylWord ht l) α

/-- Every root of the named integral root datum occurs as a nontrivial adjoint weight of the
Geck carrier. This is an inclusion, not an exhaustion or a root-space dimension assertion. -/
theorem root_mem_nontrivialAdjointWeights_geckWeightTorus (k : Fin t.numRoots) :
    SplitTorus.weightCharacter ((t.simplyConnectedRootDatum ht).root k) ∈
      Derivation.nontrivialAdjointWeights (t.geckWeightTorusIntegralCoordinateMap ht).hom := by
  obtain ⟨l, i, hli⟩ := t.exists_geckWeylRootIndex_eq ht k
  have h := (t.geckWeylCharacterAut_mem_nontrivialAdjointWeights_iff ht
    (t.geckWeylWordProd ht l) (SplitTorus.weightCharacter (t.rootGeneratorWeight ht (.inl i)))).mpr
      (t.rootGeneratorWeight_mem_nontrivialAdjointWeights_geckWeightTorus ht (.inl i))
  rwa [geckWeylCharacterAut_weightCharacter, rootGeneratorWeight_inl_eq_root_simpleIndex,
    ← root_geckWeylRootIndex, hli] at h

end

end TauCeti.DynkinType
