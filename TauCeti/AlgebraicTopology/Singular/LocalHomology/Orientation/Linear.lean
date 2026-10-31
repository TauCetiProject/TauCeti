/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Local orientations of oriented vector spaces

An orientation `ω` of a real normed space `F` of dimension `n + 1` selects a local orientation of
`F` at the origin, a generator of `Hₙ₊₁(F, F ∖ {0}; ℤ)`
(`Orientation.localOrientation`). It is the oriented-chart generator
(`OpenPartialHomeomorph.localOrientationOfOrientedChart`) of the Euclidean model
`EuclideanSpace ℝ (ULift (Fin (n + 1)))`, carried to `F` by any continuous linear equivalence
`L : F ≃L[ℝ] EuclideanSpace ℝ (ULift (Fin (n + 1)))` together with the orientation `ω.map L` of the
model. It does not depend on the choice of `L`: two choices differ by a linear automorphism of the
model, which acts on its local homology by the sign of its determinant
(`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`), exactly as it acts on its
orientations.

The selected local orientations are natural: a continuous linear equivalence `f : F ≃L[ℝ] G`
carries the local orientation of `ω` to that of `ω.map f`
(`Orientation.localOrientation_map`), through the isomorphism of pairs
`(F, F ∖ {0}) ≅ (G, G ∖ {0})` it induces (`ContinuousLinearEquiv.complZeroPairIso`). The opposite
orientation selects the opposite local orientation (`Orientation.localOrientation_neg`).

These are the fibrewise normalizations of the Thom class of an oriented real vector bundle: the
fibres of the bundle are identified with a model fibre by linear equivalences, an orientation of
the bundle orients every fibre, and by naturality the selected generator of a fibre does not depend
on the identification used.

## Main definitions

* `ContinuousLinearEquiv.complZeroPairIso`: the isomorphism of pairs
  `(E, E ∖ {0}) ≅ (F, F ∖ {0})` induced by a continuous linear equivalence.
* `Orientation.localOrientation`: the local orientation at the origin selected by an orientation.

## Main results

* `Orientation.localOrientation_map`: continuous linear equivalences carry the selected local
  orientations to each other.
* `Orientation.localOrientation_neg`: reversing the orientation reverses the local orientation.
* `Orientation.localOrientation_euclideanSpace`: on the Euclidean model it is the oriented-chart
  generator of the identity chart.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10 (orientations of vector spaces and the fibre normalization of the
  Thom class).
-/

public section

noncomputable section

open CategoryTheory Module TauCeti

universe w

namespace ContinuousLinearEquiv

variable {R : Type*} [Semiring R] {E F G : Type w}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace G] [AddCommMonoid G] [Module R G]

/-- A continuous linear equivalence sends nonzero vectors to nonzero vectors. -/
theorem mapsTo_compl_zero (f : E ≃L[R] F) : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ := fun _ hx ↦ by
  rw [Set.mem_compl_singleton_iff] at hx ⊢
  exact f.map_ne_zero_iff.2 hx

/-- The isomorphism of pairs `(E, E ∖ {0}) ≅ (F, F ∖ {0})` induced by a continuous linear
equivalence `f : E ≃L[R] F`. -/
def complZeroPairIso (f : E ≃L[R] F) :
    TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E)) ≅ TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F)) :=
  TopPair.ofSubsetIso (X := TopCat.of E) (Y := TopCat.of F) f.toHomeomorph fun _ ↦ by
    rw [Set.mem_compl_singleton_iff, Set.mem_compl_singleton_iff, coe_toHomeomorph]
    exact f.map_ne_zero_iff.symm

/-- The map of pairs underlying `ContinuousLinearEquiv.complZeroPairIso f` is the map induced by
`f` as a continuous map. -/
theorem complZeroPairIso_hom (f : E ≃L[R] F) :
    f.complZeroPairIso.hom =
      TopPair.ofSubsetMap (TopCat.ofHom (f : C(E, F))) f.mapsTo_compl_zero := by
  rw [complZeroPairIso, TopPair.ofSubsetIso_hom]
  -- `f.toHomeomorph` and `f` have the same underlying continuous map.
  rfl

/-- The inverse map of pairs underlying `ContinuousLinearEquiv.complZeroPairIso f` is the map
induced by `f.symm` as a continuous map. -/
theorem complZeroPairIso_inv (f : E ≃L[R] F) :
    f.complZeroPairIso.inv =
      TopPair.ofSubsetMap (TopCat.ofHom (f.symm : C(F, E))) f.symm.mapsTo_compl_zero := by
  rw [complZeroPairIso, TopPair.ofSubsetIso_inv]
  -- `f.toHomeomorph.symm` and `f.symm` have the same underlying continuous map.
  rfl

@[simp]
theorem complZeroPairIso_hom_fst_apply (f : E ≃L[R] F) (x : E) :
    TopPair.Hom.fst f.complZeroPairIso.hom x = f x := by
  rw [complZeroPairIso_hom]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

@[simp]
theorem complZeroPairIso_inv_fst_apply (f : E ≃L[R] F) (y : F) :
    TopPair.Hom.fst f.complZeroPairIso.inv y = f.symm y := by
  rw [complZeroPairIso_inv]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- The pair isomorphism of a composite is the composite of the pair isomorphisms. -/
theorem complZeroPairIso_trans (f : E ≃L[R] F) (g : F ≃L[R] G) :
    (f.trans g).complZeroPairIso = f.complZeroPairIso ≪≫ g.complZeroPairIso := by
  ext : 1
  rw [Iso.trans_hom, complZeroPairIso_hom, complZeroPairIso_hom, complZeroPairIso_hom]
  exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext; simp)).symm

/-- The pair isomorphism of the inverse is the inverse of the pair isomorphism. -/
theorem complZeroPairIso_symm (f : E ≃L[R] F) :
    f.symm.complZeroPairIso = f.complZeroPairIso.symm := by
  ext : 1
  rw [complZeroPairIso_hom, Iso.symm_hom, complZeroPairIso_inv]

end ContinuousLinearEquiv

namespace Orientation

/-- The Euclidean model `EuclideanSpace ℝ (ULift (Fin (n + 1)))` of an `(n + 1)`-dimensional real
normed space in the universe `w`. -/
private abbrev Model (n : ℕ) : Type w :=
  EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))

variable {F G : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

/-- The oriented-chart local orientation of the Euclidean model at the origin. -/
private def modelLocalOrientation (ω : Orientation ℝ (Model.{w} n) (Fin (n + 1))) :
    LocalOrientation (Model.{w} n) 0 (n + 1) :=
  (OpenPartialHomeomorph.refl _).localOrientationOfOrientedChart
    (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _) ω
    (finrank_euclideanSpace_ulift_fin (n + 1))

private theorem modelLocalOrientation_neg (ω : Orientation ℝ (Model.{w} n) (Fin (n + 1))) :
    modelLocalOrientation (-ω) = -modelLocalOrientation ω :=
  OpenPartialHomeomorph.localOrientationOfOrientedChart_neg _ _ ω _

/-- A linear automorphism of the model carries the local orientation of `ω` to that of its image
orientation: both actions are by the sign of its determinant. -/
private theorem singularHomologyMap_modelLocalOrientation (g : (Model.{w} n) ≃L[ℝ] (Model.{w} n))
    (ω : Orientation ℝ (Model.{w} n) (Fin (n + 1))) :
    (TopPair.singularHomologyMap g.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).hom
        (modelLocalOrientation ω).val =
      (modelLocalOrientation (ω.map _ g.toLinearEquiv)).val := by
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ (Model.{w} n) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_ulift_fin]
  have hpair : g.complZeroPairIso.hom = TopPair.ofSubsetMap
      (TopCat.ofHom ((g : Model.{w} n →L[ℝ] Model.{w} n) : C(Model.{w} n, Model.{w} n)))
      g.mapsTo_compl_zero := by
    rw [g.complZeroPairIso_hom]
    -- `g` and `g` as a continuous linear map have the same underlying continuous map.
    rfl
  have hsign := singularHomologyMap_continuousLinearMap_compl_zero
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (g : Model.{w} n →L[ℝ] Model.{w} n) g.mapsTo_compl_zero (n + 1)
  rw [hpair, hsign]
  -- The determinant of `g` is nonzero, and the orientation and the local orientation change by
  -- its sign.
  have hdet : LinearMap.det (g.toLinearEquiv : (Model.{w} n) →ₗ[ℝ] (Model.{w} n)) ≠ 0 :=
    (LinearEquiv.isUnit_det' g.toLinearEquiv).ne_zero
  rcases hdet.lt_or_gt with hneg | hpos
  · rw [(ω.map_eq_neg_iff_det_neg _ hcard).2 hneg, modelLocalOrientation_neg,
      LocalOrientation.coe_neg]
    simp [ContinuousLinearMap.det, sign_neg hneg]
  · rw [(ω.map_eq_iff_det_pos _ hcard).2 hpos]
    simp [ContinuousLinearMap.det, sign_pos hpos]

/-- A linear isomorphism of local homology groups carries local orientations to local
orientations. -/
private theorem isLocalOrientation_singularHomologyMap_inv (L : F ≃L[ℝ] G)
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({0} : Set G) (n + 1)}
    (hz : IsLocalOrientation 0 (n + 1) z) :
    IsLocalOrientation (0 : F) (n + 1)
      ((TopPair.singularHomologyMap L.complZeroPairIso.inv
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).hom z) :=
  hz.map
    { hom := TopPair.singularHomologyMap L.complZeroPairIso.inv
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
      inv := TopPair.singularHomologyMap L.complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
      hom_inv_id := by
        rw [← TopPair.singularHomologyMap_comp, Iso.inv_hom_id, TopPair.singularHomologyMap_id]
      inv_hom_id := by
        rw [← TopPair.singularHomologyMap_comp, Iso.hom_inv_id, TopPair.singularHomologyMap_id] }

/-- The local orientation of the model, carried to `F` by a continuous linear equivalence
`L` to the Euclidean model, together with the orientation. -/
private def localOrientationVia (ω : Orientation ℝ F (Fin (n + 1))) (L : F ≃L[ℝ] (Model.{w} n)) :
    LocalOrientation F 0 (n + 1) :=
  ⟨(TopPair.singularHomologyMap L.complZeroPairIso.inv (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).hom
      (modelLocalOrientation (ω.map _ L.toLinearEquiv)).val,
    isLocalOrientation_singularHomologyMap_inv L (modelLocalOrientation _).property⟩

/-- The local orientation carried along `L` does not depend on `L`. -/
private theorem localOrientationVia_eq (ω : Orientation ℝ F (Fin (n + 1)))
    (L L' : F ≃L[ℝ] (Model.{w} n)) : localOrientationVia ω L = localOrientationVia ω L' := by
  -- `L'` is `L` followed by the automorphism `g = L⁻¹ ≫ L'` of the model.
  set g := L.symm.trans L'
  have hω : ω.map _ L'.toLinearEquiv = (ω.map _ L.toLinearEquiv).map _ g.toLinearEquiv := by
    have hL : L.toLinearEquiv.trans g.toLinearEquiv = L'.toLinearEquiv := by
      ext x
      simp [g]
    rw [← Orientation.map_trans, hL]
  have hpair : g.complZeroPairIso.hom ≫ L'.complZeroPairIso.inv = L.complZeroPairIso.inv := by
    rw [g.complZeroPairIso_hom, L'.complZeroPairIso_inv, L.complZeroPairIso_inv]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext; simp [g])
  apply Subtype.ext
  simp only [localOrientationVia]
  rw [hω, ← singularHomologyMap_modelLocalOrientation, ← ModuleCat.comp_apply,
    ← TopPair.singularHomologyMap_comp, hpair]

/-- **The local orientation selected by an orientation.** An orientation `ω` of a real normed
space `F` of dimension `n + 1` selects the generator of `Hₙ₊₁(F, F ∖ {0}; ℤ)` carried from the
oriented-chart generator (`OpenPartialHomeomorph.localOrientationOfOrientedChart`) of the model
`EuclideanSpace ℝ (ULift (Fin (n + 1)))`, oriented by `ω.map L`, along any continuous linear
equivalence `L` from `F` to the model. It does not depend on `L`
(`Orientation.localOrientation_map`). -/
def localOrientation (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) :
    LocalOrientation F 0 (n + 1) :=
  haveI := FiniteDimensional.of_finrank_eq_succ hF
  localOrientationVia ω
    (ContinuousLinearEquiv.ofFinrankEq (hF.trans (finrank_euclideanSpace_ulift_fin (n + 1)).symm))

private theorem localOrientation_eq_localOrientationVia (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) (L : F ≃L[ℝ] (Model.{w} n)) :
    ω.localOrientation hF = localOrientationVia ω L :=
  localOrientationVia_eq ω _ L

/-- On the Euclidean model `EuclideanSpace ℝ (ULift (Fin (n + 1)))`, the local orientation
selected by `ω` is the oriented-chart generator of the identity chart. -/
theorem localOrientation_euclideanSpace
    (ω : Orientation ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) (Fin (n + 1)))
    (hE : finrank ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) = n + 1) :
    ω.localOrientation hE = (OpenPartialHomeomorph.refl _).localOrientationOfOrientedChart
      (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _) ω hE := by
  rw [localOrientation_eq_localOrientationVia ω hE (ContinuousLinearEquiv.refl ℝ _)]
  apply Subtype.ext
  have hpair : (ContinuousLinearEquiv.refl ℝ (Model.{w} n)).complZeroPairIso.inv = 𝟙 _ := by
    rw [ContinuousLinearEquiv.complZeroPairIso_inv]
    exact TopPair.ofSubsetMap_id _
  have hω : ω.map _ (ContinuousLinearEquiv.refl ℝ (Model.{w} n)).toLinearEquiv = ω := by
    have hrefl : (ContinuousLinearEquiv.refl ℝ (Model.{w} n)).toLinearEquiv =
        LinearEquiv.refl ℝ _ := by
      ext x
      simp
    rw [hrefl, Orientation.map_refl, Equiv.refl_apply]
  simp only [localOrientationVia, hpair, TopPair.singularHomologyMap_id, ModuleCat.id_apply, hω]
  -- Both sides are the oriented-chart generator of the identity chart.
  rfl

/-- **Naturality of the selected local orientations.** A continuous linear equivalence
`f : F ≃L[ℝ] G` carries the local orientation selected by `ω` to the local orientation selected by
the transported orientation `ω.map f`. -/
theorem localOrientation_map (f : F ≃L[ℝ] G) (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) (hG : finrank ℝ G = n + 1) :
    ((ω.map _ f.toLinearEquiv).localOrientation hG).val =
      (TopPair.singularHomologyMap f.complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).hom
        (ω.localOrientation hF).val := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  let L : F ≃L[ℝ] (Model.{w} n) :=
    ContinuousLinearEquiv.ofFinrankEq (hF.trans (finrank_euclideanSpace_ulift_fin (n + 1)).symm)
  -- Read both local orientations through `L`, and through `f⁻¹ ≫ L` on `G`.
  have hω : (ω.map _ f.toLinearEquiv).map _ (f.symm.trans L).toLinearEquiv =
      ω.map _ L.toLinearEquiv := by
    have hL : f.toLinearEquiv.trans (f.symm.trans L).toLinearEquiv = L.toLinearEquiv := by
      ext x
      simp
    rw [← Orientation.map_trans, hL]
  have hpair : (f.symm.trans L).complZeroPairIso.inv =
      L.complZeroPairIso.inv ≫ f.complZeroPairIso.hom := by
    rw [(f.symm.trans L).complZeroPairIso_inv, L.complZeroPairIso_inv, f.complZeroPairIso_hom]
    exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext; simp)).symm
  rw [localOrientation_eq_localOrientationVia _ hG (f.symm.trans L),
    localOrientation_eq_localOrientationVia _ hF L]
  simp only [localOrientationVia]
  rw [hω, hpair, TopPair.singularHomologyMap_comp, ModuleCat.comp_apply]

/-- Reversing an orientation reverses the local orientation it selects. -/
@[simp]
theorem localOrientation_neg (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) :
    (-ω).localOrientation hF = -ω.localOrientation hF := by
  apply Subtype.ext
  simp only [localOrientation, localOrientationVia, Orientation.map_neg, modelLocalOrientation_neg,
    LocalOrientation.coe_neg, map_neg]

end Orientation
