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
(`Orientation.localOrientation_map`), by transport (`TauCeti.LocalOrientation.map`) along the
isomorphism of pairs `(F, F ∖ {0}) ≅ (G, G ∖ {0})` it induces
(`ContinuousLinearEquiv.complZeroPairIso`). The opposite
orientation selects the opposite local orientation (`Orientation.localOrientation_neg`).

These are the fibrewise normalizations of the Thom class of an oriented real vector bundle: the
fibres of the bundle are identified with a model fibre by linear equivalences, an orientation of
the bundle orients every fibre, and by naturality the selected generator of a fibre does not depend
on the identification used.

## Main definitions

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
private theorem modelLocalOrientation_map (g : (Model.{w} n) ≃L[ℝ] (Model.{w} n))
    (ω : Orientation ℝ (Model.{w} n) (Fin (n + 1))) :
    (modelLocalOrientation ω).map g.complZeroPairIso =
      modelLocalOrientation (ω.map _ g.toLinearEquiv) := by
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ (Model.{w} n) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_ulift_fin]
  have hsign := singularHomologyMap_continuousLinearMap_compl_zero
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (g : Model.{w} n →L[ℝ] Model.{w} n) g.mapsTo_compl_zero (n + 1)
  apply Subtype.ext
  rw [LocalOrientation.coe_map, g.complZeroPairIso_hom, hsign]
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

/-- The local orientation of the model, carried to `F` by a continuous linear equivalence
`L` to the Euclidean model, together with the orientation. -/
private def localOrientationVia (ω : Orientation ℝ F (Fin (n + 1))) (L : F ≃L[ℝ] (Model.{w} n)) :
    LocalOrientation F 0 (n + 1) :=
  (modelLocalOrientation (ω.map _ L.toLinearEquiv)).map L.complZeroPairIso.symm

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
  have hpair : g.complZeroPairIso ≪≫ L'.complZeroPairIso.symm = L.complZeroPairIso.symm := by
    simp [g]
  rw [localOrientationVia, localOrientationVia, hω, ← modelLocalOrientation_map,
    ← LocalOrientation.map_trans, hpair]

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
  have hω : ω.map _ (ContinuousLinearEquiv.refl ℝ (Model.{w} n)).toLinearEquiv = ω := by
    have hrefl : (ContinuousLinearEquiv.refl ℝ (Model.{w} n)).toLinearEquiv =
        LinearEquiv.refl ℝ _ := by
      ext x
      simp
    rw [hrefl, Orientation.map_refl, Equiv.refl_apply]
  simp only [localOrientationVia, ContinuousLinearEquiv.complZeroPairIso_refl, Iso.refl_symm, hω]
  -- Both sides are the oriented-chart generator of the identity chart.
  exact LocalOrientation.map_refl _

/-- **Naturality of the selected local orientations.** A continuous linear equivalence
`f : F ≃L[ℝ] G` carries the local orientation selected by `ω` to the local orientation selected by
the transported orientation `ω.map f`. -/
theorem localOrientation_map (f : F ≃L[ℝ] G) (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) (hG : finrank ℝ G = n + 1) :
    (ω.map _ f.toLinearEquiv).localOrientation hG =
      (ω.localOrientation hF).map f.complZeroPairIso := by
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
  rw [localOrientation_eq_localOrientationVia _ hG (f.symm.trans L),
    localOrientation_eq_localOrientationVia _ hF L, localOrientationVia, localOrientationVia, hω,
    ← LocalOrientation.map_trans, ContinuousLinearEquiv.complZeroPairIso_trans,
    ContinuousLinearEquiv.complZeroPairIso_symm, Iso.trans_symm, Iso.symm_symm_eq]

/-- Reversing an orientation reverses the local orientation it selects. -/
@[simp]
theorem localOrientation_neg (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) :
    (-ω).localOrientation hF = -ω.localOrientation hF := by
  simp only [localOrientation, localOrientationVia, Orientation.map_neg, modelLocalOrientation_neg,
    LocalOrientation.map_neg]

end Orientation
