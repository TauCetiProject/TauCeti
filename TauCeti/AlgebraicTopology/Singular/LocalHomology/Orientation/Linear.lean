/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup
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
Since `Hₙ₊₁(F, F ∖ {0}; ℤ)` is a copy of `ℤ`, it has exactly two generators, so the selection is a
bijection between the two orientations of `F` and its two local orientations at the origin
(`Orientation.localOrientationEquiv`).

These are the fibrewise normalizations of the Thom class of an oriented real vector bundle: the
fibres of the bundle are identified with a model fibre by linear equivalences, an orientation of
the bundle orients every fibre, and by naturality the selected generator of a fibre does not depend
on the identification used.

## Main definitions

* `Orientation.localOrientation`: the local orientation at the origin selected by an orientation.
* `Orientation.localOrientationEquiv`: orientations correspond bijectively to local orientations
  at the origin.
* `TauCeti.orientationModule`: the integral local homology at the origin in the dimension of
  the space.
* `TauCeti.singularHomologyComplZeroIso`: the integral local homology of `F` at the origin in
  the top degree is one copy of `ℤ`.

## Main results

* `TauCeti.orientationModule.instInvertible`, `TauCeti.finrank_orientationModule`: in finite
  dimension the orientation module is invertible and has rank one, including in dimension zero.
* `Orientation.localOrientation_map`: continuous linear equivalences carry the selected local
  orientations to each other.
* `Orientation.localOrientation_neg`: reversing the orientation reverses the local orientation.
* `Orientation.localOrientation_injective`, `Orientation.localOrientation_surjective`: the
  selection is a bijection; `Orientation.localOrientation_inj` is the injectivity as an iff.
* `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`: in a real inner product
  space it is the oriented-chart generator of the identity chart, by comparison with the Euclidean
  model through a linear isometry
  (`LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl`).
* `OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart`: an oriented
  chart, centred at a point and followed by a continuous linear equivalence `L`, carries the local
  orientation it selects to the local orientation selected by the transported orientation.

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

namespace TauCeti

variable (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral orientation module of a real normed space: its local homology at the origin
in degree `dim E`. -/
abbrev orientationModule :=
  localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({0} : Set E)
    (finrank ℝ E)

instance orientationModule.instInvertible [FiniteDimensional ℝ E] :
    Module.Invertible ℤ (orientationModule E) :=
  Module.Invertible.congr (localHomologySingletonLinearEquiv (ModuleCat.of ℤ (ULift.{w} ℤ))
    rfl ULift.moduleEquiv (0 : E)).symm

/-- The integral orientation module has rank one, also for a zero-dimensional space. -/
@[simp]
theorem finrank_orientationModule [FiniteDimensional ℝ E] :
    finrank ℤ (orientationModule E) = 1 :=
  Module.Invertible.finrank_eq_one ℤ (orientationModule E)

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- The integral local homology of a real normed space `F` of dimension `n + 1` at the origin in
degree `n + 1` is one copy of `ℤ`, computed in the identity chart. -/
def singularHomologyComplZeroIso (hF : finrank ℝ F = n + 1) :
    localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({0} : Set F) (n + 1) ≅
      ModuleCat.of ℤ (ULift.{w} ℤ) :=
  singularHomologyComplSingletonIsoOfFinrankEq _ (OpenPartialHomeomorph.refl F)
    (Set.mem_univ (0 : F)) hF

end TauCeti

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
    (OpenPartialHomeomorph.mem_refl_source _) ω
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
private theorem localOrientation_euclideanSpace
    (ω : Orientation ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) (Fin (n + 1)))
    (hE : finrank ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) = n + 1) :
    ω.localOrientation hE = (OpenPartialHomeomorph.refl _).localOrientationOfOrientedChart
      (OpenPartialHomeomorph.mem_refl_source _) ω hE := by
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

/-- Distinct orientations select distinct local orientations. -/
theorem localOrientation_injective (hF : finrank ℝ F = n + 1) :
    Function.Injective fun ω : Orientation ℝ F (Fin (n + 1)) ↦ ω.localOrientation hF := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  intro ω ω' h
  simp only at h
  rcases ω.eq_or_eq_neg ω' (by rw [Nat.card_fin, hF]) with h' | h'
  · exact h'
  · rw [h', localOrientation_neg] at h
    exact absurd (congrArg Subtype.val h)
      ((ω'.localOrientation hF).property.neg_ne (singularHomologyComplZeroIso hF))

/-- Two orientations select the same local orientation exactly when they are equal. -/
@[simp]
theorem localOrientation_inj {ω ω' : Orientation ℝ F (Fin (n + 1))} (hF : finrank ℝ F = n + 1) :
    ω.localOrientation hF = ω'.localOrientation hF ↔ ω = ω' :=
  (localOrientation_injective hF).eq_iff

/-- Every local orientation of `F` at the origin is selected by an orientation of `F`. -/
theorem localOrientation_surjective (hF : finrank ℝ F = n + 1) :
    Function.Surjective fun ω : Orientation ℝ F (Fin (n + 1)) ↦ ω.localOrientation hF := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  intro z
  let ω : Orientation ℝ F (Fin (n + 1)) := (Module.finBasisOfFinrankEq ℝ F hF).orientation
  rcases LocalOrientation.eq_or_eq_neg (singularHomologyComplZeroIso hF) z (ω.localOrientation hF)
    with h | h
  · exact ⟨ω, h.symm⟩
  · exact ⟨-ω, by simp [h]⟩

/-- **Orientations and local orientations of a vector space.** For a real normed space `F` of
dimension `n + 1`, `Orientation.localOrientation` is a bijection between the orientations of `F`
and the generators of `Hₙ₊₁(F, F ∖ {0}; ℤ)`. -/
def localOrientationEquiv (hF : finrank ℝ F = n + 1) :
    Orientation ℝ F (Fin (n + 1)) ≃ LocalOrientation F 0 (n + 1) :=
  Equiv.ofBijective _ ⟨localOrientation_injective hF, localOrientation_surjective hF⟩

@[simp]
theorem localOrientationEquiv_apply (hF : finrank ℝ F = n + 1)
    (ω : Orientation ℝ F (Fin (n + 1))) :
    localOrientationEquiv hF ω = ω.localOrientation hF :=
  (rfl)

@[simp]
theorem localOrientation_localOrientationEquiv_symm (hF : finrank ℝ F = n + 1)
    (z : LocalOrientation F 0 (n + 1)) :
    ((localOrientationEquiv hF).symm z).localOrientation hF = z :=
  (localOrientationEquiv hF).apply_symm_apply z

@[simp]
theorem localOrientationEquiv_symm_localOrientation (hF : finrank ℝ F = n + 1)
    (ω : Orientation ℝ F (Fin (n + 1))) :
    (localOrientationEquiv hF).symm (ω.localOrientation hF) = ω :=
  (localOrientationEquiv hF).symm_apply_apply ω

end Orientation

namespace TauCeti

section InnerProduct

variable {X Y : Type w} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {n : ℕ}

/-- A linear isometry carries the local orientation at the origin selected by `ν` in the identity
chart to the one selected by the transported orientation in the identity chart: both are read
through the connecting morphism, radial projection, and the sphere generators, which the isometry
preserves. -/
theorem _root_.LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl
    (f : X ≃ₗᵢ[ℝ] Y) (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1)
    (hY : finrank ℝ Y = n + 1)
    (h : (⟨f, f.continuous⟩ : C(X, Y)) ⁻¹' {0} ⊆ {0}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (⟨f, f.continuous⟩ : C(X, Y)) h (n + 1)
        ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
          (OpenPartialHomeomorph.mem_refl_source _) ν hX).val =
      ((OpenPartialHomeomorph.refl Y).localOrientationOfOrientedChart
        (OpenPartialHomeomorph.mem_refl_source _)
        (ν.map _ f.toLinearEquiv) hY).val := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let eX := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl X)
    (OpenPartialHomeomorph.mem_refl_source 0) ν hX
  let eY := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl Y)
    (OpenPartialHomeomorph.mem_refl_source 0) (ν.map _ f.toLinearEquiv) hY
  -- Radial projection onto the unit spheres commutes with the isometry.
  have hsq : TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of X) (Y := TopCat.of Y)
        (TopCat.ofHom (⟨f, f.continuous⟩ : C(X, Y))) (B := {0}ᶜ) (B' := {0}ᶜ)
        ((Set.mapsTo_preimage _ _).mono_left (Set.compl_subset_compl.2 h))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : Y)).toFun =
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : X)).toFun ≫
        TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
          f.toLinearIsometry.continuous_unitSphereMap⟩ := by
    exact f.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere 0 0 f.map_zero
  have key : localHomologyMap R (⟨f, f.continuous⟩ : C(X, Y)) h (n + 1) ≫ eY.hom = eX.hom := by
    simp only [eX, eY, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    rw [localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
    congr 1
    -- The composite is only type-correct after unfolding the subspace of the pair.
    erw [← Functor.map_comp_assoc, hsq, Functor.map_comp_assoc]
    exact congrArg _ (reducedSingularHomologySphereIsoOfOrientation_hom_naturality R ν
      (ν.map _ f.toLinearEquiv) f rfl hX)
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso eY.hom).1
  rw [← ConcreteCategory.comp_apply, key]
  exact (eX.inv_hom_id_apply 1).trans (eY.inv_hom_id_apply 1).symm

end InnerProduct

end TauCeti

namespace Orientation

variable {X : Type w} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {n : ℕ}

/-- **The local orientation of an orientation in the identity chart.** In a real inner product
space `X` of dimension `n + 1`, the local orientation at the origin selected by an orientation `ν`
(`Orientation.localOrientation`) is the one selected by `ν` in the identity chart of `X`. -/
theorem localOrientation_eq_localOrientationOfOrientedChart_refl
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1) :
    ν.localOrientation hX = (OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
      (OpenPartialHomeomorph.mem_refl_source _) ν hX := by
  have := FiniteDimensional.of_finrank_eq_succ hX
  -- Compare both with the Euclidean model through a linear isometry.
  let f : X ≃ₗᵢ[ℝ] Model.{w} n :=
    ((stdOrthonormalBasis ℝ X).reindex ((finCongr hX).trans Equiv.ulift.symm)).repr
  have hM : finrank ℝ (Model.{w} n) = n + 1 := finrank_euclideanSpace_ulift_fin (n + 1)
  have hmap := localOrientation_map f.toContinuousLinearEquiv ν hX hM
  rw [localOrientation_euclideanSpace] at hmap
  apply Subtype.ext
  apply (ConcreteCategory.bijective_of_isIso (TopPair.singularHomologyMap
    f.toContinuousLinearEquiv.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))).1
  rw [← LocalOrientation.coe_map, ← hmap, ContinuousLinearEquiv.complZeroPairIso_hom]
  have h := f.localHomologyMap_localOrientationOfOrientedChart_refl ν hX hM
    (fun x hx ↦ by simpa using hx)
  rw [← localHomologyMap_def]
  exact h.symm

end Orientation

namespace TauCeti

section Chart

variable {M X F : Type w} [TopologicalSpace M] [T1Space M] [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **An oriented chart, followed by a linear equivalence, reads the local orientation it selects
as the local orientation of the transported orientation.** Let `φ` be a chart of `M` with values in
a real inner product space `X`, `ν` an orientation of `X`, and `L : X ≃L[ℝ] F` a linear
equivalence. The map `x ↦ L (φ x - φ z)` on the source of `φ` carries the local orientation of `M`
at `z` selected by `ν` in `φ`, read in the source through excision, to the local orientation of `F`
at the origin selected by the transported orientation `ν.map L`. -/
theorem _root_.OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M X) {z : M} (hz : z ∈ φ.source) (L : X ≃L[ℝ] F)
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1) (hF : finrank ℝ F = n + 1)
    (h : (((L : X →L[ℝ] F) : C(X, F)).comp
      ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(X, X)).comp φ.sourceRestrict)) ⁻¹' {0} ⊆ {⟨z, hz⟩}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ))
        (((L : X →L[ℝ] F) : C(X, F)).comp
          ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(X, X)).comp φ.sourceRestrict))
        (S := {⟨z, hz⟩}) (T := {0}) h (n + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
          (φ.localOrientationOfOrientedChart hz ν hX)).val =
      ((ν.map _ L.toLinearEquiv).localOrientation hF).val := by
  set Z := ModuleCat.of ℤ (ULift.{w} ℤ)
  set c := ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
    (φ.localOrientationOfOrientedChart hz ν hX)).val
  -- Factor the canonical map into the restricted chart, the centering translation, and `L`.
  set sR := φ.sourceRestrict
  let T : C(X, X) := ⟨fun y ↦ y - φ z, by fun_prop⟩
  let Lc : C(X, F) := ((L : X →L[ℝ] F) : C(X, F))
  have hsR : sR ⁻¹' {φ z} ⊆ {⟨z, hz⟩} := fun x hx ↦ Subtype.ext (φ.sourceRestrict_preimage hz hx)
  have hT : T ⁻¹' {0} ⊆ {φ z} := fun y hy ↦ sub_eq_zero.1 hy
  have hL : Lc ⁻¹' {0} ⊆ {0} := fun y hy ↦ by simpa [Lc] using hy
  have hcomp : localHomologyMap Z (Lc.comp (T.comp sR)) h (n + 1) =
      localHomologyMap Z sR hsR (n + 1) ≫
      localHomologyMap Z T hT (n + 1) ≫ localHomologyMap Z Lc hL (n + 1) := by
    rw [localHomologyMap_comp, localHomologyMap_comp,
      localHomologyMap_congr Z (ContinuousMap.comp_assoc Lc T sR).symm]
  -- The restricted chart carries `c` to the local orientation of `X` at `φ z` selected by `ν` in
  -- the identity chart.
  have hA := φ.localHomologyMap_sourceRestrict_localOrientationOfOrientedChart hz ν hX hsR
  -- The translation carries it to the local orientation at the origin, which `L` carries to the
  -- local orientation selected by `ν.map L`.
  have hB := localHomologyMap_translate_localOrientationOfOrientedChart_refl
    (OpenPartialHomeomorph.mem_refl_source (φ z)) (OpenPartialHomeomorph.mem_refl_source 0)
    (by simpa only [zero_add] using hT) ν hX
  simp only [zero_add] at hB
  have hC : localHomologyMap Z Lc hL (n + 1)
      ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
        (OpenPartialHomeomorph.mem_refl_source 0) ν hX).val =
      ((ν.map _ L.toLinearEquiv).localOrientation hF).val := by
    rw [Orientation.localOrientation_map L ν hX hF, LocalOrientation.coe_map,
      ← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
      ContinuousLinearEquiv.complZeroPairIso_hom, ← localHomologyMap_def]
  rw [hcomp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hA, hB, hC]

end Chart

end TauCeti
