/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Base change in the over category of schemes

Mathlib proves stability of `LocallyOfFiniteType` and `QuasiCompact` under `Limits.pullback`,
which yields `LocallyOfFiniteType (pullback.snd Y.hom f)` and `CompactSpace (pullback Y.hom f)`
directly. Because `CategoryTheory.Over.pullback` is not reducible, typeclass search on objects of
`Over S'` obtained via `(Over.pullback f).obj Y` does not unfold the underlying scheme or
structure morphism automatically. This file registers the corresponding instances on
`((Over.pullback f).obj Y).hom` and `((Over.pullback f).obj Y).left` for arbitrary base-change
morphisms of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.locallyOfFiniteType_over_pullback_obj_hom`: base change along any
  morphism of schemes preserves `LocallyOfFiniteType` on structure morphisms in `Over`.
* `TauCeti.AlgebraicGeometry.compactSpace_over_pullback_obj_left`: base change along a
  quasi-compact morphism of schemes preserves `CompactSpace` on underlying schemes in `Over`.
* `Over.Hom.morphismRestrictPullbackMapIso` identifies open restriction with base change.
* `Over.pullback_map_injective_of_isSchemeTheoreticallyDominant` uses schematic density and
  separatedness, and `Over.Hom.isSplitEpi_of_surjective_pullback_map` lifts sections.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace CategoryTheory.Over.Hom

variable {T S : Scheme.{u}} {X Y : Over S} (m : X ⟶ Y) (j : T ⟶ S) [IsOpenImmersion j]

/-- The arrow comparison together with its projection equations. -/
private noncomputable def morphismRestrictPullbackMapIsoWithProjections :
    {e : Arrow.mk (m.left ∣_ Y.hom ⁻¹ᵁ j.opensRange) ≅ Arrow.mk ((Over.pullback j).map m).left //
      e.hom.left ≫ pullback.fst X.hom j = (m.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ j.opensRange)).ι ∧
      e.hom.right ≫ pullback.fst Y.hom j = (Y.hom ⁻¹ᵁ j.opensRange).ι} := by
  have sq := Over.isPullback_pullback_map_left j m
  rw [Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y.hom j).flip]
  refine ⟨m.left.morphismRestrictArrowIso _ sq.w.symm
    (Scheme.preimage_opensRange_of_isPullback sq), ?_, ?_⟩ <;> simp

/-- Base change of `m` along the open immersion `j` identifies its underlying arrow with
the restriction of `m.left` to the inverse image of `j.opensRange`. -/
noncomputable def morphismRestrictPullbackMapIso :
    Arrow.mk (m.left ∣_ Y.hom ⁻¹ᵁ j.opensRange) ≅ Arrow.mk ((Over.pullback j).map m).left :=
  (morphismRestrictPullbackMapIsoWithProjections m j).val

/-- The source comparison commutes with the first pullback projection. -/
@[reassoc (attr := simp)]
theorem morphismRestrictPullbackMapIso_hom_left_fst :
    (m.morphismRestrictPullbackMapIso j).hom.left ≫ pullback.fst X.hom j =
      (m.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ j.opensRange)).ι :=
  (morphismRestrictPullbackMapIsoWithProjections m j).property.1

/-- The target comparison commutes with the first pullback projection. -/
@[reassoc (attr := simp)]
theorem morphismRestrictPullbackMapIso_hom_right_fst :
    (m.morphismRestrictPullbackMapIso j).hom.right ≫ pullback.fst Y.hom j =
      (Y.hom ⁻¹ᵁ j.opensRange).ι :=
  (morphismRestrictPullbackMapIsoWithProjections m j).property.2

/-- Base change of `m` along the open immersion `j` is an isomorphism exactly when its
underlying morphism restricts to an isomorphism over the inverse image of `j.opensRange`. -/
theorem isIso_pullback_map_iff_of_isOpenImmersion :
    IsIso ((Over.pullback j).map m) ↔ IsIso (m.left ∣_ Y.hom ⁻¹ᵁ j.opensRange) :=
  (isIso_iff_of_reflects_iso ((Over.pullback j).map m) (Over.forget _)).symm.trans
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (m.morphismRestrictPullbackMapIso j)).symm

end CategoryTheory.Over.Hom

/-- Base change is injective on morphisms from a scheme with schematically dense pullback
to a separated target over the same base. -/
theorem CategoryTheory.Over.pullback_map_injective_of_isSchemeTheoreticallyDominant
    {T S : Scheme.{u}} (j : T ⟶ S) {X Y : Over S} [IsSeparated Y.hom]
    [IsSchemeTheoreticallyDominant (pullback.fst X.hom j)] :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := by
  intro f g h
  exact Over.OverMorphism.ext (TauCeti.ext_of_isSchemeTheoreticallyDominant (pullback.fst X.hom j)
    Y.hom ((Over.w f).trans (Over.w g).symm) ((Over.pullback_map_eq_map_iff j f g).mp h))

/-- A section after base change gives a section over the base if base change is surjective
on morphisms in the reverse direction and the target is separated with schematically dense
pullback. -/
theorem CategoryTheory.Over.Hom.isSplitEpi_of_surjective_pullback_map {η S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y) {j : η ⟶ S} [IsSeparated Y.hom]
    [IsSchemeTheoreticallyDominant (pullback.fst Y.hom j)]
    [IsSplitEpi ((Over.pullback j).map f)]
    (h : Function.Surjective ((Over.pullback j).map : (Y ⟶ X) → _)) : IsSplitEpi f := by
  obtain ⟨g, hg⟩ := h (section_ ((Over.pullback j).map f))
  refine IsSplitEpi.mk' ⟨g, Over.pullback_map_injective_of_isSchemeTheoreticallyDominant j ?_⟩
  rw [Functor.map_comp, hg, IsSplitEpi.id, Functor.map_id]

namespace TauCeti

namespace AlgebraicGeometry

/-- Base change along any morphism of schemes preserves `LocallyOfFiniteType` of the structure
morphism of an object in `Over S`. -/
instance locallyOfFiniteType_over_pullback_obj_hom {S S' : Scheme.{u}} (f : S' ⟶ S)
    (Y : Over S) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType ((Over.pullback f).obj Y).hom := by
  dsimp only [Over.pullback, Over.mk_hom]
  infer_instance

/-- Base change along a quasi-compact morphism of schemes preserves quasi-compactness of the
underlying topological space of an object in `Over S`. -/
instance compactSpace_over_pullback_obj_left {S S' : Scheme.{u}} (f : S' ⟶ S) [QuasiCompact f]
    (Y : Over S) [CompactSpace Y.left] :
    CompactSpace ((Over.pullback f).obj Y).left := by
  dsimp only [Over.pullback, Over.mk_left]
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst Y.hom f)

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical comparison for two successive base changes is a pullback square. -/
theorem isPullback_pullbackLeftPullbackSndIso_inv_fst
    {S T Z L : Scheme.{u}} (z : Z ⟶ S) (d : T ⟶ S) (t : L ⟶ T) :
    IsPullback
      ((pullbackLeftPullbackSndIso z d t).inv ≫
        pullback.fst (pullback.snd z d) t)
      (pullback.snd z (t ≫ d)) (pullback.snd z d) t := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (pullbackLeftPullbackSndIso z d t).symm rfl ?_
  · simp [Category.assoc]
  · exact pullbackLeftPullbackSndIso_inv_snd_snd z d t


/-- Restricting the square for two successive base changes along compatible opens gives a
pullback square, compatibly with both open inclusions. -/
theorem restricted_composite_projection_square
    {S T Z L : Scheme.{u}} (z : Z ⟶ S) (d : T ⟶ S) (t : L ⟶ T)
    (VB : (pullback z d).Opens) (VL : (pullback z (t ≫ d)).Opens) (W : S.Opens)
    (hVL : VL = ((pullbackLeftPullbackSndIso z d t).inv ≫
      pullback.fst (pullback.snd z d) t) ⁻¹ᵁ VB)
    (q : VB.toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι = VB.ι ≫ pullback.snd z d) :
    let WL := t ⁻¹ᵁ (d ⁻¹ᵁ W)
    ∃ (nV : VL.toScheme ⟶ VB.toScheme) (qL : VL.toScheme ⟶ WL.toScheme),
      IsPullback nV qL q (t.resLE (d ⁻¹ᵁ W) WL le_rfl) ∧
      nV ≫ VB.ι = VL.ι ≫ (pullbackLeftPullbackSndIso z d t).inv ≫
        pullback.fst (pullback.snd z d) t ∧
      qL ≫ WL.ι = VL.ι ≫ pullback.snd z (t ≫ d) := by
  let WT := d ⁻¹ᵁ W
  let WL := t ⁻¹ᵁ WT
  let n := (pullbackLeftPullbackSndIso z d t).inv ≫ pullback.fst (pullback.snd z d) t
  have hn₂ : n ≫ pullback.snd z d = pullback.snd z (t ≫ d) ≫ t := by simp [n]
  have eVB : VB ≤ (pullback.snd z d) ⁻¹ᵁ WT := by
    intro x hx
    have hh := congrArg (fun k ↦ k ⟨x, hx⟩) hq
    -- Expose the underlying points of the open inclusions in the commutative square.
    change (q ⟨x, hx⟩).val = pullback.snd z d x at hh
    -- Expose preimage membership to use the pointwise square equality.
    change pullback.snd z d x ∈ WT
    rw [← hh]
    exact (q ⟨x, hx⟩).property
  have eVL : VL ≤ (pullback.snd z (t ≫ d)) ⁻¹ᵁ WL := by
    rw [hVL]
    have hh := congrArg (fun k ↦ k ⁻¹ᵁ WT) hn₂
    have hh' : n ⁻¹ᵁ ((pullback.snd z d) ⁻¹ᵁ WT) =
        (pullback.snd z (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT) := by
      simpa only [Scheme.Hom.comp_preimage] using hh
    exact (n.preimage_mono eVB).trans_eq hh'
  have hq' : (pullback.snd z d).resLE WT VB eVB = q := by
    rw [← cancel_mono WT.ι]
    exact (Scheme.Hom.resLE_comp_ι _ _).trans hq.symm
  refine ⟨n.resLE VB VL hVL.le, (pullback.snd z (t ≫ d)).resLE WL VL eVL, ?_, ?_,
    Scheme.Hom.resLE_comp_ι _ _⟩
  · have h := Scheme.Hom.isPullback_resLE
      (Scheme.Hom.isPullback_pullbackLeftPullbackSndIso_inv_fst z d t)
      (le_rfl : WL ≤ t ⁻¹ᵁ WT) eVB (UY := VL)
      (by rw [← hVL, inf_eq_left.mpr eVL])
    rw [hq'] at h
    exact h
  · simpa only [n, Category.assoc] using Scheme.Hom.resLE_comp_ι n hVL.le

/-- Restriction of an over-morphism commutes with a further base change, as an isomorphism
of arrows. -/
theorem restricted_composite_base_change
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens) (W : S.Opens)
    (q : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι =
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).ι ≫ pullback.snd Y₀.hom d)
    (L : Scheme.{u}) (t : L ⟶ T) :
    let g := (((Over.pullback d).map f₀).left) ∣_
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)
    let s := t.resLE (d ⁻¹ᵁ W) _ le_rfl
    Nonempty
      (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
      Arrow.mk (pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _)
        (by simp) (by simp))) := by
  dsimp only
  let fT := ((Over.pullback d).map f₀).left
  let fL := ((Over.pullback (t ≫ d)).map f₀).left
  let VB := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  let UC := fT ⁻¹ᵁ VB
  let VL := (pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V
  let UL := fL ⁻¹ᵁ VL
  let WT := d ⁻¹ᵁ W
  let WL := t ⁻¹ᵁ WT
  let nY := (pullbackLeftPullbackSndIso Y₀.hom d t).inv ≫
    pullback.fst (pullback.snd Y₀.hom d) t
  let nX := (pullbackLeftPullbackSndIso X₀.hom d t).inv ≫
    pullback.fst (pullback.snd X₀.hom d) t
  have hn : nX ≫ fT = fL ≫ nY := by
    apply pullback.hom_ext <;> simp [nX, nY, fT, fL, Over.pullback_map_left]
  have hqc : ((fT ∣_ VB) ≫ q) ≫ WT.ι = UC.ι ≫ pullback.snd X₀.hom d := by
    simp only [Category.assoc]
    -- Expose the local WT and VB aliases in the supplied restriction equation.
    rw [show q ≫ WT.ι = VB.ι ≫ pullback.snd Y₀.hom d from hq]
    simp only [morphismRestrict_ι_assoc, fT, Over.pullback_map_left, pullback.lift_snd]
    rfl
  have hVL : VL = nY ⁻¹ᵁ VB := by
    dsimp [VL, VB]
    rw [← Scheme.Hom.comp_preimage]
    simp [nY]
  have hUL : UL = nX ⁻¹ᵁ UC := by
    change fL ⁻¹ᵁ VL = nX ⁻¹ᵁ (fT ⁻¹ᵁ VB) -- Expose the source inverse images.
    rw [hVL]
    exact (congrArg (fun k ↦ k ⁻¹ᵁ VB) hn).symm
  obtain ⟨nB, qB, hB, hnB, hqB⟩ :=
    restricted_composite_projection_square Y₀.hom d t VB VL W hVL q hq
  obtain ⟨nC, qC, hC, hnC, hqC⟩ :=
    restricted_composite_projection_square X₀.hom d t UC UL W hUL ((fT ∣_ VB) ≫ q) hqc
  have hRT : (fT ∣_ VB) ≫ VB.ι = UC.ι ≫ fT := morphismRestrict_ι fT VB
  have hRL : (fL ∣_ VL) ≫ VL.ι = UL.ι ≫ fL := morphismRestrict_ι fL VL
  refine ⟨Arrow.isoMk hC.isoPullback hB.isoPullback ?_⟩
  dsimp only [Arrow.mk_hom]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [reassoc_of% hC.isoPullback_hom_fst, hB.isoPullback_hom_fst]
    rw [← cancel_mono VB.ι]
    simp only [Category.assoc]
    rw [hRT, reassoc_of% hnC, hnB, reassoc_of% hRL]
    simpa only [nX, nY, Category.assoc] using congrArg (fun k ↦ UL.ι ≫ k) hn
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [hC.isoPullback_hom_snd, hB.isoPullback_hom_snd]
    rw [← cancel_mono WL.ι]
    rw [hqC, Category.assoc, hqB, reassoc_of% hRL]
    simp [fL, Over.pullback_map_left]

end AlgebraicGeometry.Scheme.Hom
