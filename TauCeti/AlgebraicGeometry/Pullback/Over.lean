/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Finiteness and quasi-compactness under `Over.pullback` of schemes

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
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

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

universe u

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
