/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Restrict

/-!
# Target locality of morphisms locally of finite type

A morphism locally of finite type into a sheafy pre-adic space remains locally of finite type
on restricting to any open of its target. Consequently the condition can be checked over any
open cover of the target, independently of the affinoid charts in its definition.

The affinoid restriction theorem supplies finite-type charts after shrinking the target.
Their source opens cover the inverse image of the chosen target open, and the existing source-cover
descent theorem then gives the result for arbitrary morphisms.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.48 and Propositions 8.46 and 8.50.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace

open Huber ValuationSpectrum

universe u

variable {X Y : PreAdicSpace.{u}}

/-- A morphism locally of finite type into a sheafy pre-adic space remains locally of finite
type after restriction over any open of the target. -/
theorem LocallyOfFiniteType.restrictPreimage {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (hY : isSheafy Y) (W : Opens Y) : LocallyOfFiniteType (f.restrictPreimage W) := by
  classical
  let XW := X.restrict ((Opens.map f.base).obj W).isOpenEmbedding
  let YW := Y.restrict W.isOpenEmbedding
  -- Restrict each finite-type chart over `W`, retaining its image as an open of `XW`.
  have hlocal : ∀ x : XW, ∃ K : Opens XW, x ∈ K ∧
      LocallyOfFiniteType (XW.ofRestrict K.isOpenEmbedding ≫ f.restrictPreimage W) := by
    intro x
    obtain ⟨U, hx, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
      hsheaf, eU, eV, hfac⟩ := (locallyOfFiniteType_iff f).mp hf x.1
    let XA := presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP'
    let YA := presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP
    let q := presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf
    let R : Opens YA := (Opens.map eV.inv.base).obj
      ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W)
    have hsA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
        (presentationLimitPresheaf P S.plus) :=
      ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ hY)
    have hq : LocallyOfFiniteType (q.restrictPreimage R) :=
      locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap
        P P' hP hP' φ hφ hsheaf hsA R
    let u := XA.ofRestrict ((Opens.map q.base).obj R).isOpenEmbedding ≫
      eU.inv ≫ X.ofRestrict U.isOpenEmbedding
    let v := YA.ofRestrict R.isOpenEmbedding ≫ eV.inv ≫ Y.ofRestrict V.isOpenEmbedding
    have w : q.restrictPreimage R ≫ v = u ≫ f := by
      dsimp only [u, v]
      rw [Hom.restrictPreimage_ofRestrict_assoc]
      simp only [hfac, Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    let K : Opens XW := (Opens.map (X.ofRestrict
      ((Opens.map f.base).obj W).isOpenEmbedding).base).obj U
    let O : Opens YW := (Opens.map (Y.ofRestrict W.isOpenEmbedding).base).obj V
    let a := XW.ofRestrict K.isOpenEmbedding ≫
      X.ofRestrict ((Opens.map f.base).obj W).isOpenEmbedding
    let b := YW.ofRestrict O.isOpenEmbedding ≫ Y.ofRestrict W.isOpenEmbedding
    -- Compare the restricted charts with the canonical open restrictions, inside `X` and `Y`.
    have hb : Set.range b.base = Set.range v.base := by
      ext y
      constructor
      · rintro ⟨⟨⟨y, hyW⟩, hyV⟩, rfl⟩
        have hi := congrArg (fun g ↦ g.base ⟨y, hyV⟩) eV.hom_inv_id
        refine ⟨⟨eV.hom.base ⟨y, hyV⟩, ?_⟩, ?_⟩
        · exact Opens.mem_map.mpr (Opens.mem_map.mpr (hi.symm ▸ hyW))
        · exact congrArg Subtype.val hi
      · rintro ⟨r, rfl⟩
        exact ⟨⟨⟨v.base r, Opens.mem_map.mp (Opens.mem_map.mp r.2)⟩,
          (eV.inv.base r.1).2⟩, rfl⟩
    have ha : Set.range a.base = Set.range u.base := by
      ext z
      constructor
      · rintro ⟨⟨⟨z, hzW⟩, hzU⟩, rfl⟩
        let z' : X.restrict U.isOpenEmbedding := ⟨z, hzU⟩
        have hz : eU.hom.base z' ∈ (Opens.map q.base).obj R := by
          have hw := congrArg (fun g ↦ g.base z') hfac
          exact Opens.mem_map.mpr (Opens.mem_map.mpr (Opens.mem_map.mpr (hw ▸ hzW)))
        exact ⟨⟨eU.hom.base z', hz⟩,
          congrArg (fun g ↦ (g.base z').1) eU.hom_inv_id⟩
      · rintro ⟨r, rfl⟩
        have hw := congrArg (fun g ↦ g.base r) w
        exact ⟨⟨⟨u.base r, Opens.mem_map.mpr (hw ▸
          Opens.mem_map.mp (Opens.mem_map.mp ((q.restrictPreimage R).base r).2))⟩,
          (eU.inv.base r.1).2⟩, rfl⟩
    let eK := IsOpenImmersion.isoOfRangeEq a u ha
    let eO := IsOpenImmersion.isoOfRangeEq b v hb
    have heq : XW.ofRestrict K.isOpenEmbedding ≫ f.restrictPreimage W =
        eK.hom ≫ q.restrictPreimage R ≫ eO.inv ≫ YW.ofRestrict O.isOpenEmbedding := by
      rw [← cancel_mono (Y.ofRestrict W.isOpenEmbedding)]
      simp only [Category.assoc, Hom.restrictPreimage_ofRestrict]
      rw [IsOpenImmersion.isoOfRangeEq_inv_comp, w,
        IsOpenImmersion.isoOfRangeEq_hom_comp_assoc]
      rfl
    refine ⟨K, hx, ?_⟩
    rw [heq, MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType.{u}]
    have hq' : LocallyOfFiniteType (q.restrictPreimage R ≫ eO.inv) :=
      (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFiniteType.{u} _ _).mpr hq
    simpa only [Category.assoc] using
      hq'.comp_of_isOpenImmersion (YW.ofRestrict O.isOpenEmbedding)
  choose K hxK hK using hlocal
  exact LocallyOfFiniteType.of_iSup_eq_top K
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxK x⟩) hK

/-- Over a sheafy target, being locally of finite type is equivalent to being locally of finite
type over every member of an open cover of the target. -/
theorem locallyOfFiniteType_iff_of_iSup_eq_top {f : X ⟶ Y} (hY : isSheafy Y) {ι : Type*}
    (V : ι → Opens Y) (hV : iSup V = ⊤) :
    LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (f.restrictPreimage (V i)) :=
  ⟨fun hf i ↦ hf.restrictPreimage hY (V i),
    LocallyOfFiniteType.of_iSup_eq_top_restrictPreimage V hV⟩

end TauCeti.PreAdicSpace
