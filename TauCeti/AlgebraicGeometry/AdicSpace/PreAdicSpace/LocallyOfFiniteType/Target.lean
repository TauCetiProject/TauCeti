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

/-- The chart square: restricting `q` over `R` and mapping into `Y` through the chart `v`
agrees with mapping the restricted source chart `u` through `f`. -/
private theorem restrictPreimage_comp_eq_of_chart {f : X ⟶ Y} {U : Opens X} {V : Opens Y}
    {XA YA : PreAdicSpace.{u}} (eU : X.restrict U.isOpenEmbedding ≅ XA)
    (eV : Y.restrict V.isOpenEmbedding ≅ YA) {q : XA ⟶ YA}
    (hfac : X.ofRestrict U.isOpenEmbedding ≫ f =
      eU.hom ≫ q ≫ eV.inv ≫ Y.ofRestrict V.isOpenEmbedding) (R : Opens YA) :
    q.restrictPreimage R ≫ YA.ofRestrict R.isOpenEmbedding ≫ eV.inv ≫
        Y.ofRestrict V.isOpenEmbedding =
      (XA.ofRestrict ((Opens.map q.base).obj R).isOpenEmbedding ≫ eU.inv ≫
        X.ofRestrict U.isOpenEmbedding) ≫ f := by
  rw [Hom.restrictPreimage_ofRestrict_assoc]
  simp only [hfac, Category.assoc, Iso.inv_hom_id_assoc]

/-- The open of `Y` cut out by `W` inside the chart `V` has the same image as the chart
restricted over the pullback of `W`. -/
private theorem range_restrict_chart_target_eq {V W : Opens Y} {YA : PreAdicSpace.{u}}
    (eV : Y.restrict V.isOpenEmbedding ≅ YA) :
    Set.range (((Y.restrict W.isOpenEmbedding).ofRestrict
        ((Opens.map (Y.ofRestrict W.isOpenEmbedding).base).obj V).isOpenEmbedding ≫
        Y.ofRestrict W.isOpenEmbedding).base) =
      Set.range ((YA.ofRestrict ((Opens.map eV.inv.base).obj
        ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W)).isOpenEmbedding ≫
        eV.inv ≫ Y.ofRestrict V.isOpenEmbedding).base) := by
  ext y
  constructor
  · rintro ⟨⟨⟨y, hyW⟩, hyV⟩, rfl⟩
    have hi := congrArg (fun g ↦ g.base ⟨y, hyV⟩) eV.hom_inv_id
    refine ⟨⟨eV.hom.base ⟨y, hyV⟩, ?_⟩, ?_⟩
    · exact Opens.mem_map.mpr (Opens.mem_map.mpr (hi.symm ▸ hyW))
    · exact congrArg Subtype.val hi
  · rintro ⟨r, rfl⟩
    exact ⟨⟨⟨_, Opens.mem_map.mp (Opens.mem_map.mp r.2)⟩, (eV.inv.base r.1).2⟩, rfl⟩

/-- The source analogue of `range_restrict_chart_target_eq`, for a chart square `hfac`. -/
private theorem range_restrict_chart_source_eq {f : X ⟶ Y} {W : Opens Y} {U : Opens X}
    {V : Opens Y} {XA YA : PreAdicSpace.{u}} (eU : X.restrict U.isOpenEmbedding ≅ XA)
    (eV : Y.restrict V.isOpenEmbedding ≅ YA) {q : XA ⟶ YA}
    (hfac : X.ofRestrict U.isOpenEmbedding ≫ f =
      eU.hom ≫ q ≫ eV.inv ≫ Y.ofRestrict V.isOpenEmbedding) :
    Set.range (((X.restrict ((Opens.map f.base).obj W).isOpenEmbedding).ofRestrict
        ((Opens.map (X.ofRestrict ((Opens.map f.base).obj W).isOpenEmbedding).base).obj
          U).isOpenEmbedding ≫ X.ofRestrict ((Opens.map f.base).obj W).isOpenEmbedding).base) =
      Set.range ((XA.ofRestrict ((Opens.map q.base).obj ((Opens.map eV.inv.base).obj
        ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W))).isOpenEmbedding ≫
        eU.inv ≫ X.ofRestrict U.isOpenEmbedding).base) := by
  have w := restrictPreimage_comp_eq_of_chart eU eV hfac
    ((Opens.map eV.inv.base).obj ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W))
  ext z
  constructor
  · rintro ⟨⟨⟨z, hzW⟩, hzU⟩, rfl⟩
    let z' : X.restrict U.isOpenEmbedding := ⟨z, hzU⟩
    have hz : eU.hom.base z' ∈ (Opens.map q.base).obj ((Opens.map eV.inv.base).obj
        ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W)) := by
      have hw := congrArg (fun g ↦ g.base z') hfac
      exact Opens.mem_map.mpr (Opens.mem_map.mpr (Opens.mem_map.mpr (hw ▸ hzW)))
    exact ⟨⟨eU.hom.base z', hz⟩, congrArg (fun g ↦ (g.base z').1) eU.hom_inv_id⟩
  · rintro ⟨r, rfl⟩
    have hw := congrArg (fun g ↦ g.base r) w
    exact ⟨⟨⟨_, Opens.mem_map.mpr (hw ▸ Opens.mem_map.mp (Opens.mem_map.mp
      ((q.restrictPreimage _).base r).2))⟩, (eU.inv.base r.1).2⟩, rfl⟩

/-- If `q` restricted over the pullback of `W` to a chart is locally of finite type, so is the
restriction of `f` over `W` to the part of the source chart `U` lying over `W`. -/
private theorem locallyOfFiniteType_restrict_chart {f : X ⟶ Y} {W : Opens Y} {U : Opens X}
    {V : Opens Y} {XA YA : PreAdicSpace.{u}} (eU : X.restrict U.isOpenEmbedding ≅ XA)
    (eV : Y.restrict V.isOpenEmbedding ≅ YA) {q : XA ⟶ YA}
    (hfac : X.ofRestrict U.isOpenEmbedding ≫ f =
      eU.hom ≫ q ≫ eV.inv ≫ Y.ofRestrict V.isOpenEmbedding)
    (hq : LocallyOfFiniteType (q.restrictPreimage ((Opens.map eV.inv.base).obj
      ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W)))) :
    LocallyOfFiniteType (((X.restrict ((Opens.map f.base).obj W).isOpenEmbedding).ofRestrict
      ((Opens.map (X.ofRestrict ((Opens.map f.base).obj W).isOpenEmbedding).base).obj
        U).isOpenEmbedding) ≫ f.restrictPreimage W) := by
  set R : Opens YA := (Opens.map eV.inv.base).obj
    ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W) with hR
  have w := restrictPreimage_comp_eq_of_chart eU eV hfac R
  let eK := IsOpenImmersion.isoOfRangeEq _ _ (range_restrict_chart_source_eq (W := W) eU eV hfac)
  let eO := IsOpenImmersion.isoOfRangeEq _ _ (range_restrict_chart_target_eq (W := W) eV)
  have heq : ((X.restrict ((Opens.map f.base).obj W).isOpenEmbedding).ofRestrict
      ((Opens.map (X.ofRestrict ((Opens.map f.base).obj W).isOpenEmbedding).base).obj
        U).isOpenEmbedding) ≫ f.restrictPreimage W =
      eK.hom ≫ q.restrictPreimage R ≫ eO.inv ≫ (Y.restrict W.isOpenEmbedding).ofRestrict
        ((Opens.map (Y.ofRestrict W.isOpenEmbedding).base).obj V).isOpenEmbedding := by
    rw [← cancel_mono (Y.ofRestrict W.isOpenEmbedding)]
    simp only [Category.assoc, Hom.restrictPreimage_ofRestrict]
    rw [IsOpenImmersion.isoOfRangeEq_inv_comp, w, IsOpenImmersion.isoOfRangeEq_hom_comp_assoc]
    rfl
  rw [heq, MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType.{u}]
  have hq' : LocallyOfFiniteType (q.restrictPreimage R ≫ eO.inv) :=
    (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFiniteType.{u} _ _).mpr hq
  simpa only [Category.assoc] using hq'.comp_of_isOpenImmersion
    ((Y.restrict W.isOpenEmbedding).ofRestrict
      ((Opens.map (Y.ofRestrict W.isOpenEmbedding).base).obj V).isOpenEmbedding)

/-- A morphism locally of finite type into a sheafy pre-adic space remains locally of finite
type after restriction over any open of the target. -/
theorem LocallyOfFiniteType.restrictPreimage {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (hY : isSheafy Y) (W : Opens Y) : LocallyOfFiniteType (f.restrictPreimage W) := by
  classical
  -- Restrict each finite-type chart over `W`, retaining its image as an open of the source.
  have hlocal : ∀ x : X.restrict ((Opens.map f.base).obj W).isOpenEmbedding, ∃ K : Opens _,
      x ∈ K ∧ LocallyOfFiniteType
        (((X.restrict ((Opens.map f.base).obj W).isOpenEmbedding).ofRestrict
          K.isOpenEmbedding) ≫ f.restrictPreimage W) := by
    intro x
    obtain ⟨U, hx, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
      hsheaf, eU, eV, hfac⟩ := (chartLocally_iff f).mp ((locallyOfFiniteType_iff f).mp hf) x.1
    have hsA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
        (presentationLimitPresheaf P S.plus) :=
      ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ hY)
    exact ⟨_, hx, locallyOfFiniteType_restrict_chart eU eV hfac
      (locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap
        P P' hP hP' φ hφ hsheaf hsA _)⟩
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
