/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Opens of locally directed colimits of schemes

Let `F : J ⥤ Scheme` be a locally directed diagram of open immersions indexed by a small thin
category, so that its colimit is the scheme glued from the `F j` along the images of the
transition maps (`AlgebraicGeometry.Scheme.IsLocallyDirected.openCover`). This file describes how
the images of the `F j` in the colimit meet.

## Main results

* `AlgebraicGeometry.Scheme.IsLocallyDirected.preimage_opensRange_ι_le`: the part of `F j` lying
  over the image of `F i` is contained in the image of `F f`, for any `f : i ⟶ j`.
* `AlgebraicGeometry.Scheme.IsLocallyDirected.preimage_le_iSup_preimage_inf_opensRange`: the
  preimage in `F j` of an open contained in the image of `F i` is covered by its intersections with
  the images of the `F k` mapping to both `F i` and `F j`.
* `AlgebraicGeometry.Scheme.IsLocallyDirected.isLocallyDirected_of_range_inter_subset`: a diagram
  of open immersions indexed by a meet-semilattice is locally directed when the images of `F i`
  and `F j` meet inside the image of `F (i ⊓ j)`.
* `AlgebraicGeometry.Scheme.IsLocallyDirected.ι_eq_ι_iff_inf`: over a meet-semilattice, points of
  `F i` and `F j` are identified in the colimit exactly along `F (i ⊓ j)`.
* `AlgebraicGeometry.Scheme.IsLocallyDirected.exists_pullback_lift_eq`: every point of the
  pullback of the inclusions of `F i` and `F j` comes from some `F k` mapping to both.
* The open cover `AlgebraicGeometry.Scheme.IsLocallyDirected.openCover` of the colimit of a thin
  locally directed diagram is locally directed, with the diagram maps as transition maps.
* `AlgebraicGeometry.Scheme.range_pushout_inl_union_range_pushout_inr`: a pushout of two open
  immersions is covered by the images of its two pieces.
* `AlgebraicGeometry.Scheme.pushoutOpenCover`: the open cover by those two pieces.
* `AlgebraicGeometry.Scheme.isPullback_pushout_of_isOpenImmersion`: those two pieces intersect
  in precisely the common open along which they were glued.

## References

* The Stacks Project, Section 26.14, *Gluing schemes* (Tag 01JA).
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u v w

namespace IsLocallyDirected

variable {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J]

/-- In the colimit of a thin locally directed diagram of open immersions, the part of `F j` lying
over the image of `F i` is contained in the image of `F f`, for any `f : i ⟶ j`. -/
theorem preimage_opensRange_ι_le {i j : J}
    (f : i ⟶ j) : colimit.ι F j ⁻¹ᵁ (colimit.ι F i).opensRange ≤ (F.map f).opensRange := by
  rintro y ⟨x, hx⟩
  obtain ⟨k, fi, fj, z, rfl, rfl⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hx
  exact ⟨F.map fi z, by rw [← Scheme.Hom.comp_apply, ← F.map_comp, Subsingleton.elim (fi ≫ f) fj]⟩

/-- In the colimit of a thin locally directed diagram of open immersions, the opens
`U ⊓ ιₖ(F k)`, for `k` mapping to both `i` and `j`, cover the preimage in `F j` of an open `U`
contained in the image of `F i`. -/
theorem preimage_le_iSup_preimage_inf_opensRange
    {i j : J} {U : (colimit F).Opens} (hU : U ≤ (colimit.ι F i).opensRange) :
    colimit.ι F j ⁻¹ᵁ U ≤
      ⨆ k : Σ k : J, (k ⟶ j) × (k ⟶ i), colimit.ι F j ⁻¹ᵁ (U ⊓ (colimit.ι F k.1).opensRange) := by
  intro y hy
  obtain ⟨x, hx⟩ := hU hy
  obtain ⟨k, fi, fj, z, rfl, rfl⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, fj, fi⟩, hy, z, ?_⟩
  rw [← Scheme.Hom.comp_apply, colimit.w]

end IsLocallyDirected

namespace IsLocallyDirected

section SemilatticeInf

variable {J : Type*} [SemilatticeInf J] (F : J ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]

/-- A diagram of open immersions indexed by a meet-semilattice is locally directed as soon as,
for all maps `F i ⟶ F k` and `F j ⟶ F k`, the images of `F i` and `F j` in `F k` meet inside the
image of `F (i ⊓ j)`. -/
theorem isLocallyDirected_of_range_inter_subset
    (h : ∀ {i j k : J} (fi : i ⟶ k) (fj : j ⟶ k),
      Set.range (F.map fi) ∩ Set.range (F.map fj) ⊆
        Set.range (F.map (homOfLE (inf_le_left (b := j)) ≫ fi))) :
    (F ⋙ Scheme.forget).IsLocallyDirected := by
  refine ⟨fun {i j k} fi fj xi xj hij ↦ ?_⟩
  -- On points, the functor `F ⋙ Scheme.forget` applies the maps of `F`.
  replace hij : F.map fi xi = F.map fj xj := hij
  obtain ⟨x, hx⟩ := h fi fj ⟨⟨xi, rfl⟩, ⟨xj, hij.symm⟩⟩
  refine ⟨i ⊓ j, homOfLE inf_le_left, homOfLE inf_le_right, x, ?_, ?_⟩
  · rw [Functor.comp_map, Scheme.forget_map, TypeCat.ofHom_apply]
    apply (F.map fi).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← F.map_comp, hx]
  · rw [Functor.comp_map, Scheme.forget_map, TypeCat.ofHom_apply]
    apply (F.map fj).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← F.map_comp, ← hij, ← hx,
      Subsingleton.elim (homOfLE inf_le_right ≫ fj) (homOfLE inf_le_left ≫ fi)]

variable [(F ⋙ Scheme.forget).IsLocallyDirected] [Small.{u} J]

/-- In the colimit of a locally directed diagram of open immersions indexed by a meet-semilattice,
points of `F i` and `F j` are identified exactly when they come from a common point of
`F (i ⊓ j)`. -/
theorem ι_eq_ι_iff_inf {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ x : F.obj (i ⊓ j),
        F.map (homOfLE inf_le_left) x = xi ∧ F.map (homOfLE inf_le_right) x = xj := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hxi, hxj⟩ ↦ (ι_eq_ι_iff F).2 ⟨_, _, _, x, hxi, hxj⟩⟩
  obtain ⟨k, fi, fj, x, rfl, rfl⟩ := (ι_eq_ι_iff F).1 h
  refine ⟨F.map (homOfLE (le_inf (leOfHom fi) (leOfHom fj))) x, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← F.map_comp, Subsingleton.elim (_ ≫ _) fi]
  · rw [← Scheme.Hom.comp_apply, ← F.map_comp, Subsingleton.elim (_ ≫ _) fj]

end SemilatticeInf

section OpenCover

variable {J : Type w} [Category.{v} J] (F : J ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

/-- Every point of the pullback of the inclusions of `F i` and `F j` into the colimit of a thin
locally directed diagram of open immersions comes from a point of some `F k` mapping to both. -/
theorem exists_pullback_lift_eq {i j : J}
    (x : (pullback (colimit.ι F i) (colimit.ι F j)).carrier) :
    ∃ (k : J) (fi : k ⟶ i) (fj : k ⟶ j) (z : F.obj k),
      pullback.lift (F.map fi) (F.map fj) ((colimit.w F fi).trans (colimit.w F fj).symm) z =
        x := by
  obtain ⟨k, fi, fj, z, hzi, -⟩ := (ι_eq_ι_iff F).1
    congr($(pullback.condition (f := colimit.ι F i) (g := colimit.ι F j)) x)
  refine ⟨k, fi, fj, z, ?_⟩
  -- The first projection of a pullback along an open immersion is injective.
  apply (pullback.fst (colimit.ι F i) (colimit.ι F j)).isOpenEmbedding.injective
  exact congr($(pullback.lift_fst (F.map fi) (F.map fj)
    ((colimit.w F fi).trans (colimit.w F fj).symm)) z).trans hzi

/-- The open cover of a locally directed colimit by its members is indexed by the index category
of the diagram. -/
instance instCategoryI₀OpenCover : Category.{v} (openCover F).I₀ :=
  inferInstanceAs (Category.{v} J)

/-- The open cover of the colimit of a thin locally directed diagram of open immersions by its
members is locally directed, with the maps of the diagram as transition maps. -/
noncomputable instance instLocallyDirectedOpenCover : (openCover F).LocallyDirected where
  trans f := F.map f
  trans_id i := F.map_id i
  trans_comp f g := F.map_comp f g
  w f := colimit.w F f
  directed x := exists_pullback_lift_eq F x
  property_trans {i j : J} (f : i ⟶ j) := inferInstanceAs (IsOpenImmersion (F.map f))

/-- The transition maps of the open cover of a locally directed colimit are the maps of the
diagram. -/
@[simp]
theorem openCover_trans {i j : J} (f : i ⟶ j) : (openCover F).trans f = F.map f := (rfl)

end OpenCover

end IsLocallyDirected

/-- **A pushout of open immersions is covered by its two pieces.** Every point of the pushout of
two open immersions `X ⟵ W ⟶ Z` of schemes lies in the image of `X` or of `Z`. -/
theorem range_pushout_inl_union_range_pushout_inr {W X Z : Scheme.{u}} (g : W ⟶ X)
    (h : W ⟶ Z) [IsOpenImmersion g] [IsOpenImmersion h] :
    Set.range (pushout.inl g h) ∪ Set.range (pushout.inr g h) = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  -- Every point of a locally directed colimit comes from one of the three pieces of the span,
  -- and the apex maps through the left piece.
  obtain ⟨i, q, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span g h) p
  rcases i with _ | _ | _
  · refine Or.inl ⟨g q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← colimit.w (span g h) (WidePushoutShape.Hom.init .left)]
    -- `pushout.inl` is the colimit inclusion of the left piece of the span.
    rfl
  · exact Or.inl ⟨q, rfl⟩
  · exact Or.inr ⟨q, rfl⟩

/-- The open cover of a pushout of open immersions by its two pieces, indexed by `Bool`,
with the left piece at `false` and the right piece at `true`. -/
@[expose]
noncomputable def pushoutOpenCover {W X Y : Scheme.{u}} (i : W ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] : (pushout i j).OpenCover :=
  Cover.mkOfCovers Bool
    (fun b ↦ if b then Y else X)
    (fun b ↦ match b with | false => pushout.inl i j | true => pushout.inr i j)
    (fun z ↦ by
      rcases (Set.ext_iff.mp (range_pushout_inl_union_range_pushout_inr i j) z).mpr
        trivial with ⟨x, rfl⟩ | ⟨y, rfl⟩
      exacts [⟨false, x, rfl⟩, ⟨true, y, rfl⟩])
    (fun b ↦ by cases b <;> infer_instance)

/-- The two-piece pushout cover has a finite index type. -/
instance {W X Y : Scheme.{u}} (i : W ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] : Finite (pushoutOpenCover i j).I₀ :=
  inferInstanceAs (Finite Bool)

/-- The first chart of the pushout cover is its left inclusion. -/
@[simp]
theorem pushoutOpenCover_f_false {W X Y : Scheme.{u}} (i : W ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    (pushoutOpenCover i j).f false = pushout.inl i j := rfl

/-- The second chart of the pushout cover is its right inclusion. -/
@[simp]
theorem pushoutOpenCover_f_true {W X Y : Scheme.{u}} (i : W ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    (pushoutOpenCover i j).f true = pushout.inr i j := rfl

/-- The square defining the pushout of two open immersions is also cartesian: the two
pieces intersect in precisely the open subscheme along which they were glued. -/
theorem isPullback_pushout_of_isOpenImmersion {W X Y : Scheme.{u}} (i : W ⟶ X)
    (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j] :
    IsPullback i j (pushout.inl i j) (pushout.inr i j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (pushout.condition (f := i) (g := j)).symm
    (le_antisymm ?_ ?_)
  · rintro y ⟨x, hx⟩
    -- The two legs of the span can only meet through its apex.
    have hx' : colimit.ι (span i j) WalkingSpan.left x =
        colimit.ι (span i j) WalkingSpan.right y := hx
    obtain ⟨k, fx, fy, z, rfl, rfl⟩ := (IsLocallyDirected.ι_eq_ι_iff _).mp hx'
    rcases k with _ | _ | _
    · cases fy
      exact ⟨z, rfl⟩
    · cases fy
    · cases fx
  · rintro _ ⟨w, rfl⟩
    exact ⟨i w, by rw [← Hom.comp_apply, pushout.condition, Hom.comp_apply]⟩

end AlgebraicGeometry.Scheme
