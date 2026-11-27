/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Constructions for open partial homeomorphisms

An open partial homeomorphism restricts to a chart on a subtype when membership in the subtype is
detected by a parametrized coordinate slice. This file packages that topological construction;
zero-slice subgroup charts use it after translating an ambient chart. Continuous maps that are
inverse on open sets also give an open partial homeomorphism on their mutual restrictions
(`ContinuousOn.toOpenPartialHomeomorph`). Composing with an open partial homeomorphism preserves
open embeddings whose ranges lie in its source (`OpenPartialHomeomorph.isOpenEmbedding_comp`).
An open embedding of a nonempty open subset extends to an open partial homeomorphism with that
source (`OpenPartialHomeomorph.exists_source_eq_of_isOpenEmbedding`); a homeomorphism of nonempty
open subsets extends to one with that source and target
(`OpenPartialHomeomorph.exists_source_eq_target_eq_of_homeomorph`).
Finite products of open partial homeomorphisms commute with inverses and composition
(`OpenPartialHomeomorph.pi_symm`, `OpenPartialHomeomorph.pi_trans`), as for partial equivalences.

## Main definitions

* `ContinuousOn.toOpenPartialHomeomorph` constructs an open partial homeomorphism from continuous
  maps inverse on their mutual restrictions.

* `OpenPartialHomeomorph.subtypeCoord` restricts an open partial homeomorphism to a subtype and
  reads its coordinates through a retraction onto the parametrized slice.

* `OpenPartialHomeomorph.subtypeFst` restricts an open partial homeomorphism with values in a
  product `Y × W` to the subtype it reads as `t × W`, for a subset `t` of the first factor.

## References

This construction abstracts the concrete subtype charts in the following Tau Ceti formalizations:

* `boundaryChart` in `TauCeti/Geometry/Manifold/Boundary/OfHomeomorph.lean`.
* `TauCeti.levelSetChart` in `TauCeti/Analysis/Fredholm/LevelSet/Basic.lean`.
-/

public section

open Set Topology

namespace OpenPartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Composing an open embedding with an open partial homeomorphism gives an open embedding
when its range lies in the source of the open partial homeomorphism. -/
theorem isOpenEmbedding_comp (e : OpenPartialHomeomorph X Y) {g : Z → X}
    (hg : IsOpenEmbedding g) (hgs : range g ⊆ e.source) : IsOpenEmbedding (e ∘ g) := by
  have hgs' : ∀ z, g z ∈ e.source := fun z => hgs (mem_range_self z)
  have hgc : IsOpenEmbedding (e.source.codRestrict g hgs') :=
    .of_isEmbedding_isOpenMap (hg.isEmbedding.codRestrict _ _) (hg.isOpenMap.codRestrict _)
  simpa only [Set.domRestrict_comp_codRestrict] using e.isOpenEmbedding_restrict.comp hgc

/-- An open embedding of a nonempty open subset `U` of `X` into `Y` is the restriction of an open
partial homeomorphism of `X` into `Y` with source `U`, obtained from
`OpenPartialHomeomorph.lift_openEmbedding`. -/
theorem exists_source_eq_of_isOpenEmbedding {U : Set X} (hU : IsOpen U) {g : U → Y}
    (hg : IsOpenEmbedding g) (x : U) :
    ∃ c : OpenPartialHomeomorph X Y, c.source = U ∧ ∀ y : U, c y = g y := by
  have : Nonempty U := ⟨x⟩
  have : Nonempty Y := ⟨g x⟩
  have hi := hU.isOpenEmbedding_subtypeVal
  exact ⟨(hg.toOpenPartialHomeomorph g).lift_openEmbedding hi, by simp, fun y ↦ by simp⟩

/-- A homeomorphism between nonempty open subsets `U` of `X` and `V` of `Y` is the restriction of an
open partial homeomorphism with source `U` and target `V`. -/
theorem exists_source_eq_target_eq_of_homeomorph {U : Set X} {V : Set Y} (hU : IsOpen U)
    (hV : IsOpen V) (e : U ≃ₜ V) (x : U) :
    ∃ c : OpenPartialHomeomorph X Y, c.source = U ∧ c.target = V ∧ ∀ y : U, c y = e y := by
  obtain ⟨c, hs, hc⟩ := exists_source_eq_of_isOpenEmbedding hU
    (hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding) x
  refine ⟨c, hs, ?_, hc⟩
  rw [← c.image_source_eq_target, hs, image_eq_range, funext hc, range_comp,
    e.surjective.range_eq, image_univ, Subtype.range_coe]

open scoped Classical in
/-- Restrict an open partial homeomorphism to a subtype represented by a parametrized coordinate
slice.

The map `ι : Z → Y` parametrizes the slice and `π : Y → Z` reads its coordinates. The hypotheses
say that ambient inverse images of slice points belong to `s`, that points of `s` visible in the
source lie on the slice, and that `π` is a left inverse of `ι` wherever the slice meets the target.
Only continuity of `π` where the parametrized slice meets the target is needed. Outside the target,
the inverse uses the canonical choice supplied by `Nonempty s`; its value there is irrelevant to an
open partial homeomorphism. -/
noncomputable def subtypeCoord (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : Nonempty s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) : OpenPartialHomeomorph s Z where
  toFun x := π (e x.val)
  invFun z := if h : ι z ∈ e.target then ⟨e.symm (ι z), hι h⟩ else Classical.choice hs
  source := Subtype.val ⁻¹' e.source
  target := ι ⁻¹' e.target
  map_source' x hx := by
    rw [mem_preimage, hslice hx x.property]
    exact e.map_source hx
  map_target' z hz := by
    simp only [mem_preimage] at hz ⊢
    rw [dite_eq_left hz]
    exact e.map_target hz
  left_inv' x hx := Subtype.ext <| by
    simp [hslice hx x.property, e.map_source hx, e.left_inv hx]
  right_inv' z hz := by
    simp only [mem_preimage] at hz
    rw [dite_eq_left hz, e.right_inv hz]
    exact hπι hz
  open_source := e.open_source.preimage continuous_subtypeVal
  open_target := e.open_target.preimage hιc
  continuousOn_toFun :=
    hπc.comp
      (e.continuousOn.comp continuous_subtypeVal.continuousOn (mapsTo_preimage _ _))
      (fun x hx => ⟨e.map_source hx, ⟨π (e x.val), hslice hx x.property⟩⟩)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr
      (e.symm.continuousOn.comp hιc.continuousOn (mapsTo_preimage _ _)) fun z hz => ?_
    simp [mem_preimage.mp hz]

section SubtypeCoord

variable (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : Nonempty s) (ι : Z → Y) (π : Y → Z)
  (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
  (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
  (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
  (hπc : ContinuousOn π (e.target ∩ Set.range ι))

/-- The source of `subtypeCoord` is the part of the subtype in the ambient source. -/
@[simp]
theorem subtypeCoord_source :
    (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).source = Subtype.val ⁻¹' e.source := (rfl)

/-- The target of `subtypeCoord` is the preimage of the ambient target under the slice
parametrization. -/
@[simp]
theorem subtypeCoord_target :
    (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).target = ι ⁻¹' e.target := (rfl)

/-- `subtypeCoord` reads a subtype point using the ambient map followed by the coordinate
retraction. -/
@[simp]
theorem subtypeCoord_apply (x : s) :
    e.subtypeCoord s hs ι π hι hslice hπι hιc hπc x = π (e x.val) := (rfl)

/-- On its source, `subtypeCoord` recovers the ambient coordinate after applying the slice
parametrization. -/
theorem subtypeCoord_parametrization_apply {x : s}
    (hx : x ∈ (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).source) :
    ι (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc x) = e x.val := by
  rw [subtypeCoord_apply]
  exact hslice (by simpa only [subtypeCoord_source, Set.mem_preimage] using hx) x.property

/-- On its target, the inverse of `subtypeCoord` is the ambient inverse evaluated on the
parametrized slice. -/
@[simp]
theorem coe_subtypeCoord_symm_apply {z : Z} (hz : ι z ∈ e.target) :
    ((e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).symm z : X) = e.symm (ι z) := by
  simp [subtypeCoord, hz]

end SubtypeCoord

section SubtypeFst

variable {W : Type*} [TopologicalSpace W] (e : OpenPartialHomeomorph X (Y × W)) {s : Set X}
  {t : Set Y} (h : ∀ x ∈ e.source, x ∈ s ↔ (e x).1 ∈ t)

include h in
/-- On the target of `e`, the inverse of `e` sends the part of `t × W` into `s`. -/
private theorem symm_prodMap_mem_of_mem_target {z : t × W}
    (hz : Prod.map Subtype.val id z ∈ e.target) : e.symm (Prod.map Subtype.val id z) ∈ s :=
  (h _ (e.map_target hz)).2 (by rw [e.right_inv hz]; exact z.1.property)

variable [Nonempty t]

include h in
open Classical in
/-- On the source of `e`, a point of `s` is read in `t × W` without moving it. -/
private theorem prodMap_dite_eq {x : X} (hx : x ∈ e.source) (hxs : x ∈ s) :
    Prod.map Subtype.val id
      (if hp : (e x).1 ∈ t then (⟨(e x).1, hp⟩ : t) else Classical.arbitrary t, (e x).2) = e x := by
  simp [(h x hx).1 hxs]

variable [Nonempty s]

open Classical in
/-- An open partial homeomorphism `e` of `X` with values in `Y × W` restricts to one of a nonempty
subset `s` of `X` with values in `t × W`, for a nonempty subset `t` of `Y`, when, on the source of
`e`, a point lies in `s` exactly when its first coordinate lies in `t`. -/
noncomputable def subtypeFst : OpenPartialHomeomorph s (t × W) :=
  e.subtypeCoord s inferInstance (Prod.map Subtype.val id)
    (fun p ↦ (if hp : p.1 ∈ t then ⟨p.1, hp⟩ else Classical.arbitrary t, p.2))
    (e.symm_prodMap_mem_of_mem_target h) (e.prodMap_dite_eq h)
    -- The ascription keeps this hypothesis in `LeftInvOn` form, so the `subtypeCoord` lemmas apply.
    (show LeftInvOn _ _ _ from fun z _ ↦ by simp [z.1.property])
    (continuous_subtypeVal.prodMap continuous_id)
    (by
      refine ContinuousOn.prodMk ?_ continuous_snd.continuousOn
      rw [IsInducing.subtypeVal.continuousOn_iff]
      refine continuous_fst.continuousOn.congr fun p hp ↦ ?_
      obtain ⟨z, rfl⟩ := hp.2
      simp)

/-- The source of `subtypeFst` is the part of `s` in the source of `e`. -/
@[simp]
theorem subtypeFst_source : (e.subtypeFst h).source = Subtype.val ⁻¹' e.source :=
  (rfl)

/-- The target of `subtypeFst` is the part of `t × W` in the target of `e`. -/
@[simp]
theorem subtypeFst_target :
    (e.subtypeFst h).target = Prod.map Subtype.val id ⁻¹' e.target :=
  (rfl)

/-- On the source of `e`, `subtypeFst` reads a point of `s` through `e`. -/
theorem subtypeFst_apply {y : s} (hy : (y : X) ∈ e.source) :
    e.subtypeFst h y = (⟨(e y).1, (h _ hy).1 y.property⟩, (e y).2) := by
  rw [subtypeFst, subtypeCoord_apply]
  simp [(h _ hy).1 y.property]

/-- The second coordinate of `subtypeFst` is that of `e`. -/
@[simp]
theorem snd_subtypeFst_apply (y : s) : (e.subtypeFst h y).2 = (e y).2 :=
  (rfl)

/-- On its target, the inverse of `subtypeFst` is the inverse of `e`. -/
@[simp]
theorem coe_subtypeFst_symm_apply {z : t × W} (hz : Prod.map Subtype.val id z ∈ e.target) :
    ((e.subtypeFst h).symm z : X) = e.symm (Prod.map Subtype.val id z) := by
  rw [subtypeFst]
  exact coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hz

variable (c : OpenPartialHomeomorph t Z)

/-- The source of `subtypeFst` composed with a chart `c` of the first factor is the part of `s` in
the source of `e` whose first coordinate `c` reads. -/
theorem mem_subtypeFst_trans_prod_refl_source {y : s} :
    y ∈ ((e.subtypeFst h).trans (c.prod (OpenPartialHomeomorph.refl W))).source ↔
      ∃ hy : (y : X) ∈ e.source, (⟨(e y).1, (h _ hy).1 y.property⟩ : t) ∈ c.source := by
  simp only [trans_source, subtypeFst_source, mem_inter_iff, mem_preimage, prod_source,
    refl_source, mem_prod, mem_univ, and_true]
  refine ⟨fun ⟨hy, hc⟩ ↦ ⟨hy, ?_⟩, fun ⟨hy, hc⟩ ↦ ⟨hy, ?_⟩⟩
  · rwa [subtypeFst_apply _ _ hy] at hc
  · rwa [subtypeFst_apply _ _ hy]

/-- `subtypeFst` composed with a chart `c` of the first factor reads a point through `e` and then
`c` in the first factor. -/
theorem subtypeFst_trans_prod_refl_apply {y : s} (hy : (y : X) ∈ e.source) :
    (e.subtypeFst h).trans (c.prod (OpenPartialHomeomorph.refl W)) y =
      (c ⟨(e y).1, (h _ hy).1 y.property⟩, (e y).2) := by
  rw [trans_apply, subtypeFst_apply _ _ hy]
  simp only [prod_apply, refl_apply, id_eq]

end SubtypeFst

section Pi

variable {ι : Type*} [Finite ι] {X Y Z : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)] [∀ i, TopologicalSpace (Z i)]

/-- The inverse of a finite product of open partial homeomorphisms is the product of the
inverses. -/
@[simp, mfld_simps]
theorem pi_symm (e : ∀ i, OpenPartialHomeomorph (X i) (Y i)) :
    (OpenPartialHomeomorph.pi e).symm = .pi fun i ↦ (e i).symm :=
  toPartialEquiv_injective (PartialEquiv.pi_symm _)

/-- The composition of two finite products of open partial homeomorphisms is the product of the
compositions. -/
@[simp, mfld_simps]
theorem pi_trans (e : ∀ i, OpenPartialHomeomorph (X i) (Y i))
    (e' : ∀ i, OpenPartialHomeomorph (Y i) (Z i)) :
    (OpenPartialHomeomorph.pi e).trans (.pi e') = .pi fun i ↦ (e i).trans (e' i) :=
  toPartialEquiv_injective (PartialEquiv.pi_trans _ _)

end Pi

end OpenPartialHomeomorph

namespace ContinuousOn

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (hf : ContinuousOn f U) (hg : ContinuousOn g V) (hU : IsOpen U) (hV : IsOpen V)
    (hgf : LeftInvOn g f (U ∩ f ⁻¹' V)) (hfg : RightInvOn g f (V ∩ g ⁻¹' U))

/-- Continuous maps on open sets define an open partial homeomorphism if they are inverse on
points whose images lie in the other set. The forward and inverse maps are the given maps,
and the source and target are exactly these mutual restrictions. -/
def toOpenPartialHomeomorph : OpenPartialHomeomorph X Y where
  toFun := f
  invFun := g
  source := U ∩ f ⁻¹' V
  target := V ∩ g ⁻¹' U
  map_source' x hx := ⟨hx.2, by simpa only [mem_preimage, hgf hx] using hx.1⟩
  map_target' y hy := ⟨hy.2, by simpa only [mem_preimage, hfg hy] using hy.1⟩
  left_inv' _ hx := hgf hx
  right_inv' _ hy := hfg hy
  open_source := hf.isOpen_inter_preimage hU hV
  open_target := hg.isOpen_inter_preimage hV hU
  continuousOn_toFun := hf.mono inter_subset_left
  continuousOn_invFun := hg.mono inter_subset_left

/-- The forward map of `toOpenPartialHomeomorph` is the given map. -/
@[simp]
theorem coe_toOpenPartialHomeomorph :
    ⇑(hf.toOpenPartialHomeomorph hg hU hV hgf hfg) = f := (rfl)

/-- The inverse map of `toOpenPartialHomeomorph` is the given inverse. -/
@[simp]
theorem coe_toOpenPartialHomeomorph_symm :
    ⇑(hf.toOpenPartialHomeomorph hg hU hV hgf hfg).symm = g := (rfl)

/-- The source of `toOpenPartialHomeomorph` consists of points of `U` mapped into `V`. -/
@[simp]
theorem toOpenPartialHomeomorph_source :
    (hf.toOpenPartialHomeomorph hg hU hV hgf hfg).source = U ∩ f ⁻¹' V := (rfl)

/-- The target of `toOpenPartialHomeomorph` consists of points of `V` mapped into `U`. -/
@[simp]
theorem toOpenPartialHomeomorph_target :
    (hf.toOpenPartialHomeomorph hg hU hV hgf hfg).target = V ∩ g ⁻¹' U := (rfl)

end ContinuousOn
