/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective
public import TauCeti.Topology.CategoryTheory.Etale
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses

/-!
# The principal locus of an étale groupoid

At an object `x` of an étale topological groupoid `C`, the isotropy group of the effective quotient
`EffectiveQuotient C` is `Aut x ⧸ ineffectiveKernel hs x`. That effective isotropy is trivial
precisely when `ineffectiveKernel hs x = ⊤`, meaning that every automorphism of `x` induces the
identity germ on objects near `x`. Such objects form the *principal locus* of the presentation: all
of their isotropy is ineffective.

In a local action chart `F : G ⋉ X ⥤ C` lying fully and faithfully over an injective map `ι : X → C`
with open-embedding arrow sections, the chart isomorphism `MulAction.stabilizer G y ≃* Aut (ι y)`
identifies `(germKernel G y).subgroupOf (stabilizer G y)` with `ineffectiveKernel hs (ι y)`.
In particular, at the centre of a local isotropy chart `Aut x ⋉ U ⥤ C`, `ineffectiveKernel hs x` is
literally `germKernel (Aut x) ⟨x, hxU⟩`, and nearby points satisfy `ineffectiveKernel hs y = ⊤`
precisely when `stabilizer (Aut x) y = germKernel (Aut x) y`.

Combining `exists_isotropy_action_of_proper_source_target` with openness and density of the
principal locus of a finite group action (`isOpen_setOf_stabilizer_eq_germKernel` and
`dense_setOf_stabilizer_eq_germKernel`), we obtain that in any Hausdorff proper étale
topological groupoid:
* `{x : C | ineffectiveKernel hs x = ⊤}` is open and dense in `C`;
* `{q : EffectiveQuotient C | Subsingleton (Aut q)}` is open and dense in `EffectiveQuotient C`;
* the image of the principal locus is open and dense in the coarse quotient
  `Quotient (isIsomorphicSetoid C)`.

No smooth or manifold structure is needed for any of these results.

## Main declarations

* `TauCeti.subsingleton_aut_toEffectiveQuotient_obj_iff`: `(toEffectiveQuotient C).obj x` has
  trivial isotropy if and only if `ineffectiveKernel hs x = ⊤`.
* `TauCeti.stabilizerMulEquivAutOfActionChart`: the isotropy isomorphism
  `MulAction.stabilizer G y ≃* Aut (ι y)` induced by a fully faithful local action chart.
* `TauCeti.comap_stabilizerMulEquivAutOfActionChart_ineffectiveKernel`,
  `TauCeti.map_stabilizerMulEquivAutOfActionChart_germKernel`: subgroup identification between the
  action's germ kernel and the groupoid's ineffective kernel in a local action chart.
* `TauCeti.ineffectiveKernel_eq_germKernel_of_isotropy_chart`: at the centre `z` of an isotropy
  chart, `ineffectiveKernel hs x = TauCeti.MulAction.germKernel (Aut x) z`.
* `TauCeti.isOpen_setOf_ineffectiveKernel_eq_top`,
  `TauCeti.dense_setOf_ineffectiveKernel_eq_top`: the principal locus is open and dense in any
  Hausdorff proper étale topological groupoid.
* `TauCeti.EffectiveQuotient.isOpen_setOf_subsingleton_aut`,
  `TauCeti.EffectiveQuotient.dense_setOf_subsingleton_aut`: objects with trivial isotropy form a
  dense open subset of `EffectiveQuotient C`.
* `TauCeti.isOpen_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top`,
  `TauCeti.dense_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top`: the principal locus is
  open and dense in the coarse space.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory MulAction Set Topology TauCeti.MulAction

namespace TauCeti

section General

variable {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- An object has trivial isotropy in `EffectiveQuotient C` if and only if all of its isotropy in
`C` lies in the ineffective kernel. -/
theorem subsingleton_aut_toEffectiveQuotient_obj_iff (x : C) :
    Subsingleton (Aut ((toEffectiveQuotient C).obj x)) ↔ ineffectiveKernel hs x = ⊤ := by
  rw [← (quotientIneffectiveKernelMulEquivAut hs x).toEquiv.subsingleton_congr,
    QuotientGroup.subsingleton_iff]

/-- Being in the principal locus (`ineffectiveKernel hs x = ⊤`) is invariant under isomorphism. -/
theorem ineffectiveKernel_eq_top_iff_of_iso {x y : C} (e : x ≅ y) :
    ineffectiveKernel hs x = ⊤ ↔ ineffectiveKernel hs y = ⊤ := by
  rw [Subgroup.eq_top_iff', Subgroup.eq_top_iff']
  refine ⟨fun h g ↦ ?_, fun h g ↦ (autMulEquivOfIso_mem_ineffectiveKernel_iff hs e).mp (h _)⟩
  exact (autMulEquivOfIso_mem_ineffectiveKernel_iff hs e.symm).mp (h _)

/-- The principal locus `{x : C | ineffectiveKernel hs x = ⊤}` is saturated under isomorphism. -/
theorem preimage_isomorphismClassesMk_image_setOf_ineffectiveKernel_eq_top :
    _root_.Quotient.mk (isIsomorphicSetoid C) ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) =
      {x : C | ineffectiveKernel hs x = ⊤} := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨y, hy, rfl⟩⟩
  rintro ⟨x, hx, hxy⟩
  obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.mp hxy
  exact (ineffectiveKernel_eq_top_iff_of_iso hs (asIso f)).mp hx

end General

section ActionChart

variable {G X : Type*} [Group G] [MulAction G X]
  {C : Type*} [Groupoid C] {ι : X → C}

/-- In a fully faithful functor `F : G ⋉ X ⥤ C` lying over `ι : X → C` on objects, the stabilizer of
`y` is canonically isomorphic to the isotropy group `Aut (ι y)`. -/
noncomputable def stabilizerMulEquivAutOfActionChart (F : ActionCategory G X ⥤ C)
    [F.Full] [F.Faithful] (hobj : ∀ a, F.obj a = ι a.back) (y : X) :
    stabilizer G y ≃* Aut (ι y) :=
  (ActionCategory.stabilizerMulEquivAut G y).trans
    (((Functor.FullyFaithful.ofFullyFaithful F).autMulEquivOfFullyFaithful
      (ActionCategory.objEquiv G X y)).trans
      (Aut.autMulEquivOfIso (eqToIso
        (show F.obj (ActionCategory.objEquiv G X y) = ι y from
          hobj (ActionCategory.objEquiv G X y)))))

/-- The underlying arrow of `stabilizerMulEquivAutOfActionChart` conjugates the `F`-image of the
stabilizer automorphism by `eqToHom`. -/
@[simp]
theorem stabilizerMulEquivAutOfActionChart_apply_asIso_hom (F : ActionCategory G X ⥤ C)
    [F.Full] [F.Faithful] (hobj : ∀ a, F.obj a = ι a.back) (y : X) (g : stabilizer G y) :
    (stabilizerMulEquivAutOfActionChart F hobj y g).asIso.hom =
      eqToHom (show F.obj (ActionCategory.objEquiv G X y) = ι y from
        hobj (ActionCategory.objEquiv G X y)).symm ≫
        F.map (ActionCategory.stabilizerMulEquivAut G y g).asIso.hom ≫
        eqToHom (show F.obj (ActionCategory.objEquiv G X y) = ι y from
          hobj (ActionCategory.objEquiv G X y)) :=
  (rfl)

variable [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- An element of `stabilizer G y` maps into `ineffectiveKernel hs (ι y)` under a local action chart
if and only if it belongs to `germKernel G y`. -/
theorem stabilizerMulEquivAutOfActionChart_mem_ineffectiveKernel_iff
    {F : ActionCategory G X ⥤ C} [F.Full] [F.Faithful]
    (hι : Function.Injective ι) (hobj : ∀ a, F.obj a = ι a.back)
    (hσ : ∀ g : G, IsOpenEmbedding fun z : X ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv G X).symm (g, z)).hom⟩ : Quiver.Total C))
    {y : X} {g : stabilizer G y} :
    stabilizerMulEquivAutOfActionChart F hobj y g ∈ ineffectiveKernel hs (ι y) ↔
      (g : G) ∈ germKernel G y := by
  have key : ∀ {p q : C} (e : p = q) (k : p ⟶ p),
      (⟨q, q, eqToHom e.symm ≫ k ≫ eqToHom e⟩ : Quiver.Total C) = ⟨p, p, k⟩ := by
    rintro p _ rfl k
    simp
  rw [mem_ineffectiveKernel, stabilizerMulEquivAutOfActionChart_apply_asIso_hom,
    key (show F.obj (ActionCategory.objEquiv G X y) = ι y from
      hobj (ActionCategory.objEquiv G X y)),
    mem_ineffectiveArrows_map_iff_mem_germKernel hι hobj _ (hσ _),
    ActionCategory.stabilizerMulEquivAut_apply_hom_hom]
  rfl

/-- Pulling back `ineffectiveKernel hs (ι y)` along a local action chart recovers the germ kernel
inside `stabilizer G y`. -/
theorem comap_stabilizerMulEquivAutOfActionChart_ineffectiveKernel
    {F : ActionCategory G X ⥤ C} [F.Full] [F.Faithful]
    (hι : Function.Injective ι) (hobj : ∀ a, F.obj a = ι a.back)
    (hσ : ∀ g : G, IsOpenEmbedding fun z : X ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv G X).symm (g, z)).hom⟩ : Quiver.Total C))
    (y : X) :
    (ineffectiveKernel hs (ι y)).comap
      (stabilizerMulEquivAutOfActionChart F hobj y).toMonoidHom =
      (germKernel G y).subgroupOf (stabilizer G y) := by
  ext g
  exact stabilizerMulEquivAutOfActionChart_mem_ineffectiveKernel_iff hs hι hobj hσ

/-- Pushing `(germKernel G y).subgroupOf (stabilizer G y)` forward along a local action chart gives
`ineffectiveKernel hs (ι y)`. -/
theorem map_stabilizerMulEquivAutOfActionChart_germKernel
    {F : ActionCategory G X ⥤ C} [F.Full] [F.Faithful]
    (hι : Function.Injective ι) (hobj : ∀ a, F.obj a = ι a.back)
    (hσ : ∀ g : G, IsOpenEmbedding fun z : X ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv G X).symm (g, z)).hom⟩ : Quiver.Total C))
    (y : X) :
    ((germKernel G y).subgroupOf (stabilizer G y)).map
      (stabilizerMulEquivAutOfActionChart F hobj y).toMonoidHom =
      ineffectiveKernel hs (ι y) := by
  rw [← comap_stabilizerMulEquivAutOfActionChart_ineffectiveKernel hs hι hobj hσ y]
  exact Subgroup.map_comap_eq_self_of_surjective
    (stabilizerMulEquivAutOfActionChart F hobj y).surjective _

/-- In a local action chart, an object `ι y` belongs to the principal locus of `C` if and only if
`stabilizer G y = germKernel G y`. -/
theorem ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel
    {F : ActionCategory G X ⥤ C} [F.Full] [F.Faithful]
    (hι : Function.Injective ι) (hobj : ∀ a, F.obj a = ι a.back)
    (hσ : ∀ g : G, IsOpenEmbedding fun z : X ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv G X).symm (g, z)).hom⟩ : Quiver.Total C))
    (y : X) :
    ineffectiveKernel hs (ι y) = ⊤ ↔ stabilizer G y = germKernel G y := by
  rw [Subgroup.eq_top_iff']
  refine ⟨fun h ↦ le_antisymm (fun g hg ↦ ?_) (germKernel_le_stabilizer y), fun h f ↦ ?_⟩
  · exact (stabilizerMulEquivAutOfActionChart_mem_ineffectiveKernel_iff hs hι hobj hσ
      (g := ⟨g, hg⟩)).mp (h _)
  · obtain ⟨g, rfl⟩ := (stabilizerMulEquivAutOfActionChart F hobj y).surjective f
    exact (stabilizerMulEquivAutOfActionChart_mem_ineffectiveKernel_iff hs hι hobj hσ).mpr
      (h ▸ g.2)

/-- **Ineffective kernel at the centre of an isotropy chart.** If `F : Aut x ⋉ X ⥤ C` lies over
an injective object map `ι : X → C`, sends each label `g` to an open embedding of arrows, and sends
`(g, z)` at a centre `z : X` to `g` itself, then `ineffectiveKernel hs x` equals
`germKernel (Aut x) z` as subgroups of `Aut x`. -/
theorem ineffectiveKernel_eq_germKernel_of_isotropy_chart
    {X : Type*} [TopologicalSpace X] {x : C} [MulAction (Aut x) X] {ι : X → C}
    (hι : Function.Injective ι) {z : X}
    {F : ActionCategory (Aut x) X ⥤ C} (hobj : ∀ a, F.obj a = ι a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun w : X ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) X).symm (g, w)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) X).symm (g, z)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩) :
    ineffectiveKernel hs x = germKernel (Aut x) z := by
  ext g
  let e := (ActionCategory.totalEquiv (Aut x) X).symm (g, z)
  have he_hom : (e.hom.hom : Aut x) = g :=
    ActionCategory.totalEquiv_symm_apply_hom_hom (g, z)
  have he_left : e.left.back = z := by
    rw [ActionCategory.totalEquiv_symm_apply_left]
    exact (ActionCategory.objEquiv (Aut x) X).left_inv z
  rw [mem_ineffectiveKernel, ← hcentre g,
    mem_ineffectiveArrows_map_iff_mem_germKernel hι hobj e.hom
      (he_hom.symm ▸ hσ g),
    he_hom, he_left]

end ActionChart

section ProperEtale

variable {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)]
  (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

include hp hs

/-- **Openness of the principal locus.** In a Hausdorff proper étale topological groupoid, the
objects whose isotropy equals their ineffective kernel form an open subset of `C`. -/
theorem isOpen_setOf_ineffectiveKernel_eq_top :
    IsOpen {x : C | ineffectiveKernel hs x = ⊤} := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have := finite_aut_of_proper_source_target hp hs x
  obtain ⟨U, hxU, act, F, hU, hcont, hFo, hfull, hfaith, hFopen, -⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs
      ((IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs)
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let : MulAction (Aut x) U := act
  have : ContinuousConstSMul (Aut x) U := ⟨hcont⟩
  have hpre : (Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤} =
      {y : U | stabilizer (Aut x) y = germKernel (Aut x) y} := by
    ext y
    exact ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs
      Subtype.val_injective hFo hFopen y
  refine ⟨(Subtype.val : U → C) '' {y : U | stabilizer (Aut x) y = germKernel (Aut x) y},
    ?_, hU.isOpenMap_subtype_val _ isOpen_setOf_stabilizer_eq_germKernel, ?_⟩
  · rw [← hpre]
    exact image_preimage_subset Subtype.val _
  · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    change (⟨x, hxU⟩ : U) ∈ (Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤} at *
    rwa [← hpre]

/-- **Density of the principal locus.** In a Hausdorff proper étale topological groupoid, the
objects whose isotropy equals their ineffective kernel form a dense subset of `C`. -/
theorem dense_setOf_ineffectiveKernel_eq_top :
    Dense {x : C | ineffectiveKernel hs x = ⊤} := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  intro x
  have := finite_aut_of_proper_source_target hp hs x
  obtain ⟨U, hxU, act, F, -, hcont, hFo, hfull, hfaith, hFopen, -⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs
      ((IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs)
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let : MulAction (Aut x) U := act
  have : ContinuousConstSMul (Aut x) U := ⟨hcont⟩
  have hpre : (Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤} =
      {y : U | stabilizer (Aut x) y = germKernel (Aut x) y} := by
    ext y
    exact ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs
      Subtype.val_injective hFo hFopen y
  have hxcl : (⟨x, hxU⟩ : U) ∈
      closure ((Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤}) := by
    rw [hpre]
    exact dense_setOf_stabilizer_eq_germKernel (⟨x, hxU⟩ : U)
  exact closure_mono (image_preimage_subset Subtype.val _)
    (image_closure_subset_closure_image continuous_subtype_val
      (mem_image_of_mem Subtype.val hxcl))

/-- In `EffectiveQuotient C` of a Hausdorff proper étale topological groupoid, the objects with
trivial isotropy form an open set. -/
theorem EffectiveQuotient.isOpen_setOf_subsingleton_aut :
    IsOpen {q : EffectiveQuotient C | Subsingleton (Aut q)} := by
  have heq : {q : EffectiveQuotient C | Subsingleton (Aut q)} =
      (EffectiveQuotient.objHomeomorph C).symm ⁻¹' {x : C | ineffectiveKernel hs x = ⊤} := by
    ext q
    simp only [mem_ofPred_eq, mem_preimage, EffectiveQuotient.objHomeomorph_symm_apply,
      ← subsingleton_aut_toEffectiveQuotient_obj_iff hs, toEffectiveQuotient_obj_objEquiv_symm]
  rw [heq]
  exact (isOpen_setOf_ineffectiveKernel_eq_top hp hs).preimage
    (EffectiveQuotient.objHomeomorph C).symm.continuous

/-- In `EffectiveQuotient C` of a Hausdorff proper étale topological groupoid, the objects with
trivial isotropy form a dense set. -/
theorem EffectiveQuotient.dense_setOf_subsingleton_aut :
    Dense {q : EffectiveQuotient C | Subsingleton (Aut q)} := by
  have heq : {q : EffectiveQuotient C | Subsingleton (Aut q)} =
      EffectiveQuotient.objHomeomorph C '' {x : C | ineffectiveKernel hs x = ⊤} := by
    ext q
    refine ⟨fun hq ↦ ⟨(EffectiveQuotient.objHomeomorph C).symm q, ?_,
      (EffectiveQuotient.objHomeomorph C).apply_symm_apply q⟩, ?_⟩
    · exact (subsingleton_aut_toEffectiveQuotient_obj_iff hs _).mp
        (by simpa using hq)
    · rintro ⟨x, hx, rfl⟩
      simpa [EffectiveQuotient.objHomeomorph_apply] using
        (subsingleton_aut_toEffectiveQuotient_obj_iff hs x).mpr hx
  rw [heq]
  exact (EffectiveQuotient.objHomeomorph C).surjective.denseRange.dense_image
    (EffectiveQuotient.objHomeomorph C).continuous
    (dense_setOf_ineffectiveKernel_eq_top hp hs)

/-- The image of the principal locus in the coarse space of a Hausdorff proper étale topological
groupoid is open. -/
theorem isOpen_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top :
    IsOpen (_root_.Quotient.mk (isIsomorphicSetoid C) ''
      {x : C | ineffectiveKernel hs x = ⊤}) :=
  (isOpenQuotientMap_isomorphismClassesMk IsTopologicalGroupoid.continuous_source
    ((IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs).isOpenMap).isOpenMap _
    (isOpen_setOf_ineffectiveKernel_eq_top hp hs)

/-- The image of the principal locus in the coarse space of a Hausdorff proper étale topological
groupoid is dense. -/
theorem dense_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top :
    Dense (_root_.Quotient.mk (isIsomorphicSetoid C) ''
      {x : C | ineffectiveKernel hs x = ⊤}) :=
  _root_.Quotient.mk_surjective.denseRange.dense_image continuous_quotient_mk'
    (dense_setOf_ineffectiveKernel_eq_top hp hs)

end ProperEtale

end TauCeti
