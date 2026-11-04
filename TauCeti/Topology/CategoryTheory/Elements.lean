/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.CategoryTheory.Elements
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Topological action groupoids of equivariant families

Let `C` be a category whose objects and total arrows `Quiver.Total C` carry topologies, as for a
topological groupoid `Γ`. An action of `C` on a family over its objects is a functor
`F : C ⥤ Type*`: the fiber over `x` is `F.obj x`, and an arrow `g : x ⟶ y` acts by
`F.map g : F.obj x → F.obj y`. The total space of the family is the type `F.Elements` of pairs of
an object and a point of its fiber, with the anchor map `Functor.Elements.obj : F.Elements → C`,
and Mathlib's category of elements `F.Elements` is the action category `Γ ⋉ Z`, an action
groupoid when `Γ` is a groupoid. For a group `G`
acting on `X`, Mathlib's `ActionCategory G X` is by definition the category of elements of
`actionAsFunctor G X`, so this generalizes the action groupoids of
`TauCeti.Topology.CategoryTheory.ActionGroupoid.Basic` to actions of groupoids.

Here the total space `Z = F.Elements` carries an arbitrary topology, and the total arrows of
`F.Elements` get the topology of the fiber product `Γ₁ ×_{Γ₀} Z` of arrows and points, matched
along the source and the anchor (`CategoryTheory.Functor.Elements.totalHomeomorph`). Thus an
arrow of `Γ ⋉ Z` is a pair `(g, z)` of an arrow `g` of `Γ` and a point `z` over its source, with
target the translate `g • z` (`CategoryTheory.Functor.Elements.act`). The action is continuous
precisely when the target map of `Γ ⋉ Z` is
(`CategoryTheory.Functor.Elements.continuous_target_iff`).

The hypotheses of a Hausdorff proper étale presentation pass from `Γ` to `Γ ⋉ Z`, given the
stated continuity of the anchor and the action:

* the total arrows remain Hausdorff and second countable when `Z` is;
* the source is continuous; the units are continuous when they are in `Γ` and the anchor is
  continuous; composition is continuous when it is in `Γ`; and, for a groupoid `Γ`, inversion is
  continuous when it is in `Γ` and the action is continuous;
* the source is a local homeomorphism when it is in `Γ` and the anchor is continuous
  (`CategoryTheory.Functor.Elements.isLocalHomeomorph_source`), since the source of `Γ ⋉ Z` is
  the base change of the source of `Γ` along the anchor (`IsLocalHomeomorph.pullback_snd`); for a
  groupoid `Γ` with continuous inversion, so is the target when moreover the action is continuous
  (`CategoryTheory.Functor.Elements.isLocalHomeomorph_target`);
* the source-target map is proper when that of `Γ` is, the anchor and the action are continuous,
  and `Z` is Hausdorff (`CategoryTheory.Functor.Elements.isProperMap_source_target`).

Natural transformations between such functors are the equivariant maps of families; when they
are continuous on total spaces they are continuous on arrows
(`CategoryTheory.NatTrans.continuous_total_mapElements`). For each point `z`, every arrow of `Γ`
whose source is the anchor of `z` gives an arrow of `Γ ⋉ Z` from `z`; distinct isotropy arrows
give distinct arrows even when they act trivially on the fibers. Arrows of `Γ` whose source has
an empty fiber have no lift.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open CategoryTheory Filter Set Topology

universe v w

namespace CategoryTheory

variable {C : Type*} [Category.{v} C]

namespace Functor.Elements

variable (F : C ⥤ Type*)

variable [TopologicalSpace (Quiver.Total C)] [TopologicalSpace F.Elements]

/-- The total arrows of the category of elements carry the topology of the fiber product of the
total arrows of `C` and the total space, along the source and the anchor. -/
instance instTopologicalSpaceTotal : TopologicalSpace (Quiver.Total F.Elements) :=
  .induced (totalEquiv F) inferInstance

/-- The total arrows of the category of elements are homeomorphic to the fiber product of the
total arrows of `C` and the total space, along the source and the anchor. -/
def totalHomeomorph : Quiver.Total F.Elements ≃ₜ
    (Quiver.Total.left : Quiver.Total C → C).Pullback (Functor.Elements.obj (F := F)) :=
  (totalEquiv F).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The arrow homeomorphism is the algebraic arrow equivalence. -/
@[simp]
theorem coe_totalHomeomorph : ⇑(totalHomeomorph F) = totalEquiv F := (rfl)

/-- The inverse arrow homeomorphism is the inverse algebraic arrow equivalence. -/
@[simp]
theorem coe_totalHomeomorph_symm : ⇑(totalHomeomorph F).symm = (totalEquiv F).symm := (rfl)

variable {F}

/-- A total arrow of the category of elements is determined by its underlying arrow of `C` and
its source, and the total arrows carry the induced topology. -/
theorem isEmbedding_total :
    IsEmbedding fun a : Quiver.Total F.Elements ↦
      ((⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C), a.left) := by
  convert IsEmbedding.subtypeVal.comp (totalHomeomorph F).isEmbedding using 1
  funext a
  simp

/-- The total arrows of the category of elements are Hausdorff when the total arrows of `C` and
the total space are. -/
instance instT2SpaceTotal [T2Space (Quiver.Total C)] [T2Space F.Elements] :
    T2Space (Quiver.Total F.Elements) :=
  isEmbedding_total.t2Space

/-- The total arrows of the category of elements are second countable when the total arrows of
`C` and the total space are. -/
instance instSecondCountableTopologyTotal [SecondCountableTopology (Quiver.Total C)]
    [SecondCountableTopology F.Elements] : SecondCountableTopology (Quiver.Total F.Elements) :=
  isEmbedding_total.isInducing.secondCountableTopology

/-- The underlying arrow of `C` of a total arrow of the category of elements depends
continuously on it. -/
@[fun_prop]
theorem continuous_total_π :
    Continuous fun a : Quiver.Total F.Elements ↦
      (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C) :=
  continuous_fst.comp isEmbedding_total.continuous

/-- The source of the category of elements is continuous. -/
@[fun_prop]
theorem continuous_source :
    Continuous (Quiver.Total.left : Quiver.Total F.Elements → F.Elements) :=
  continuous_snd.comp isEmbedding_total.continuous

/-- The target of the category of elements is continuous exactly when the action map
`Γ₁ ×_{Γ₀} Z → Z` is. -/
theorem continuous_target_iff :
    Continuous (Quiver.Total.right : Quiver.Total F.Elements → F.Elements) ↔
      Continuous (act F) := by
  rw [← (totalHomeomorph F).symm.comp_continuous_iff']
  congr!
  funext q
  simp

/-- Composition in the category of elements is continuous on composable pairs when composition
in `C` is. -/
theorem continuous_comp
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C)) :
    Continuous fun p : {p : Quiver.Total F.Elements × Quiver.Total F.Elements //
        p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ :
        Quiver.Total F.Elements) := by
  let π := fun a : Quiver.Total F.Elements ↦
    (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C)
  let g := fun p : {p : Quiver.Total F.Elements × Quiver.Total F.Elements //
      p.1.right = p.2.left} ↦
    (⟨(π p.1.1, π p.1.2), congrArg Functor.Elements.obj p.2⟩ :
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})
  have hg : Continuous g :=
    ((continuous_total_π.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_total_π.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  refine isEmbedding_total.continuous_iff.mpr (((hc.comp hg).prodMk
    (continuous_source.comp (continuous_fst.comp continuous_subtype_val))).congr fun p ↦ ?_)
  obtain ⟨⟨⟨x, y, f⟩, ⟨y', z, f'⟩⟩, h⟩ := p
  dsimp only at h
  subst h
  simp [g, π]

variable [TopologicalSpace C]

/-- The unit map of the category of elements is continuous when the unit map of `C` and the
anchor are. -/
theorem continuous_unit (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hp : Continuous (Functor.Elements.obj : F.Elements → C)) :
    Continuous fun x : F.Elements ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total F.Elements) :=
  isEmbedding_total.continuous_iff.mpr ((hu.comp hp).prodMk continuous_id)

/-- The source of the category of elements is a local homeomorphism when the source of `C` is
one and the anchor is continuous: it is the base change of the source of `C` along the anchor. -/
theorem isLocalHomeomorph_source
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : Continuous (Functor.Elements.obj : F.Elements → C)) :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total F.Elements → F.Elements) :=
  -- The source is the second projection of the fiber product, read through `totalHomeomorph`.
  have h : (Quiver.Total.left : Quiver.Total F.Elements → F.Elements) =
      Function.Pullback.snd ∘ totalHomeomorph F := by
    funext a
    simp [Function.Pullback.snd]
  h ▸ (hs.pullback_snd hp).comp (totalHomeomorph F).isLocalHomeomorph

/-- The source-target map of the category of elements is proper when the source-target map of
`C` is proper, the anchor and the action are continuous, and the total space is Hausdorff. -/
theorem isProperMap_source_target [T2Space F.Elements]
    (hst : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hp : Continuous (Functor.Elements.obj : F.Elements → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total F.Elements → F.Elements)) :
    IsProperMap fun a : Quiver.Total F.Elements ↦ (a.left, a.right) := by
  refine isProperMap_iff_ultrafilter.mpr ⟨continuous_source.prodMk ht, fun 𝒰 w hw ↦ ?_⟩
  have hl := (continuous_fst.tendsto w).comp hw
  have hr := (continuous_snd.tendsto w).comp hw
  -- The underlying arrows of `C` converge to an arrow `g` between the anchors of the limits.
  obtain ⟨g, hg, h𝒰⟩ := (isProperMap_iff_ultrafilter.mp hst).2
    (𝒰 := 𝒰.map fun a : Quiver.Total F.Elements ↦
      (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C))
    (y := (w.1.obj, w.2.obj))
    (((hp.tendsto _).comp hl).prodMk_nhds ((hp.tendsto _).comp hr))
  simp only [Prod.mk.injEq] at hg
  -- The arrow `(g, w.1)` of `Γ ⋉ Z` is a limit, and its target is `w.2` by separation.
  let a := (totalEquiv F).symm ⟨(g, w.1), hg.1⟩
  have ha : (𝒰 : Filter (Quiver.Total F.Elements)) ≤ 𝓝 a := by
    rw [← tendsto_id', isEmbedding_total.tendsto_nhds_iff]
    have hea : ((⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C), a.left) =
        (g, w.1) := by
      simpa only [totalEquiv_apply] using
        congrArg Subtype.val ((totalEquiv F).apply_symm_apply ⟨(g, w.1), hg.1⟩)
    rw [hea]
    exact (tendsto_map'_iff.mp h𝒰).prodMk_nhds hl
  exact ⟨a, Prod.ext (totalEquiv_symm_apply_left F _)
    (tendsto_nhds_unique ((ht.tendsto a).comp ha) hr), ha⟩

section Groupoid

variable {G : Type*} [Groupoid G] [TopologicalSpace G] [TopologicalSpace (Quiver.Total G)]
  {F : G ⥤ Type*} [TopologicalSpace F.Elements]

omit [TopologicalSpace G] in
/-- Inversion in the category of elements of a groupoid is continuous when inversion in the
groupoid and the action are. -/
theorem continuous_inverse
    (hi : Continuous fun a : Quiver.Total G ↦
      (⟨a.right, a.left, CategoryTheory.inv a.hom⟩ : Quiver.Total G))
    (ht : Continuous (Quiver.Total.right : Quiver.Total F.Elements → F.Elements)) :
    Continuous fun a : Quiver.Total F.Elements ↦
      (⟨a.right, a.left, CategoryTheory.inv a.hom⟩ : Quiver.Total F.Elements) := by
  refine isEmbedding_total.continuous_iff.mpr (((hi.comp continuous_total_π).prodMk ht).congr
    fun a ↦ ?_)
  -- Inversion in `F.Elements` is inversion of the underlying arrow (`Functor.Elements.groupoid`).
  simp only [← Groupoid.inv_eq_inv]
  rfl

/-- The target of the category of elements of a groupoid is a local homeomorphism when the source
of the groupoid is one, inversion in the groupoid is continuous, and the anchor and the action
are continuous. -/
theorem isLocalHomeomorph_target
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total G → G))
    (hi : Continuous fun a : Quiver.Total G ↦
      (⟨a.right, a.left, CategoryTheory.inv a.hom⟩ : Quiver.Total G))
    (hp : Continuous (Functor.Elements.obj : F.Elements → G))
    (ht : Continuous (Quiver.Total.right : Quiver.Total F.Elements → F.Elements)) :
    IsLocalHomeomorph (Quiver.Total.right : Quiver.Total F.Elements → F.Elements) := by
  -- Inversion is a continuous involution, hence a homeomorphism exchanging source and target.
  let ι : Quiver.Total F.Elements ≃ₜ Quiver.Total F.Elements :=
    { toFun a := ⟨a.right, a.left, CategoryTheory.inv a.hom⟩
      invFun a := ⟨a.right, a.left, CategoryTheory.inv a.hom⟩
      left_inv a := by simp
      right_inv a := by simp
      continuous_toFun := continuous_inverse hi ht
      continuous_invFun := continuous_inverse hi ht }
  exact (isLocalHomeomorph_source hs hp).comp ι.isLocalHomeomorph

end Groupoid

end Functor.Elements

namespace NatTrans

variable [TopologicalSpace (Quiver.Total C)] {F F' : C ⥤ Type w} [TopologicalSpace F.Elements]
  [TopologicalSpace F'.Elements]

/-- An equivariant map of families over the objects of `C` that is continuous on total spaces is
continuous on the total arrows of the action categories. -/
theorem continuous_total_mapElements (φ : F ⟶ F') (hφ : Continuous (φ.mapElements).obj) :
    Continuous fun a : Quiver.Total F.Elements ↦
      (⟨φ.mapElements.obj a.left, φ.mapElements.obj a.right, φ.mapElements.map a.hom⟩ :
        Quiver.Total F'.Elements) :=
  Functor.Elements.isEmbedding_total.continuous_iff.mpr
    (Functor.Elements.continuous_total_π.prodMk (hφ.comp Functor.Elements.continuous_source))

end NatTrans

end CategoryTheory
