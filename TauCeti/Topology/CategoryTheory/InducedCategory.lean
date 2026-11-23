/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Topology.CategoryTheory.Functor.IsomorphismClasses
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses
public import TauCeti.Topology.IsLocalHomeomorph
public import TauCeti.Topology.Maps.Proper.Basic

/-!
# Pullback groupoids

Let `D` be a category whose objects and total arrows carry topologies, as for a topological
groupoid, and let `f : M → D` be a map from a topological space `M`. Mathlib's induced category
`CategoryTheory.InducedCategory D f` has objects `M` and arrows `x ⟶ y` the arrows `f x ⟶ f y`
of `D`. When `D` is a groupoid this is the pullback groupoid `f*D`, and the fully faithful
`CategoryTheory.inducedFunctor f` is the identity on arrows. Pulling back along the disjoint
union of a family of charts gives the groupoid presented by those charts, with every arrow of `D`
between chart points retained, including isotropy acting trivially.

This file topologizes `InducedCategory D f`. Its objects carry the topology of `M`. Its total
arrows are homeomorphic to the fiber product of the source-target map of `D` with `f × f`
(`CategoryTheory.InducedCategory.totalHomeomorph`): an arrow is recorded by its underlying total
arrow of `D` and its two endpoints. With these topologies:

* source, target and the induced functor on total arrows are continuous, and the pullback of a
  topological groupoid along a continuous map is a topological groupoid
  (`CategoryTheory.InducedCategory.isTopologicalGroupoid`);
* the total arrows are Hausdorff, respectively second countable, when `M` and the total arrows of
  `D` are;
* the source-target map is proper when that of `D` is and `f` is continuous
  (`CategoryTheory.InducedCategory.isProperMap_source_target`), being its base change along
  `f × f`;
* the source is a local homeomorphism when `f` and the source of `D` are and the target of `D` is
  continuous (`CategoryTheory.InducedCategory.isLocalHomeomorph_source`), and so is the target for
  a topological groupoid `D` (`CategoryTheory.InducedCategory.isLocalHomeomorph_target`).

So the pullback of a Hausdorff proper étale groupoid along a local homeomorphism from a Hausdorff
space is again a Hausdorff proper étale groupoid.

If moreover `f` is open and its image meets every orbit, the induced functor induces a
homeomorphism of coarse spaces
(`CategoryTheory.InducedCategory.isHomeomorph_isomorphismClasses_map_inducedFunctor`), although
`f` need not be surjective. The isotropy group at `x` is that of `D` at `f x`, by Mathlib's
`CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful` applied to
`CategoryTheory.fullyFaithfulInducedFunctor f`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Sections 5.3 and 5.4.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open Topology

namespace CategoryTheory.InducedCategory

section Topology

variable {M D : Type*} [Category D] (f : M → D) [TopologicalSpace M]

/-- The objects of the pullback along `f : M → D` carry the topology of `M`. -/
instance instTopologicalSpace : TopologicalSpace (InducedCategory D f) :=
  inferInstanceAs (TopologicalSpace M)

/-- The objects of the pullback are Hausdorff when `M` is. -/
instance instT2Space [T2Space M] : T2Space (InducedCategory D f) :=
  inferInstanceAs (T2Space M)

/-- The objects of the pullback are second countable when `M` is. -/
instance instSecondCountableTopology [SecondCountableTopology M] :
    SecondCountableTopology (InducedCategory D f) :=
  inferInstanceAs (SecondCountableTopology M)

variable [TopologicalSpace (Quiver.Total D)]

/-- The total arrows of the pullback along `f` carry the topology of the fiber product of the
source-target map of `D` with `f × f`: an arrow is recorded by its underlying total arrow of `D`
and its two endpoints in `M`. -/
instance instTopologicalSpaceTotal : TopologicalSpace (Quiver.Total (InducedCategory D f)) :=
  .induced (fun a ↦ (⟨((inducedFunctor f).toPrefunctor.mapTotal a, ((a.left : M), (a.right : M))),
    rfl⟩ : (fun a : Quiver.Total D ↦ (a.left, a.right)).Pullback (Prod.map f f))) inferInstance

/-- The total arrows of the pullback along `f` are homeomorphic to the fiber product of the
source-target map of `D` with `f × f`. -/
def totalHomeomorph : Quiver.Total (InducedCategory D f) ≃ₜ
    (fun a : Quiver.Total D ↦ (a.left, a.right)).Pullback (Prod.map f f) :=
  Equiv.toHomeomorphOfIsInducing
    { toFun a := ⟨((inducedFunctor f).toPrefunctor.mapTotal a, ((a.left : M), (a.right : M))), rfl⟩
      invFun p := ⟨p.val.2.1, p.val.2.2, homMk (Quiver.homOfEq p.val.1.hom
        (Prod.ext_iff.mp p.property).1 (Prod.ext_iff.mp p.property).2)⟩
      left_inv _ := rfl
      right_inv _ := Subtype.ext (Prod.ext (Quiver.Total.mk_homOfEq _ _ _) rfl) } ⟨rfl⟩

/-- The homeomorphism records an arrow of the pullback by its underlying total arrow of `D` and
its endpoints. -/
@[simp]
theorem totalHomeomorph_apply (a : Quiver.Total (InducedCategory D f)) :
    totalHomeomorph f a =
      ⟨((inducedFunctor f).toPrefunctor.mapTotal a, ((a.left : M), (a.right : M))), rfl⟩ := (rfl)

/-- The inverse homeomorphism reads a total arrow of `D` as an arrow between the given points. -/
@[simp]
theorem totalHomeomorph_symm_apply
    (p : (fun a : Quiver.Total D ↦ (a.left, a.right)).Pullback (Prod.map f f)) :
    (totalHomeomorph f).symm p = ⟨p.val.2.1, p.val.2.2, homMk (Quiver.homOfEq p.val.1.hom
        (Prod.ext_iff.mp p.property).1 (Prod.ext_iff.mp p.property).2)⟩ := (rfl)

variable {f} in
/-- A map into the total arrows of the pullback is continuous exactly when its source, its target
and its underlying total arrow of `D` are. -/
theorem continuous_total_iff {Y : Type*} [TopologicalSpace Y]
    {g : Y → Quiver.Total (InducedCategory D f)} :
    Continuous g ↔ Continuous (fun y ↦ ((g y).left : M)) ∧ Continuous (fun y ↦ ((g y).right : M)) ∧
      Continuous (fun y ↦ (inducedFunctor f).toPrefunctor.mapTotal (g y)) := by
  refine ⟨fun hg ↦ ?_, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  · have h := continuous_subtypeVal.comp ((totalHomeomorph f).continuous.comp hg)
    exact ⟨continuous_fst.comp (continuous_snd.comp h),
      continuous_snd.comp (continuous_snd.comp h), continuous_fst.comp h⟩
  · exact (totalHomeomorph f).isInducing.continuous_iff.mpr
      ((h₃.prodMk (h₁.prodMk h₂)).subtype_mk _)

/-- The source of the pullback is continuous. -/
@[fun_prop]
theorem continuous_source :
    Continuous (Quiver.Total.left : Quiver.Total (InducedCategory D f) → InducedCategory D f) :=
  (continuous_total_iff.mp continuous_id).1

/-- The target of the pullback is continuous. -/
@[fun_prop]
theorem continuous_target :
    Continuous (Quiver.Total.right : Quiver.Total (InducedCategory D f) → InducedCategory D f) :=
  (continuous_total_iff.mp continuous_id).2.1

/-- The induced functor is continuous on total arrows. -/
@[fun_prop]
theorem continuous_mapTotal_inducedFunctor :
    Continuous (inducedFunctor f).toPrefunctor.mapTotal :=
  (continuous_total_iff.mp continuous_id).2.2

/-- The total arrows of the pullback are Hausdorff when `M` and the total arrows of `D` are. -/
instance instT2SpaceTotal [T2Space M] [T2Space (Quiver.Total D)] :
    T2Space (Quiver.Total (InducedCategory D f)) :=
  (totalHomeomorph f).symm.t2Space

/-- The total arrows of the pullback are second countable when `M` and the total arrows of `D`
are. -/
instance instSecondCountableTopologyTotal [SecondCountableTopology M]
    [SecondCountableTopology (Quiver.Total D)] :
    SecondCountableTopology (Quiver.Total (InducedCategory D f)) :=
  have : SecondCountableTopology
      ((fun a : Quiver.Total D ↦ (a.left, a.right)).Pullback (Prod.map f f)) :=
    inferInstanceAs (SecondCountableTopology
      {p : Quiver.Total D × (M × M) | (p.1.left, p.1.right) = Prod.map f f p.2})
  (totalHomeomorph f).isInducing.secondCountableTopology

variable {f}

/-- **The pullback of a topological groupoid is a topological groupoid.** Units, inversion and
composition are computed in `D`, so they are continuous when they are in `D` and `f` is
continuous. -/
theorem isTopologicalGroupoid [IsGroupoid D] [TopologicalSpace D]
    [TauCeti.IsTopologicalGroupoid D] (hf : Continuous f) :
    TauCeti.IsTopologicalGroupoid (InducedCategory D f) where
  continuous_source := continuous_source f
  continuous_target := continuous_target f
  continuous_unit := continuous_total_iff.mpr ⟨continuous_id, continuous_id,
    TauCeti.IsTopologicalGroupoid.continuous_unit.comp hf⟩
  continuous_inverse := by
    -- The induced functor commutes with inversion, which is computed in `D`.
    have h : (fun a : Quiver.Total (InducedCategory D f) ↦
        (inducedFunctor f).toPrefunctor.mapTotal ⟨a.right, a.left, inv a.hom⟩) =
        (fun a : Quiver.Total D ↦ ⟨a.right, a.left, inv a.hom⟩) ∘
          (inducedFunctor f).toPrefunctor.mapTotal :=
      funext fun a ↦ congrArg (fun h ↦ (⟨f a.right, f a.left, h⟩ : Quiver.Total D))
        ((inducedFunctor f).map_inv a.hom)
    refine continuous_total_iff.mpr ⟨continuous_target f, continuous_source f, ?_⟩
    rw [h]
    exact TauCeti.IsTopologicalGroupoid.continuous_inverse.comp
      (continuous_mapTotal_inducedFunctor f)
  continuous_comp := by
    let φ := (inducedFunctor f).toPrefunctor.mapTotal
    have hfst : Continuous fun p : {p : Quiver.Total (InducedCategory D f) ×
        Quiver.Total (InducedCategory D f) // p.1.right = p.2.left} ↦ p.val.1 :=
      continuous_fst.comp continuous_subtypeVal
    have hsnd : Continuous fun p : {p : Quiver.Total (InducedCategory D f) ×
        Quiver.Total (InducedCategory D f) // p.1.right = p.2.left} ↦ p.val.2 :=
      continuous_snd.comp continuous_subtypeVal
    -- A composable pair of the pullback maps to a composable pair of `D`.
    let g : {p : Quiver.Total (InducedCategory D f) × Quiver.Total (InducedCategory D f) //
        p.1.right = p.2.left} → {q : Quiver.Total D × Quiver.Total D // q.1.right = q.2.left} :=
      fun p ↦ ⟨(φ p.val.1, φ p.val.2), congrArg f p.property⟩
    have hg : Continuous g := (((continuous_mapTotal_inducedFunctor f).comp hfst).prodMk
      ((continuous_mapTotal_inducedFunctor f).comp hsnd)).subtype_mk _
    refine continuous_total_iff.mpr ⟨?_, ?_, ?_⟩
    · simpa only [Quiver.Total.comp_left, Function.comp_def] using (continuous_source f).comp hfst
    · simpa only [Quiver.Total.comp_right, Function.comp_def] using (continuous_target f).comp hsnd
    convert TauCeti.IsTopologicalGroupoid.continuous_comp.comp hg using 1
    funext ⟨⟨a, b⟩, h⟩
    rw [Function.comp_apply, Quiver.Total.comp_def, Quiver.Total.comp_def]
    simp [g, φ, Prefunctor.mapTotal]

/-- **Properness is stable under pullback.** The source-target map of the pullback along a
continuous `f` is the base change of that of `D` along `f × f`, so it is proper when the
source-target map of `D` is. No separation hypothesis is needed. -/
theorem isProperMap_source_target [TopologicalSpace D] (hf : Continuous f)
    (h : IsProperMap fun a : Quiver.Total D ↦ (a.left, a.right)) :
    IsProperMap fun a : Quiver.Total (InducedCategory D f) ↦ ((a.left : M), (a.right : M)) :=
  (h.pullback_snd (hf.prodMap hf)).comp (totalHomeomorph f).isProperMap

variable (f) in
/-- The total arrows of the pullback along `f` are obtained from `M` by two base changes: of the
source of `D` along `f`, giving the arrows of `D` out of points of `f`, and then of `f` along the
target of these arrows. -/
private def totalHomeomorphPullbackPullback :
    Quiver.Total (InducedCategory D f) ≃ₜ
      f.Pullback (fun q : (Quiver.Total.left : Quiver.Total D → D).Pullback f ↦ q.val.1.right) where
  toFun a := ⟨((a.right : M), ⟨((inducedFunctor f).toPrefunctor.mapTotal a, (a.left : M)), rfl⟩),
    rfl⟩
  invFun r := ⟨r.val.2.val.2, r.val.1, homMk (Quiver.homOfEq r.val.2.val.1.hom r.val.2.property
    r.property.symm)⟩
  left_inv _ := rfl
  right_inv r := Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext (Quiver.Total.mk_homOfEq _ _ _)
    rfl)))
  continuous_toFun := ((continuous_target f).prodMk (((continuous_mapTotal_inducedFunctor f).prodMk
    (continuous_source f)).subtype_mk _)).subtype_mk _
  continuous_invFun := by
    have h₁ : Continuous fun r : f.Pullback
        (fun q : (Quiver.Total.left : Quiver.Total D → D).Pullback f ↦ q.val.1.right) ↦
          r.val.2.val :=
      continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal)
    refine continuous_total_iff.mpr ⟨continuous_snd.comp h₁, continuous_fst.comp
      continuous_subtypeVal, ?_⟩
    convert continuous_fst.comp h₁ using 1
    funext r
    exact Quiver.Total.mk_homOfEq _ _ _

/-- **Étaleness is stable under pullback along local homeomorphisms.** If `f` and the source of
`D` are local homeomorphisms and the target of `D` is continuous, the source of the pullback along
`f` is a local homeomorphism. No separation hypothesis is needed. -/
theorem isLocalHomeomorph_source [TopologicalSpace D] (hf : IsLocalHomeomorph f)
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D))
    (ht : Continuous (Quiver.Total.right : Quiver.Total D → D)) :
    IsLocalHomeomorph
      (Quiver.Total.left : Quiver.Total (InducedCategory D f) → InducedCategory D f) := by
  -- The source is the composite of the two base-change projections and a homeomorphism.
  have h₁ := hs.pullback_snd hf.continuous
  have h₂ := hf.pullback_snd (g := fun q : (Quiver.Total.left : Quiver.Total D → D).Pullback f ↦
    q.val.1.right) (ht.comp (continuous_fst.comp continuous_subtypeVal))
  exact (h₁.comp h₂).comp (totalHomeomorphPullbackPullback f).isLocalHomeomorph

/-- The target of the pullback of an étale topological groupoid along a local homeomorphism is a
local homeomorphism, since inversion exchanges source and target. -/
theorem isLocalHomeomorph_target [IsGroupoid D] [TopologicalSpace D]
    [TauCeti.IsTopologicalGroupoid D] (hf : IsLocalHomeomorph f)
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D)) :
    IsLocalHomeomorph
      (Quiver.Total.right : Quiver.Total (InducedCategory D f) → InducedCategory D f) :=
  have := isTopologicalGroupoid hf.continuous
  (TauCeti.IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target _).mp
    (isLocalHomeomorph_source hf hs TauCeti.IsTopologicalGroupoid.continuous_target)

end Topology

section Coarse

universe v u

variable {M D : Type u} [Groupoid.{v} D] {f : M → D} [TopologicalSpace M] [TopologicalSpace D]
  [TopologicalSpace (Quiver.Total D)]

/-- **Coarse spaces of pullbacks.** Let `D` be a groupoid with continuous source and open target,
and let `f : M → D` be continuous and open, meeting every orbit. Then the induced functor from the
pullback along `f` induces a homeomorphism of coarse spaces. The map `f` need not be surjective:
it can be the disjoint union of a family of open charts whose images meet every orbit. -/
theorem isHomeomorph_isomorphismClasses_map_inducedFunctor
    (hs : Continuous (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsOpenMap (Quiver.Total.right : Quiver.Total D → D)) (hf : Continuous f)
    (hf' : IsOpenMap f) (hsurj : ∀ y : D, ∃ x : M, Nonempty (f x ≅ y)) :
    IsHomeomorph (X := Quotient (isIsomorphicSetoid (InducedCategory D f)))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map (inducedFunctor f).toCatHom) :=
  have : (inducedFunctor f).EssSurj := ⟨hsurj⟩
  (inducedFunctor f).isHomeomorph_isomorphismClasses_map hf
    ((TauCeti.isOpenQuotientMap_isomorphismClassesMk hs ht).isOpenMap.comp hf')

end Coarse

end CategoryTheory.InducedCategory
