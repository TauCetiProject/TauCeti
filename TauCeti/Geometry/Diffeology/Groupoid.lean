/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Diffeology.Manifold
public import TauCeti.Geometry.Diffeology.Quotient
public import TauCeti.Topology.CategoryTheory.Etale
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses

/-!
# The coarse diffeology of an étale groupoid

Let `C` be a categorical groupoid whose objects form a diffeological space. Its coarse space, the
native quotient `Quotient (isIsomorphicSetoid C)` of the objects by isomorphism, carries the
quotient diffeology (`TauCeti.Diffeology.instDiffeologicalSpaceQuotient`). When the objects form
a smooth manifold with its manifold diffeology, the D-topology of this coarse diffeology is the
coarse quotient topology (`TauCeti.Diffeology.instIsDTopologyCompatibleQuotient`).

This file shows that this coarse diffeology is glued from the quotient diffeologies of open sets
of objects. Let `U` be a D-open set of objects and `r` a relation on `U` relating any two objects
joined by an arrow, for instance the orbit relation of a local action. Suppose that every
arrow `y ⟶ u` with `u ∈ U` extends to a *smooth local transport*: a map `τ`, smooth on a D-open
neighbourhood `V` of `y`, with `τ y = u` and an arrow `z ⟶ τ z` for every `z ∈ V`. Then the map
`U / r → C / ≅` sending the class of `y` to its isomorphism class is an induction with D-open
image (`TauCeti.Diffeology.isInduction_of_mk_eq_isomorphismClassesMk`,
`TauCeti.Diffeology.isOpen_range_of_mk_eq_isomorphismClassesMk`). So near the classes meeting
`U`, a map into the coarse space is a plot exactly when it locally lifts to a plot of `U`.

The point is the converse of smoothness: a plot `ℓ` of the objects whose classes lie in the image
of `U` is moved into `U` by a smooth local transport, without changing its classes.

If the source of `C` is a smooth local diffeomorphism and its target is smooth, the composite of
the target with a local inverse of the source through an arrow is such a transport. Combined with
the local isotropy action of a Hausdorff proper étale groupoid
(`TauCeti.exists_isotropy_action_of_proper_source_target`), this gives finite quotient charts of
the coarse diffeology: every object `x` has an open neighbourhood `U` with an action of the finite
isotropy group `Aut x`, presenting the full subgroupoid on `U`, such that `U / Aut x → C / ≅` is an
induction and an open embedding
(`TauCeti.Diffeology.exists_isotropy_action_isInduction_of_proper_source_target`). Every isotropy
arrow is retained as a label of this action, including arrows acting trivially on `U`; the coarse
diffeology does not see this ineffective part of the isotropy.

## Main results

* `TauCeti.Diffeology.isInduction_of_mk_eq_isomorphismClassesMk`: open pieces of the coarse
  diffeology, given smooth local transports.
* `TauCeti.Diffeology.isOpen_range_of_mk_eq_isomorphismClassesMk`: their images are D-open.
* `TauCeti.Diffeology.exists_isotropy_action_isInduction_of_proper_source_target`: finite
  quotient charts of the coarse diffeology of a smooth proper étale groupoid.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2, for the local isotropy charts
  of a proper étale groupoid.
* P. Iglesias-Zemmour, Y. Karshon and M. Zadka, *Orbifolds as diffeologies*, Trans. Amer. Math.
  Soc. **362** (2010), for orbifold diffeologies locally modelled on finite quotients.
* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 1, for inductions and quotient diffeologies.
-/

public noncomputable section

open CategoryTheory Function Set Topology MulAction
open scoped Manifold ContDiff

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

section Transport

variable {C : Type*} [Groupoid C] [DiffeologicalSpace C] {U : Set C} {r : Setoid U}
  {φ : Quotient r → Quotient (isIsomorphicSetoid C)}

/-- **Open pieces of the coarse diffeology.** Let `U` be a D-open set of objects of a groupoid and
`r` a relation on `U` relating any two objects joined by an arrow. Suppose every arrow
`y ⟶ u` with `u ∈ U` extends to a smooth local transport: a map `τ` with `τ y = u`, smooth on a
D-open neighbourhood `V` of `y`, with an arrow `z ⟶ τ z` for every `z ∈ V`. Then a map
`U / r → C / ≅` sending the class of each `y` to its isomorphism class is an induction: a map into
`U / r` is a plot exactly when its image in the coarse space is a plot. -/
theorem isInduction_of_mk_eq_isomorphismClassesMk
    (hU : IsOpen[_root_.Diffeology.dTopology] U)
    (htr : ∀ ⦃y u : C⦄, (y ⟶ u) → u ∈ U → ∃ V : Set C, IsOpen[_root_.Diffeology.dTopology] V ∧
      y ∈ V ∧ ∃ τ : C → C, τ y = u ∧ _root_.Diffeology.DSmooth (V.domRestrict τ) ∧
        ∀ z ∈ V, Nonempty (z ⟶ τ z))
    (hr : ∀ y y' : U, Nonempty ((y : C) ⟶ y') → r y y')
    (hφ : ∀ y, φ (Quotient.mk r y) = Quotient.mk (isIsomorphicSetoid C) (y : C)) :
    IsInduction φ where
  injective := injective_of_mk_eq_isomorphismClassesMk hr hφ
  isPlot_iff {n p} := by
    have hcomp : φ ∘ Quotient.mk r = Quotient.mk (isIsomorphicSetoid C) ∘ Subtype.val := funext hφ
    have hφs : _root_.Diffeology.DSmooth φ := ((isSubduction_quotient_mk r).dSmooth_iff φ).mpr
      (hcomp ▸ (dSmooth_quotient_mk _).comp dSmooth_subtype_val)
    refine ⟨fun hp ↦ hφs n p hp, fun hp ↦ ?_⟩
    refine (isPlot_quotient_iff r).mpr (locallyLifts_iff.mpr fun z _ ↦ ?_)
    -- Near `z`, the image of `p` in the coarse space lifts to a plot `ℓ` of the objects.
    obtain ⟨v, hv, hzv, -, ℓ, hℓ, hℓp⟩ :=
      locallyLifts_iff.mp ((isPlot_quotient_iff _).mp hp) z (mem_univ z)
    obtain ⟨u, hu⟩ := Quotient.exists_rep (p z)
    -- An arrow from `ℓ z` to a representative `u ∈ U` of `p z` has a smooth local transport `τ`.
    obtain ⟨f⟩ : Nonempty (ℓ z ⟶ (u : C)) :=
      isomorphismClassesMk_eq_iff.mp ((hℓp hzv).trans (by rw [Function.comp_apply, ← hu, hφ]))
    obtain ⟨V, hV, hzV, τ, hτ, hτs, hτV⟩ := htr f u.2
    -- `τ ∘ ℓ` is a plot near `z` passing through `u`, so it lands in the open set `U` near `z`.
    let : TopologicalSpace C := _root_.Diffeology.dTopology
    have hw : IsOpen (v ∩ ℓ ⁻¹' V) := (hℓ.continuousOn hv).isOpen_inter_preimage hv hV
    have hτℓ : IsPlotOn (v ∩ ℓ ⁻¹' V) (τ ∘ ℓ) := hℓ.comp_inter_preimage hτs
    have hw' : IsOpen (v ∩ ℓ ⁻¹' V ∩ (τ ∘ ℓ) ⁻¹' U) :=
      (hτℓ.continuousOn hw).isOpen_inter_preimage hw hU
    classical
    let lift : 𝔼ⁿ → U := fun y ↦ if h : τ (ℓ y) ∈ U then ⟨τ (ℓ y), h⟩ else u
    have hlift : ∀ y ∈ v ∩ ℓ ⁻¹' V ∩ (τ ∘ ℓ) ⁻¹' U, (lift y : C) = τ (ℓ y) := fun y hy ↦ by
      simp [lift, show τ (ℓ y) ∈ U from hy.2]
    refine ⟨_, hw', ⟨⟨hzv, hzV⟩, by simp [hτ]⟩, subset_univ _, lift,
      isPlotOn_subtype_iff.mpr ((hτℓ.mono inter_subset_left).congr fun y hy ↦ (hlift y hy).symm),
      fun y hy ↦ injective_of_mk_eq_isomorphismClassesMk hr hφ ?_⟩
    -- Transport along `τ` does not change isomorphism classes.
    rw [Function.comp_apply, hφ, hlift y hy, ← Function.comp_apply (f := φ), ← hℓp hy.1.1,
      Function.comp_apply, isomorphismClassesMk_eq_iff]
    exact (hτV _ hy.1.2).map Groupoid.inv

/-- Under the hypotheses of `TauCeti.Diffeology.isInduction_of_mk_eq_isomorphismClassesMk`, the
image of `U / r` in the coarse space, the set of classes meeting `U`, is open for the
D-topology. -/
theorem isOpen_range_of_mk_eq_isomorphismClassesMk
    (hU : IsOpen[_root_.Diffeology.dTopology] U)
    (htr : ∀ ⦃y u : C⦄, (y ⟶ u) → u ∈ U → ∃ V : Set C, IsOpen[_root_.Diffeology.dTopology] V ∧
      y ∈ V ∧ ∃ τ : C → C, τ y = u ∧ _root_.Diffeology.DSmooth (V.domRestrict τ) ∧
        ∀ z ∈ V, Nonempty (z ⟶ τ z))
    (hφ : ∀ y, φ (Quotient.mk r y) = Quotient.mk (isIsomorphicSetoid C) (y : C)) :
    IsOpen[_root_.Diffeology.dTopology] (range φ) := by
  have hcomp : φ ∘ Quotient.mk r = Quotient.mk (isIsomorphicSetoid C) ∘ Subtype.val := funext hφ
  have hrange : range φ = Quotient.mk (isIsomorphicSetoid C) '' U := by
    rw [← (Quotient.mk_surjective (s := r)).range_comp, hcomp, range_comp, Subtype.range_coe]
  -- The D-topology of the quotient diffeology is coinduced from the D-topology of the objects.
  have htop : (_root_.Diffeology.dTopology : TopologicalSpace (Quotient (isIsomorphicSetoid C))) =
      .coinduced (Quotient.mk _) _root_.Diffeology.dTopology :=
    dTopology_coinducedDiffeology _
  rw [hrange, htop, isOpen_coinduced]
  let : TopologicalSpace C := _root_.Diffeology.dTopology
  refine isOpen_iff_forall_mem_open.mpr fun y ⟨u, huU, hu⟩ ↦ ?_
  -- Near `y`, a smooth local transport moves objects into `U` without changing their classes.
  obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.mp hu.symm
  obtain ⟨V, hV, hyV, τ, hτ, hτs, hτV⟩ := htr f huU
  refine ⟨V ∩ τ ⁻¹' U, fun z hz ↦ ⟨τ z, hz.2, isomorphismClassesMk_eq_iff.mpr
      ((hτV z hz.1).map Groupoid.inv)⟩,
    (continuousOn_dTopology_of_dSmooth_domRestrict hV hτs).isOpen_inter_preimage hV hU, hyV, ?_⟩
  rw [mem_preimage, hτ]
  exact huU

end Transport

section Manifold

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℝ, E) ∞ C]
  [DiffeologicalSpace C] [IsContMDiffCompatible E C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace E' (Quiver.Total C)]

/-- If the source is a smooth local diffeomorphism and the target is smooth, then following a
local inverse of the source through an arrow `y ⟶ u` and then the target is a smooth local
transport from `y` to `u`. -/
private theorem exists_transport
    (hs : IsLocalDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ (Quiver.Total.right : Quiver.Total C → C))
    ⦃y u : C⦄ (f : y ⟶ u) :
    ∃ V : Set C, IsOpen[_root_.Diffeology.dTopology] V ∧ y ∈ V ∧ ∃ τ : C → C, τ y = u ∧
      _root_.Diffeology.DSmooth (V.domRestrict τ) ∧ ∀ z ∈ V, Nonempty (z ⟶ τ z) := by
  have ha := hs ⟨y, u, f⟩
  -- Every arrow `b` with source `z` gives an arrow from `z` to the target of `b`.
  have harrow (z : C) (b : Quiver.Total C) (hb : b.left = z) : Nonempty (z ⟶ b.right) := by
    obtain ⟨_, _, g⟩ := b
    exact hb ▸ ⟨g⟩
  refine ⟨ha.localInverse.source,
    (_root_.Diffeology.IsDTopologyCompatible.dTop_eq C).symm ▸ ha.localInverse_open_source,
    ha.localInverse_mem_source, fun z ↦ (ha.localInverse z).right,
    congrArg Quiver.Total.right (ha.localInverse_left_inv ha.localInverse_mem_target),
    (ht.comp_contMDiffOn ha.contMDiffOn_localInverse).dSmooth_domRestrict,
    fun z hz ↦ harrow z _ (ha.localInverse_right_inv hz)⟩

/-- **Finite quotient charts of the coarse diffeology of a proper étale groupoid.** Let `C` be a
groupoid whose objects and total arrows are smooth manifolds, with source and target smooth local
diffeomorphisms, continuous units and composition, Hausdorff arrows and proper source-target map,
and give the objects their manifold diffeology. Every object `x` has an open neighbourhood `U` with
a continuous action of the isotropy group `Aut x`, which is finite by
`TauCeti.finite_hom_of_proper_source_target`, and a fully faithful functor
`Aut x ⋉ U ⥤ C` that is the inclusion on objects, such that the map `U / Aut x → C / ≅` sending
the orbit of `y` to its isomorphism class is an induction and an open embedding. So the coarse
diffeology is glued from the quotient diffeologies of the finite isotropy charts `U / Aut x`. -/
theorem exists_isotropy_action_isInduction_of_proper_source_target [T2Space (Quiver.Total C)]
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2)
    (x : C) :
    ∃ (U : Set C) (_ : x ∈ U) (_ : MulAction (Aut x) U) (F : ActionCategory (Aut x) U ⥤ C)
      (φ : orbitRel.Quotient (Aut x) U → Quotient (isIsomorphicSetoid C)),
      IsOpen U ∧ (∀ g : Aut x, Continuous fun y : U ↦ g • y) ∧
      (∀ a, F.obj a = (a.back : C)) ∧ F.Full ∧ F.Faithful ∧
      (∀ y, φ (Quotient.mk _ y) = Quotient.mk (isIsomorphicSetoid C) (y : C)) ∧
      IsInduction φ ∧ IsOpenEmbedding φ := by
  obtain ⟨U, hxU, _, F, hU, hact, hF, hfull, hfaith, -, -⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs.isLocalHomeomorph ht.isLocalHomeomorph
      hu hc x
  -- Since `F` is full and the inclusion on objects, orbits in `U` are isomorphism classes in `C`.
  have hback (y : U) : (ActionCategory.objEquiv (Aut x) U y).back = y :=
    (ActionCategory.objEquiv (Aut x) U).left_inv y
  have hr (y y' : U) : orbitRel (Aut x) U y y' ↔ Nonempty ((y : C) ⟶ y') := by
    rw [ActionCategory.orbitRel_iff_isIsomorphic_obj_of_full F, hF, hF, hback, hback,
      Groupoid.isIsomorphic_iff_nonempty_hom]
  let φ : orbitRel.Quotient (Aut x) U → Quotient (isIsomorphicSetoid C) :=
    Quotient.map Subtype.val fun y y' h ↦ Groupoid.isIsomorphic_iff_nonempty_hom.mpr
      ((hr y y').mp h)
  have hφ (y : U) : φ (Quotient.mk _ y) = Quotient.mk (isIsomorphicSetoid C) (y : C) := rfl
  refine ⟨U, hxU, inferInstance, F, φ, hU, hact, hF, hfull, hfaith, hφ,
    isInduction_of_mk_eq_isomorphismClassesMk
      ((_root_.Diffeology.IsDTopologyCompatible.dTop_eq C).symm ▸ hU)
      (fun _ _ f _ ↦ exists_transport hs ht.contMDiff f) (fun y y' ↦ (hr y y').mpr) hφ,
    isOpenEmbedding_of_mk_eq_isomorphismClassesMk hU hs.contMDiff.continuous ht.isOpenMap
      (fun y y' ↦ (hr y y').mpr) hφ⟩

end Manifold

end TauCeti.Diffeology
