/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient
public import TauCeti.Topology.CategoryTheory.Etale
public import TauCeti.Topology.CategoryTheory.Functor.IsomorphismClasses
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic

/-!
# The ineffective kernel and effective quotient of an étale groupoid

Let `C` be a topological groupoid whose source is a local homeomorphism. An arrow `a` from `x`
induces a germ at `x` of a local homeomorphism of objects: follow a local section of the source
through `a`, then take the target. The arrow is *ineffective* when this germ is the identity. In
terms of arrows alone, this means that source and target agree on a neighbourhood of `a`, and
`TauCeti.ineffectiveArrows C` is the interior of the set of arrows with equal endpoints
(`TauCeti.mem_ineffectiveArrows_iff_eventually_right_eq` compares the two descriptions).

The ineffective arrows contain the identities and are closed under inversion, composition and
conjugation by arbitrary arrows. Closure under composition and conjugation holds because
composition is open when the source is open (`TauCeti.eventually_exists_comp_eq`). Consequently
the ineffective automorphisms of an object `x` form a normal subgroup
`TauCeti.ineffectiveKernel hs x` of `Aut x`, the ineffective kernel, and an isomorphism `x ≅ y`
carries the ineffective kernel at `x` onto the one at `y`. In particular its order only depends
on the isomorphism class of `x`. When the source-target map is also proper, the automorphism
groups are finite (`TauCeti.finite_aut_of_proper_source_target`), hence so are the ineffective
kernels (`TauCeti.finite_ineffectiveKernel`).

Two parallel arrows are related by the germ relation `TauCeti.germRel C` when they induce the same
germ, that is, when one followed by the inverse of the other is ineffective. This is a congruence,
and the quotient groupoid `TauCeti.EffectiveQuotient C` is the effective quotient. Its objects are
those of `C` (`TauCeti.EffectiveQuotient.objEquiv`), with the same topology
(`TauCeti.EffectiveQuotient.objHomeomorph`), and it has the same isomorphism classes, so effective
reduction does not change the coarse space. Its isotropy group at `x` is `Aut x` divided by the
ineffective kernel. Ineffective isotropy is retained by `C` itself: distinct arrows inducing the
same germ remain distinct there. The arrow topology of the effective quotient is not constructed
in this file.

For the action groupoid of a discrete group acting on a space, these notions are the germ kernel
`TauCeti.MulAction.germKernel` of the action and the effective quotient
`TauCeti.ActionGroupoid.Effective` (see `TauCeti.germRel_actionCategory`).

## Main declarations

* `TauCeti.ineffectiveArrows C`: the arrows near which source and target agree.
* `TauCeti.ineffectiveKernel hs x`: the normal subgroup of ineffective automorphisms of `x`.
* `TauCeti.map_autMulEquivOfIso_ineffectiveKernel`: isomorphisms transport ineffective kernels.
* `TauCeti.EffectiveQuotient C`: the quotient of `C` by the germ relation `TauCeti.germRel C`,
  with its projection `TauCeti.toEffectiveQuotient C`. Both are exposed definitions unfolding to
  `CategoryTheory.Quotient (germRel C)` and its projection, so the universal property is
  `CategoryTheory.Quotient.lift (germRel C)` with `CategoryTheory.Quotient.lift_spec` and
  `CategoryTheory.Quotient.lift_unique`.
* `TauCeti.toEffectiveQuotient_map_eq_iff`: two parallel arrows have the same image exactly when
  they induce the same germ.
* `TauCeti.quotientIneffectiveKernelMulEquivAut`: the isotropy of the effective quotient at `x` is
  `Aut x` divided by the ineffective kernel.
* `TauCeti.EffectiveQuotient.isomorphismClassesHomeomorph`: the coarse spaces of `C` and of its
  effective quotient are homeomorphic.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1, for ineffective orbifolds and
  their effective reductions.
-/

public section

open CategoryTheory Filter Set Topology

namespace TauCeti

section Quiver

variable {C : Type*} [Quiver C] [TopologicalSpace (Quiver.Total C)]

variable (C) in
/-- The ineffective arrows of a quiver whose total arrows carry a topology: the arrows near which
source and target agree. When the source is a local homeomorphism, these are the arrows inducing
the identity germ on objects (`TauCeti.mem_ineffectiveArrows_iff_eventually_right_eq`). -/
def ineffectiveArrows : Set (Quiver.Total C) :=
  interior {a | a.left = a.right}

/-- An arrow is ineffective exactly when source and target agree near it. -/
theorem mem_ineffectiveArrows_iff {a : Quiver.Total C} :
    a ∈ ineffectiveArrows C ↔ ∀ᶠ b in 𝓝 a, b.left = b.right :=
  mem_interior_iff_mem_nhds

theorem isOpen_ineffectiveArrows : IsOpen (ineffectiveArrows C) :=
  isOpen_interior

/-- An ineffective arrow is an arrow from an object to itself. -/
theorem left_eq_right_of_mem_ineffectiveArrows {a : Quiver.Total C}
    (ha : a ∈ ineffectiveArrows C) : a.left = a.right :=
  interior_subset ha

/-- **Ineffective arrows induce the identity germ.** Let the source be a local homeomorphism and
let `σ` be a local section of the source through `a`, continuous at the source of `a`. Then `a` is
ineffective exactly when `σ` followed by the target, a representative of the germ of the map of
objects induced by `a`, is the identity near the source of `a`. -/
theorem mem_ineffectiveArrows_iff_eventually_right_eq [TopologicalSpace C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) {a : Quiver.Total C}
    {σ : C → Quiver.Total C} (hσ : ContinuousAt σ a.left) (hσa : σ a.left = a)
    (hσl : ∀ᶠ y in 𝓝 a.left, (σ y).left = y) :
    a ∈ ineffectiveArrows C ↔ ∀ᶠ y in 𝓝 a.left, (σ y).right = y := by
  have hσt : Tendsto σ (𝓝 a.left) (𝓝 a) := by
    have := hσ.tendsto
    rwa [hσa] at this
  rw [mem_ineffectiveArrows_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [hσt.eventually h, hσl] with y hy hyl
    rw [← hy, hyl]
  · -- Near `a` the source is injective, so every arrow `b` near `a` is `σ` of its source.
    obtain ⟨U, hU, hinj⟩ := isLocallyInjective_iff_nhds.mp hs.isLocallyInjective a
    have hl : Tendsto Quiver.Total.left (𝓝 a) (𝓝 a.left) := hs.continuous.continuousAt.tendsto
    filter_upwards [hU, hl.eventually (hσt.eventually hU), hl.eventually hσl, hl.eventually h]
      with b hb hσb hσbl hσbr
    have hσbb : σ b.left = b := hinj hσb hb hσbl
    calc b.left = (σ b.left).right := hσbr.symm
      _ = b.right := by rw [hσbb]

end Quiver

section Groupoid

variable {C : Type*} [Groupoid C]

variable [TopologicalSpace (Quiver.Total C)]

variable (C) in
/-- The germ relation on parallel arrows of a groupoid whose total arrows carry a topology: `f`
and `f'` are related when `f` followed by the inverse of `f'` is ineffective. In an étale groupoid
this means that `f` and `f'` induce the same germ at their source. -/
def germRel : HomRel C :=
  fun x _ f f' ↦ (⟨x, x, f ≫ inv f'⟩ : Quiver.Total C) ∈ ineffectiveArrows C

@[simp]
theorem germRel_iff {x y : C} {f f' : x ⟶ y} :
    germRel C f f' ↔ (⟨x, x, f ≫ inv f'⟩ : Quiver.Total C) ∈ ineffectiveArrows C :=
  Iff.rfl

variable (C) in
/-- The effective quotient of a groupoid whose total arrows carry a topology: the quotient groupoid
by the germ relation. For an étale groupoid, two parallel arrows have the same image exactly when
they induce the same germ (`TauCeti.toEffectiveQuotient_map_eq_iff`). -/
@[expose] def EffectiveQuotient : Type _ :=
  CategoryTheory.Quotient (germRel C)

instance : Groupoid (EffectiveQuotient C) :=
  inferInstanceAs (Groupoid (CategoryTheory.Quotient (germRel C)))

variable (C) in
/-- The projection from a groupoid to its effective quotient. It is the identity on objects and
sends each arrow to its class under the germ relation. -/
@[expose] def toEffectiveQuotient : C ⥤ EffectiveQuotient C :=
  CategoryTheory.Quotient.functor (germRel C)

instance : (toEffectiveQuotient C).Full :=
  inferInstanceAs (CategoryTheory.Quotient.functor (germRel C)).Full

instance : (toEffectiveQuotient C).EssSurj :=
  inferInstanceAs (CategoryTheory.Quotient.functor (germRel C)).EssSurj

/-- The projection to the effective quotient reflects isomorphisms, as does any functor out of a
groupoid. -/
instance : (toEffectiveQuotient C).ReflectsIsomorphisms :=
  ⟨fun _ _ ↦ inferInstance⟩

variable (C) in
/-- The objects of the effective quotient are the objects of the groupoid. -/
def EffectiveQuotient.objEquiv : C ≃ EffectiveQuotient C :=
  (CategoryTheory.Quotient.equiv (germRel C)).symm

@[simp]
theorem EffectiveQuotient.objEquiv_apply (x : C) :
    EffectiveQuotient.objEquiv C x = (toEffectiveQuotient C).obj x :=
  (rfl)

@[simp]
theorem EffectiveQuotient.objEquiv_symm_toEffectiveQuotient_obj (x : C) :
    (EffectiveQuotient.objEquiv C).symm ((toEffectiveQuotient C).obj x) = x :=
  (rfl)

@[simp]
theorem toEffectiveQuotient_obj_objEquiv_symm (x : EffectiveQuotient C) :
    (toEffectiveQuotient C).obj ((EffectiveQuotient.objEquiv C).symm x) = x :=
  (rfl)

/-- Every automorphism in the effective quotient is the image of an automorphism. -/
theorem mapAut_toEffectiveQuotient_surjective (x : C) :
    Function.Surjective ((toEffectiveQuotient C).mapAut x) := by
  intro e
  obtain ⟨f, hf⟩ := (toEffectiveQuotient C).map_surjective e.asIso.hom
  exact ⟨.of (Groupoid.isoEquivHom x x |>.symm f), Aut.ext (Iso.ext (by simpa using hf))⟩

/-- Two objects are isomorphic in the effective quotient exactly when they are isomorphic. -/
theorem isIsomorphic_toEffectiveQuotient_obj_iff {x y : C} :
    IsIsomorphic ((toEffectiveQuotient C).obj x) ((toEffectiveQuotient C).obj y) ↔
      IsIsomorphic x y := by
  rw [Groupoid.isIsomorphic_iff_nonempty_hom, Groupoid.isIsomorphic_iff_nonempty_hom]
  exact ⟨fun ⟨f⟩ ↦ ⟨(toEffectiveQuotient C).preimage f⟩, fun ⟨f⟩ ↦ ⟨(toEffectiveQuotient C).map f⟩⟩

/-- The projection to the effective quotient induces a bijection on isomorphism classes. -/
theorem isomorphismClasses_map_toEffectiveQuotient_bijective :
    Function.Bijective (α := _root_.Quotient (isIsomorphicSetoid C))
      (β := _root_.Quotient (isIsomorphicSetoid (EffectiveQuotient C)))
      (isomorphismClasses.map (toEffectiveQuotient C).toCatHom) := by
  refine ⟨(toEffectiveQuotient C).isomorphismClasses_map_injective, fun q ↦ ?_⟩
  induction q using _root_.Quotient.inductionOn with
  | h x => exact ⟨_root_.Quotient.mk _ ((EffectiveQuotient.objEquiv C).symm x), rfl⟩

variable [TopologicalSpace C]

variable (C) in
/-- The objects of the effective quotient carry the topology of the objects of the groupoid. -/
instance : TopologicalSpace (EffectiveQuotient C) :=
  TopologicalSpace.induced (CategoryTheory.Quotient.equiv (germRel C)) ‹_›

variable (C) in
/-- The objects of the effective quotient are homeomorphic to the objects of the groupoid. -/
def EffectiveQuotient.objHomeomorph : C ≃ₜ EffectiveQuotient C :=
  (Equiv.toHomeomorphOfIsInducing (EffectiveQuotient.objEquiv C).symm ⟨rfl⟩).symm

@[simp]
theorem EffectiveQuotient.objHomeomorph_apply (x : C) :
    EffectiveQuotient.objHomeomorph C x = (toEffectiveQuotient C).obj x :=
  (rfl)

@[simp]
theorem EffectiveQuotient.objHomeomorph_symm_apply (x : EffectiveQuotient C) :
    (EffectiveQuotient.objHomeomorph C).symm x = (EffectiveQuotient.objEquiv C).symm x :=
  (rfl)

/-- The projection to the effective quotient is a homeomorphism on objects. -/
theorem isHomeomorph_toEffectiveQuotient_obj : IsHomeomorph (toEffectiveQuotient C).obj :=
  (EffectiveQuotient.objHomeomorph C).isHomeomorph

variable (C) in
/-- Effective reduction does not change the coarse space: the projection to the effective quotient
induces a homeomorphism between the spaces of isomorphism classes. -/
noncomputable def EffectiveQuotient.isomorphismClassesHomeomorph :
    _root_.Quotient (isIsomorphicSetoid C) ≃ₜ
      _root_.Quotient (isIsomorphicSetoid (EffectiveQuotient C)) :=
  (toEffectiveQuotient C).isomorphismClassesHomeomorph
    isHomeomorph_toEffectiveQuotient_obj.isQuotientMap

@[simp]
theorem EffectiveQuotient.isomorphismClassesHomeomorph_apply_mk (x : C) :
    EffectiveQuotient.isomorphismClassesHomeomorph C (_root_.Quotient.mk _ x) =
      _root_.Quotient.mk _ ((toEffectiveQuotient C).obj x) :=
  (toEffectiveQuotient C).isomorphismClassesHomeomorph_apply_mk _ x

variable [IsTopologicalGroupoid C]

variable (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

include hs in
/-- In an étale groupoid the identity arrows are ineffective. -/
theorem id_mem_ineffectiveArrows (x : C) :
    (⟨x, x, 𝟙 x⟩ : Quiver.Total C) ∈ ineffectiveArrows C :=
  interior_maximal (by rintro _ ⟨y, rfl⟩; rfl)
    (isOpen_range_unit IsTopologicalGroupoid.continuous_unit hs) ⟨x, rfl⟩

/-- The inverse of an arrow is ineffective exactly when the arrow is. -/
theorem inv_mem_ineffectiveArrows_iff {a : Quiver.Total C} :
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C) ∈ ineffectiveArrows C ↔
      a ∈ ineffectiveArrows C := by
  rw [mem_ineffectiveArrows_iff, mem_ineffectiveArrows_iff,
    ← IsTopologicalGroupoid.inverseHomeomorph_apply,
    ← (IsTopologicalGroupoid.inverseHomeomorph C).map_nhds_eq, eventually_map]
  simp only [IsTopologicalGroupoid.inverseHomeomorph_apply]
  exact eventually_congr (.of_forall fun _ ↦ eq_comm)

/-- When the source is open, the composite of two ineffective arrows is ineffective. -/
theorem comp_mem_ineffectiveArrows (ho : IsOpenMap (Quiver.Total.left : Quiver.Total C → C))
    {a b : Quiver.Total C} (ha : a ∈ ineffectiveArrows C) (hb : b ∈ ineffectiveArrows C)
    (h : a.right = b.left) : a.comp b h ∈ ineffectiveArrows C := by
  rw [mem_ineffectiveArrows_iff] at ha hb ⊢
  filter_upwards [eventually_exists_comp_eq ho h (A := {a | a.left = a.right})
    (B := {a | a.left = a.right}) ha hb] with c ⟨a', ha', b', hb', h', hc⟩
  rw [← hc, Quiver.Total.comp_left, Quiver.Total.comp_right]
  exact (ha' : a'.left = a'.right).trans (h'.trans hb')

include hs in
/-- In an étale groupoid, conjugating an ineffective automorphism of `y` by an arrow `f : x ⟶ y`
gives an ineffective automorphism of `x`. -/
private theorem conj_mem_ineffectiveArrows {x y : C} (f : x ⟶ y) {g : y ⟶ y}
    (hg : (⟨y, y, g⟩ : Quiver.Total C) ∈ ineffectiveArrows C) :
    (⟨x, x, f ≫ g ≫ inv f⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by
  have ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) :=
    (IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs
  -- The target is injective on a neighbourhood `W` of `f`.
  obtain ⟨W, hW, hinj⟩ := isLocallyInjective_iff_nhds.mp ht.isLocallyInjective ⟨x, y, f⟩
  have hW' : {k : Quiver.Total C | (⟨k.right, k.left, inv k.hom⟩ : Quiver.Total C) ∈ W} ∈
      𝓝 (⟨y, x, inv f⟩ : Quiver.Total C) :=
    IsTopologicalGroupoid.continuous_inverse.continuousAt.preimage_mem_nhds (by simpa using hW)
  rw [mem_ineffectiveArrows_iff] at hg ⊢
  have hN := eventually_exists_comp_eq hs.isOpenMap (a := ⟨y, y, g⟩) (b := ⟨y, x, inv f⟩) rfl hg
    hW'
  rw [Quiver.Total.mk_comp_mk] at hN
  have key := eventually_exists_comp_eq hs.isOpenMap (a := ⟨x, y, f⟩) (b := ⟨y, x, g ≫ inv f⟩)
    rfl hW hN
  rw [Quiver.Total.mk_comp_mk] at key
  -- Near `f ≫ g ≫ f⁻¹`, an arrow `c` is `f' ≫ g' ≫ k` with `f'` and `k⁻¹` in `W` and `g'` with
  -- equal endpoints. Then `k⁻¹` and `f'` have the same target, so they agree.
  filter_upwards [key] with c ⟨f', hf', d, ⟨g', hg', k, hk, hgk, hd⟩, hfd, hc⟩
  have hkf : (⟨k.right, k.left, inv k.hom⟩ : Quiver.Total C) = f' := by
    refine hinj hk hf' ?_
    calc k.left = g'.right := hgk.symm
      _ = g'.left := (hg' : g'.left = g'.right).symm
      _ = d.left := by rw [← hd, Quiver.Total.comp_left]
      _ = f'.right := hfd.symm
  calc c.left = f'.left := by rw [← hc, Quiver.Total.comp_left]
    _ = k.right := (congrArg Quiver.Total.left hkf).symm
    _ = d.right := by rw [← hd, Quiver.Total.comp_right]
    _ = c.right := by rw [← hc, Quiver.Total.comp_right]

include hs in
/-- In an étale groupoid, conjugation by an arrow `f : x ⟶ y` identifies the ineffective
automorphisms of `y` with those of `x`. -/
theorem conj_mem_ineffectiveArrows_iff {x y : C} (f : x ⟶ y) {g : y ⟶ y} :
    (⟨x, x, f ≫ g ≫ inv f⟩ : Quiver.Total C) ∈ ineffectiveArrows C ↔
      (⟨y, y, g⟩ : Quiver.Total C) ∈ ineffectiveArrows C :=
  ⟨fun h ↦ by simpa using conj_mem_ineffectiveArrows hs (inv f) h,
    conj_mem_ineffectiveArrows hs f⟩

include hs in
/-- The ineffective kernel at an object `x` of an étale groupoid: the automorphisms of `x`
inducing the identity germ at `x`. It is a normal subgroup of `Aut x`. -/
def ineffectiveKernel (x : C) : Subgroup (Aut x) where
  carrier := {g | (⟨x, x, g.asIso.hom⟩ : Quiver.Total C) ∈ ineffectiveArrows C}
  one_mem' := by simpa using id_mem_ineffectiveArrows hs x
  mul_mem' {g h} hg hh := by
    simpa using comp_mem_ineffectiveArrows hs.isOpenMap hh hg rfl
  inv_mem' {g} hg := by
    simpa using inv_mem_ineffectiveArrows_iff.mpr hg

@[simp]
theorem mem_ineffectiveKernel {x : C} {g : Aut x} :
    g ∈ ineffectiveKernel hs x ↔ (⟨x, x, g.asIso.hom⟩ : Quiver.Total C) ∈ ineffectiveArrows C :=
  Iff.rfl

instance ineffectiveKernel_normal (x : C) : (ineffectiveKernel hs x).Normal where
  conj_mem n hn g := by
    rw [mem_ineffectiveKernel] at hn ⊢
    simpa using (conj_mem_ineffectiveArrows_iff hs g.asIso.inv).mpr hn

/-- An isomorphism `e : x ≅ y` carries the ineffective kernel at `x` onto the one at `y`, by
conjugation. -/
theorem autMulEquivOfIso_mem_ineffectiveKernel_iff {x y : C} (e : x ≅ y) {g : Aut x} :
    Aut.autMulEquivOfIso e g ∈ ineffectiveKernel hs y ↔ g ∈ ineffectiveKernel hs x := by
  simpa using conj_mem_ineffectiveArrows_iff hs e.inv (g := g.asIso.hom)

/-- An isomorphism `e : x ≅ y` maps the ineffective kernel at `x` onto the one at `y`. -/
theorem map_autMulEquivOfIso_ineffectiveKernel {x y : C} (e : x ≅ y) :
    (ineffectiveKernel hs x).map (Aut.autMulEquivOfIso e).toMonoidHom = ineffectiveKernel hs y := by
  ext g
  rw [Subgroup.mem_map_equiv, ← autMulEquivOfIso_mem_ineffectiveKernel_iff hs e,
    MulEquiv.apply_symm_apply]

/-- When the source-target map is also proper, the ineffective kernels are finite. -/
theorem finite_ineffectiveKernel (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (x : C) : Finite (ineffectiveKernel hs x) :=
  have := finite_aut_of_proper_source_target hp hs x
  inferInstance

/-- The order of the ineffective kernel only depends on the isomorphism class of the object. -/
theorem card_ineffectiveKernel_eq_of_iso {x y : C} (e : x ≅ y) :
    Nat.card (ineffectiveKernel hs x) = Nat.card (ineffectiveKernel hs y) := by
  rw [← map_autMulEquivOfIso_ineffectiveKernel hs e]
  exact (Subgroup.card_map_of_injective (Aut.autMulEquivOfIso e).injective).symm

include hs in
/-- In an étale groupoid the germ relation is a congruence. -/
theorem congruence_germRel : Congruence (germRel C) where
  equivalence :=
    { refl _ := by simpa using id_mem_ineffectiveArrows hs _
      symm h := by simpa using inv_mem_ineffectiveArrows_iff.mpr h
      trans h h' := by
        simpa using comp_mem_ineffectiveArrows hs.isOpenMap h h' rfl }
  comp_left f g g' h := by
    simpa using (conj_mem_ineffectiveArrows_iff hs f).mpr h
  comp_right g h := by
    simpa using h

include hs in
/-- In an étale groupoid, two parallel arrows have the same image in the effective quotient
exactly when they induce the same germ. -/
theorem toEffectiveQuotient_map_eq_iff {x y : C} {f f' : x ⟶ y} :
    (toEffectiveQuotient C).map f = (toEffectiveQuotient C).map f' ↔
      (⟨x, x, f ≫ inv f'⟩ : Quiver.Total C) ∈ ineffectiveArrows C :=
  haveI := congruence_germRel hs
  CategoryTheory.Quotient.functor_map_eq_iff _ f f'

include hs in
/-- In an étale groupoid, an automorphism becomes trivial in the effective quotient exactly when
it is ineffective. -/
theorem toEffectiveQuotient_map_eq_id_iff {x : C} {f : x ⟶ x} :
    (toEffectiveQuotient C).map f = 𝟙 _ ↔ (⟨x, x, f⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by
  rw [← (toEffectiveQuotient C).map_id, toEffectiveQuotient_map_eq_iff hs, IsIso.inv_id,
    Category.comp_id]

/-- The kernel of the passage from the isotropy of an étale groupoid at `x` to the isotropy of its
effective quotient is the ineffective kernel. -/
theorem ker_mapAut_toEffectiveQuotient (x : C) :
    ((toEffectiveQuotient C).mapAut x).ker = ineffectiveKernel hs x := by
  ext g
  rw [MonoidHom.mem_ker, mem_ineffectiveKernel, ← toEffectiveQuotient_map_eq_id_iff hs,
    Aut.ext_iff, Iso.ext_iff]
  simp

/-- The isotropy group of the effective quotient of an étale groupoid at `x` is `Aut x` divided by
the ineffective kernel: effective reduction keeps exactly the effective part of the isotropy. -/
noncomputable def quotientIneffectiveKernelMulEquivAut (x : C) :
    Aut x ⧸ ineffectiveKernel hs x ≃* Aut ((toEffectiveQuotient C).obj x) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mapAut_toEffectiveQuotient hs x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (mapAut_toEffectiveQuotient_surjective x))

@[simp]
theorem quotientIneffectiveKernelMulEquivAut_mk (x : C) (g : Aut x) :
    quotientIneffectiveKernelMulEquivAut hs x (QuotientGroup.mk g) =
      (toEffectiveQuotient C).mapAut x g :=
  (rfl)

/-- The projection to the effective quotient of an étale groupoid is faithful exactly when every
ineffective kernel is trivial. -/
theorem toEffectiveQuotient_faithful_iff :
    (toEffectiveQuotient C).Faithful ↔ ∀ x : C, ineffectiveKernel hs x = ⊥ := by
  refine ⟨fun hF x ↦ ?_, fun h ↦ ⟨fun {x _} f f' hf ↦ ?_⟩⟩
  · rw [← ker_mapAut_toEffectiveQuotient hs, MonoidHom.ker_eq_bot_iff]
    intro g g' hg
    exact Aut.ext (Iso.ext ((toEffectiveQuotient C).map_injective
      (congrArg (fun e : Aut _ ↦ e.asIso.hom) hg)))
  · rw [toEffectiveQuotient_map_eq_iff hs] at hf
    have : (.of (Groupoid.isoEquivHom x x |>.symm (f ≫ inv f')) : Aut x) ∈
        ineffectiveKernel hs x := by
      simpa using hf
    rw [h x, Subgroup.mem_bot, Aut.ext_iff, Iso.ext_iff] at this
    simpa using this

end Groupoid

end TauCeti
