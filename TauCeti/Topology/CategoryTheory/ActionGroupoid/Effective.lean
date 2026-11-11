/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Effective
public import TauCeti.Topology.Algebra.GroupAction.GermKernel
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective

/-!
# The effective quotient of an action groupoid

Let a group `G` act on a topological space `X` by continuous maps. An arrow `x ⟶ g • x` of the
action groupoid `G ⋉ X` (Mathlib's `CategoryTheory.ActionCategory G X`) induces the germ at `x`
of the map `g • ·`. Its *ineffective* arrows are the automorphisms of `x` inducing the germ of
the identity: these are the labels in the germ kernel `TauCeti.MulAction.germKernel G x`. The
effective quotient `TauCeti.ActionGroupoid.Effective G X` identifies two arrows with the same
source and target when they induce the same germ at their source. It is the quotient groupoid
(Mathlib's `CategoryTheory.Quotient`) by the germ relation `TauCeti.ActionGroupoid.germRel`,
which is a congruence because each translation `g • ·` is continuous. Its arrows are therefore
germs of the action, and its isotropy at `x` is the stabilizer of `x` divided by the germ kernel
at `x`.

The quotient keeps the objects, so it has the same isomorphism classes, namely the orbits of the
action: effective reduction does not change the coarse space. It does change the isotropy, and
the projection `TauCeti.ActionGroupoid.toEffective` is faithful exactly when every germ kernel is
trivial. Unlike the faithful quotient action of `G ⧸ ker` (`TauCeti.effectiveActionFunctor`),
the effective quotient discards elements acting trivially near a point even when they act
nontrivially elsewhere. The two agree when every germ kernel is the kernel of the action, as
happens for actions by `C¹` maps with torsion stabilizers on a preconnected Hausdorff manifold
without boundary (`TauCeti.germKernel_eq_ker`).

For a discrete group, `G ⋉ X` is an étale topological groupoid, and these are its ineffective
arrows and effective quotient in the sense of `TauCeti.ineffectiveArrows` and
`TauCeti.EffectiveQuotient`: an arrow is ineffective exactly when its label lies in the germ kernel
at its source, and the two germ relations agree (`TauCeti.germRel_actionCategory`).

## Main declarations

* `TauCeti.ActionGroupoid.Effective G X`: the effective quotient of `G ⋉ X`, with its projection
  `TauCeti.ActionGroupoid.toEffective G X` and its universal property
  `TauCeti.ActionGroupoid.Effective.lift`.
* `TauCeti.ActionGroupoid.toEffective_map_eq_iff`: two arrows have the same image exactly when
  their labels agree near the source.
* `TauCeti.ActionGroupoid.toEffective_map_eq_id_iff`: an automorphism of `x` becomes trivial
  exactly when its label is in the germ kernel at `x`.
* `TauCeti.ActionGroupoid.Effective.stabilizerQuotientMulEquivAut`: the isotropy group of the
  effective quotient at `x` is the stabilizer of `x` divided by the germ kernel.
* `TauCeti.ActionGroupoid.Effective.orbitQuotientEquivIsomorphismClasses`: the isomorphism
  classes of the effective quotient are the orbits of the action.
* `TauCeti.ActionGroupoid.toEffective_faithful_iff`: the projection is faithful exactly when all
  germ kernels are trivial.
* `TauCeti.germRel_actionCategory`: for a discrete group, the germ relation of the étale groupoid
  `G ⋉ X` is the germ relation of the action.
* `TauCeti.ActionGroupoid.Effective.toQuotientKer`: if every germ kernel is the kernel of the
  action, this equivalence identifies the effective quotient with the action groupoid of the
  faithful quotient action.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1, for ineffective
  orbifolds and their effective reductions.
-/

public section

open CategoryTheory Filter MulAction Topology TauCeti.MulAction

namespace TauCeti.ActionGroupoid

variable (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]

/-- Two arrows of the action groupoid `G ⋉ X` with the same source and target are related by the
germ relation when their labels act in the same way near the source. -/
def germRel : HomRel (ActionCategory G X) :=
  fun a _ f f' ↦ ∀ᶠ y in 𝓝 a.back, (f.hom : G) • y = (f'.hom : G) • y

variable {G X}

/-- The defining property of the germ relation. -/
theorem germRel_iff {a b : ActionCategory G X} {f f' : a ⟶ b} :
    germRel G X f f' ↔ ∀ᶠ y in 𝓝 a.back, (f.hom : G) • y = (f'.hom : G) • y :=
  Iff.rfl

/-- Two arrows are related by the germ relation exactly when they differ by an element of the
germ kernel at their source. -/
theorem germRel_iff_mem_germKernel {a b : ActionCategory G X} {f f' : a ⟶ b} :
    germRel G X f f' ↔ (f.hom : G)⁻¹ * f'.hom ∈ germKernel G a.back := by
  rw [germRel_iff]
  refine (eventually_congr (.of_forall fun y ↦ ?_)).trans mem_germKernel.symm
  rw [mul_smul, inv_smul_eq_iff, eq_comm]

variable (G X)

/-- The effective quotient of the action groupoid `G ⋉ X`: the quotient groupoid by the germ
relation. For an action by continuous maps the germ relation is already a congruence, so two
arrows with the same source and target are identified exactly when they induce the same germ at
the source (`TauCeti.ActionGroupoid.toEffective_map_eq_iff`), and the arrows of the quotient are
the germs of the action. -/
@[expose] def Effective : Type _ :=
  CategoryTheory.Quotient (germRel G X)

instance : Groupoid (Effective G X) :=
  inferInstanceAs (Groupoid (CategoryTheory.Quotient (germRel G X)))

/-- The projection from the action groupoid to its effective quotient. It is the identity on
objects and sends each arrow to its germ. -/
@[expose] def toEffective : ActionCategory G X ⥤ Effective G X :=
  CategoryTheory.Quotient.functor (germRel G X)

instance : (toEffective G X).Full :=
  inferInstanceAs (CategoryTheory.Quotient.functor (germRel G X)).Full

instance : (toEffective G X).EssSurj :=
  inferInstanceAs (CategoryTheory.Quotient.functor (germRel G X)).EssSurj

/-- The points of `X` are the objects of the effective quotient of `G ⋉ X`. -/
@[expose] def Effective.objEquiv : X ≃ Effective G X :=
  (ActionCategory.objEquiv G X).trans (CategoryTheory.Quotient.equiv (germRel G X)).symm

variable {G X}

@[simp]
theorem toEffective_obj_objEquiv (x : X) :
    (toEffective G X).obj (ActionCategory.objEquiv G X x) = Effective.objEquiv G X x :=
  (rfl)

@[simp]
theorem Effective.objEquiv_symm_toEffective_obj (a : ActionCategory G X) :
    (Effective.objEquiv G X).symm ((toEffective G X).obj a) = a.back :=
  (rfl)

section Lift

variable {D : Type*} [Category* D] (F : ActionCategory G X ⥤ D)
  (H : ∀ (a b : ActionCategory G X) (f f' : a ⟶ b), germRel G X f f' → F.map f = F.map f')

/-- The universal property of the effective quotient: a functor out of `G ⋉ X` sending arrows
with the same germ at their source to the same arrow factors through the effective quotient. -/
@[expose] def Effective.lift : Effective G X ⥤ D :=
  CategoryTheory.Quotient.lift (germRel G X) F H

@[simp]
theorem Effective.toEffective_comp_lift : toEffective G X ⋙ Effective.lift F H = F :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem Effective.lift_obj_toEffective_obj (a : ActionCategory G X) :
    (Effective.lift F H).obj ((toEffective G X).obj a) = F.obj a :=
  (rfl)

@[simp]
theorem Effective.lift_map_toEffective_map {a b : ActionCategory G X} (f : a ⟶ b) :
    (Effective.lift F H).map ((toEffective G X).map f) = F.map f :=
  (rfl)

/-- A functor out of the effective quotient that restricts to `F` along the projection is the
induced functor `TauCeti.ActionGroupoid.Effective.lift F H`. -/
theorem Effective.lift_unique (Φ : Effective G X ⥤ D) (hΦ : toEffective G X ⋙ Φ = F) :
    Φ = Effective.lift F H :=
  CategoryTheory.Quotient.lift_unique _ _ _ Φ hΦ

/-- Two functors out of the effective quotient are equal when they agree after the projection
from `G ⋉ X`. -/
theorem Effective.ext_functor {F₁ F₂ : Effective G X ⥤ D}
    (h : toEffective G X ⋙ F₁ = toEffective G X ⋙ F₂) : F₁ = F₂ :=
  CategoryTheory.Quotient.lift_unique' _ _ _ h

end Lift

/-- Two objects of the effective quotient are isomorphic exactly when the corresponding points lie
in the same orbit. -/
theorem Effective.isIsomorphic_objEquiv_iff {x y : X} :
    IsIsomorphic (Effective.objEquiv G X x) (Effective.objEquiv G X y) ↔ orbitRel G X x y := by
  rw [← ActionCategory.isIsomorphic_iff_orbitRel, Groupoid.isIsomorphic_iff_nonempty_hom,
    Groupoid.isIsomorphic_iff_nonempty_hom, ← toEffective_obj_objEquiv,
    ← toEffective_obj_objEquiv]
  exact ⟨fun ⟨f⟩ ↦ ⟨(toEffective G X).preimage f⟩, fun ⟨f⟩ ↦ ⟨(toEffective G X).map f⟩⟩

variable (G X) in
/-- Effective reduction does not change the coarse space: the isomorphism classes of the effective
quotient of `G ⋉ X` are the orbits of the action. -/
def Effective.orbitQuotientEquivIsomorphismClasses :
    orbitRel.Quotient G X ≃ _root_.Quotient (isIsomorphicSetoid (Effective G X)) :=
  _root_.Quotient.congr (Effective.objEquiv G X) fun _ _ ↦ isIsomorphic_objEquiv_iff.symm

@[simp]
theorem Effective.orbitQuotientEquivIsomorphismClasses_mk (x : X) :
    Effective.orbitQuotientEquivIsomorphismClasses G X (_root_.Quotient.mk _ x) =
      _root_.Quotient.mk _ (Effective.objEquiv G X x) :=
  (rfl)

variable (G) in
/-- The passage from the isotropy of `G ⋉ X` at `x` to the isotropy of its effective quotient:
an element of the stabilizer of `x` is sent to its germ at `x`. -/
def Effective.stabilizerToAut (x : X) : stabilizer G x →* Aut (Effective.objEquiv G X x) :=
  ((toEffective G X).mapAut (ActionCategory.objEquiv G X x)).comp
    (ActionCategory.stabilizerMulEquivAut G x).toMonoidHom

@[simp]
theorem Effective.stabilizerToAut_apply_asIso_hom (x : X) (g : stabilizer G x) :
    (Effective.stabilizerToAut G x g).asIso.hom =
      (toEffective G X).map (ActionCategory.stabilizerMulEquivAut G x g).asIso.hom :=
  (rfl)

/-- Every automorphism in the effective quotient is the germ of an element of the stabilizer. -/
theorem Effective.stabilizerToAut_surjective (x : X) :
    Function.Surjective (Effective.stabilizerToAut G x) := by
  intro e
  obtain ⟨f, hf⟩ := (toEffective G X).map_surjective e.asIso.hom
  refine ⟨⟨f.hom, ActionCategory.hom_smul f⟩, Aut.ext (Iso.ext ?_)⟩
  rw [stabilizerToAut_apply_asIso_hom, ← hf]
  exact congrArg (toEffective G X).map
    (Functor.Elements.hom_ext (ActionCategory.stabilizerMulEquivAut_apply_hom_hom x _))

section Faithful

variable {hker : ∀ x : X, germKernel G x ≤ (toPermHom G X).ker}

/-- If every germ kernel is the kernel of the action, that is, if every element acting as the
identity near some point acts trivially on all of `X`, the projection
`TauCeti.effectiveActionFunctor` onto the action groupoid of the faithful quotient action of
`G ⧸ ker` factors through the effective quotient, and this functor is an equivalence. -/
@[expose] def Effective.toQuotientKer (hker : ∀ x : X, germKernel G x ≤ (toPermHom G X).ker) :
    Effective G X ⥤ ActionCategory (G ⧸ (toPermHom G X).ker) X :=
  Effective.lift (effectiveActionFunctor G X) fun _ _ f f' h ↦ by
    apply Functor.Elements.hom_ext
    rw [effectiveActionFunctor_map_hom, effectiveActionFunctor_map_hom, QuotientGroup.eq]
    exact hker _ (germRel_iff_mem_germKernel.mp h)

@[simp]
theorem Effective.toQuotientKer_map_toEffective_map {a b : ActionCategory G X} (f : a ⟶ b) :
    (Effective.toQuotientKer hker).map ((toEffective G X).map f) =
      (effectiveActionFunctor G X).map f :=
  Effective.lift_map_toEffective_map _ _ f

@[simp]
theorem Effective.toQuotientKer_obj_objEquiv (x : X) :
    (Effective.toQuotientKer hker).obj (Effective.objEquiv G X x) =
      ActionCategory.objEquiv (G ⧸ (toPermHom G X).ker) X x :=
  effectiveActionFunctor_obj G X x

/-- The effective quotient followed by `TauCeti.ActionGroupoid.Effective.toQuotientKer` is the
projection to the faithful quotient action groupoid. -/
@[simp]
theorem Effective.toEffective_comp_toQuotientKer :
    toEffective G X ⋙ Effective.toQuotientKer hker = effectiveActionFunctor G X :=
  Effective.toEffective_comp_lift _ _

instance : (Effective.toQuotientKer hker).Full :=
  Functor.full_of_comp_essSurj _ (toEffective G X) fun _ _ φ ↦
    let ⟨f, hf⟩ := (effectiveActionFunctor G X).map_surjective φ
    ⟨(toEffective G X).map f, (Effective.toQuotientKer_map_toEffective_map f).trans hf⟩

instance : (Effective.toQuotientKer hker).EssSurj where
  mem_essImage y := ⟨Effective.objEquiv G X y.back,
    ⟨eqToIso ((effectiveActionFunctor_obj G X y.back).trans (ActionCategory.back_coe y))⟩⟩

instance : (Effective.toQuotientKer hker).Faithful :=
  Functor.faithful_of_comp_essSurj _ (toEffective G X) fun x _ φ ψ h ↦ by
    obtain ⟨f, rfl⟩ := (toEffective G X).map_surjective φ
    obtain ⟨f', rfl⟩ := (toEffective G X).map_surjective ψ
    have h' : (effectiveActionFunctor G X).map f = (effectiveActionFunctor G X).map f' :=
      (Effective.toQuotientKer_map_toEffective_map f).symm.trans
        (h.trans (Effective.toQuotientKer_map_toEffective_map f'))
    refine CategoryTheory.Quotient.sound _ (germRel_iff_mem_germKernel.mpr
      (ker_toPermHom_le_germKernel x.back (QuotientGroup.eq (s := (toPermHom G X).ker).mp ?_)))
    simpa only [effectiveActionFunctor_map_hom] using congrArg (fun f ↦ f.hom) h'

instance : (Effective.toQuotientKer hker).IsEquivalence where

end Faithful

section Etale

variable [TopologicalSpace G] [DiscreteTopology G]

/-- For a discrete group, an arrow of the étale groupoid `G ⋉ X` is ineffective exactly when its
label lies in the germ kernel at its source. -/
theorem _root_.TauCeti.mem_ineffectiveArrows_actionCategory_iff
    {a : Quiver.Total (ActionCategory G X)} :
    a ∈ ineffectiveArrows (ActionCategory G X) ↔ (a.hom.hom : G) ∈ germKernel G a.left.back := by
  -- The arrows with the label of `a` form a local section of the source through `a`.
  rw [mem_ineffectiveArrows_iff_eventually_right_eq (isLocalHomeomorph_source G X)
    (σ := (sourceChart G X a.hom.hom).symm)
    ((sourceChart G X a.hom.hom).continuousAt_symm (by simp))
    (by simpa using (sourceChart G X a.hom.hom).left_inv (x := a) (by simp))
    (.of_forall fun y ↦ by
      rw [sourceChart_symm_apply, arrowHomeomorph_symm_apply,
        ActionCategory.totalEquiv_symm_apply_left]
      exact ActionCategory.back_coe y)]
  refine Iff.trans ?_ mem_germKernel.symm
  rw [← objectHomeomorph_apply, ← (objectHomeomorph G X).map_nhds_eq, eventually_map]
  refine eventually_congr (.of_forall fun y ↦ ?_)
  rw [sourceChart_symm_apply, arrowHomeomorph_symm_apply,
    ActionCategory.totalEquiv_symm_apply_right, objectHomeomorph_apply]
  -- The inverse of `objEquiv` is `back`.
  exact (ActionCategory.objEquiv G X).eq_symm_apply.symm

/-- For a discrete group, the germ relation of the étale groupoid `G ⋉ X` is the germ relation of
the action. Hence `TauCeti.EffectiveQuotient (ActionCategory G X)` is
`TauCeti.ActionGroupoid.Effective G X`. -/
theorem _root_.TauCeti.germRel_actionCategory :
    _root_.TauCeti.germRel (ActionCategory G X) = germRel G X := by
  funext a b f f'
  rw [eq_iff_iff, _root_.TauCeti.germRel_iff, mem_ineffectiveArrows_actionCategory_iff,
    germRel_iff_mem_germKernel]
  simp only [ActionCategory.comp_hom, ActionCategory.inv_hom]
  rw [← inv_mem_iff, mul_inv_rev, inv_inv]

end Etale

variable [ContinuousConstSMul G X]

/-- For an action by continuous maps, the germ relation is a congruence: germs at the source are
preserved by composing with any arrow on either side. -/
instance congruence_germRel : Congruence (germRel G X) where
  equivalence :=
    { refl _ := .of_forall fun _ ↦ rfl
      symm h := h.mono fun _ ↦ Eq.symm
      trans h h' := (h.and h').mono fun _ hy ↦ hy.1.trans hy.2 }
  comp_left {a b _} f g g' h := by
    have hf : (f.hom : G) • a.back = b.back := f.map_val
    have ht : Tendsto ((f.hom : G) • ·) (𝓝 a.back) (𝓝 b.back) :=
      hf ▸ (continuous_const_smul (f.hom : G)).tendsto a.back
    refine (ht.eventually h).mono fun y hy ↦ ?_
    rw [ActionCategory.comp_hom, ActionCategory.comp_hom, mul_smul, mul_smul]
    exact hy
  comp_right g h := h.mono fun y hy ↦ by
    rw [ActionCategory.comp_hom, ActionCategory.comp_hom, mul_smul, mul_smul, hy]

/-- Two arrows of `G ⋉ X` with the same source and target have the same image in the effective
quotient exactly when their labels act in the same way near the source. -/
theorem toEffective_map_eq_iff {a b : ActionCategory G X} {f f' : a ⟶ b} :
    (toEffective G X).map f = (toEffective G X).map f' ↔
      ∀ᶠ y in 𝓝 a.back, (f.hom : G) • y = (f'.hom : G) • y :=
  CategoryTheory.Quotient.functor_map_eq_iff (germRel G X) f f'

/-- Two arrows of `G ⋉ X` have the same image in the effective quotient exactly when they differ
by an element of the germ kernel at their source. -/
theorem toEffective_map_eq_iff_mem_germKernel {a b : ActionCategory G X} {f f' : a ⟶ b} :
    (toEffective G X).map f = (toEffective G X).map f' ↔
      (f.hom : G)⁻¹ * f'.hom ∈ germKernel G a.back :=
  toEffective_map_eq_iff.trans germRel_iff_mem_germKernel

/-- The ineffective arrows of `G ⋉ X`: an automorphism becomes trivial in the effective quotient
exactly when its label is in the germ kernel, that is, when it induces the identity germ. -/
@[simp]
theorem toEffective_map_eq_id_iff {a : ActionCategory G X} {f : a ⟶ a} :
    (toEffective G X).map f = 𝟙 _ ↔ (f.hom : G) ∈ germKernel G a.back := by
  rw [← (toEffective G X).map_id, toEffective_map_eq_iff_mem_germKernel, ActionCategory.id_hom,
    mul_one]
  exact inv_mem_iff

/-- The projection to the effective quotient is faithful exactly when every germ kernel is
trivial: no element of `G` other than `1` acts as the identity near a point. -/
theorem toEffective_faithful_iff : (toEffective G X).Faithful ↔ ∀ x : X, germKernel G x = ⊥ := by
  refine ⟨fun hF x ↦ (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_, fun h ↦ ⟨fun hf ↦ ?_⟩⟩
  · let f : ActionCategory.objEquiv G X x ⟶ ActionCategory.objEquiv G X x :=
      Functor.Elements.homMk g (germKernel_le_stabilizer x hg)
    have hmap : (toEffective G X).map f = (toEffective G X).map (𝟙 _) := by
      rw [CategoryTheory.Functor.map_id, toEffective_map_eq_id_iff]
      exact hg
    simpa only [ActionCategory.id_hom] using
      congrArg (fun f ↦ (f.hom : G)) (hF.map_injective hmap)
  · rw [toEffective_map_eq_iff_mem_germKernel, h, Subgroup.mem_bot, inv_mul_eq_one] at hf
    exact Functor.Elements.hom_ext hf

/-- The kernel of the passage from the stabilizer to the isotropy of the effective quotient is the
germ kernel. -/
theorem Effective.ker_stabilizerToAut (x : X) :
    (Effective.stabilizerToAut G x).ker = (germKernel G x).subgroupOf (stabilizer G x) := by
  ext g
  rw [MonoidHom.mem_ker, Aut.ext_iff, Iso.ext_iff, Aut.one_asIso, Iso.refl_hom,
    stabilizerToAut_apply_asIso_hom]
  -- The identity of `objEquiv G X x` is the image of the identity of `x` under `toEffective`,
  -- and the source `(ActionCategory.objEquiv G X x).back` of the arrow is `x` by `coe_back`.
  exact toEffective_map_eq_id_iff.trans (by
    rw [ActionCategory.stabilizerMulEquivAut_apply_hom_hom, Subgroup.mem_subgroupOf,
      ActionCategory.objEquiv, Equiv.coe_fn_mk, ActionCategory.coe_back])

variable (G) in
/-- The isotropy group of the effective quotient at `x` is the stabilizer of `x` divided by the
germ kernel at `x`: effective reduction keeps exactly the effective part of the isotropy. -/
noncomputable def Effective.stabilizerQuotientMulEquivAut (x : X) :
    stabilizer G x ⧸ (germKernel G x).subgroupOf (stabilizer G x) ≃*
      Aut (Effective.objEquiv G X x) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_stabilizerToAut (G := G) x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (stabilizerToAut_surjective (G := G) x))

@[simp]
theorem Effective.stabilizerQuotientMulEquivAut_mk (x : X) (g : stabilizer G x) :
    Effective.stabilizerQuotientMulEquivAut G x (QuotientGroup.mk g) =
      Effective.stabilizerToAut G x g :=
  (rfl)

end TauCeti.ActionGroupoid
