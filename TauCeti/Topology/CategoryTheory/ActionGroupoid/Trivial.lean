/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Coarse
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective
public import TauCeti.Topology.CategoryTheory.Groupoid.Constructions
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The trivial action gerbe and its effective reduction

Let a group `K` act trivially on a topological space `N`, meaning `∀ (k : K) (x : N), k • x = x`
(for example via `MulAction.compHom N (1 : K →* Equiv.Perm N)`). The native action groupoid
`ActionCategory K N` (`K × N ⇒ N`) retains every group element as an automorphism of every object,
so at each `x : N` its isotropy group is isomorphic to `K` while its orbit space and categorical
coarse space are homeomorphic to `N`.

When `K` carries the discrete topology, `ActionCategory K N` is an étale topological groupoid
(and proper when `K` is compact, i.e. finite, and `N` is Hausdorff). Every arrow is ineffective:
`ineffectiveArrows (ActionCategory K N) = Set.univ`, which is closed. Passing to the effective
quotient `TauCeti.EffectiveQuotient (ActionCategory K N)` collapses all `K`-labels while keeping
the objects and coarse space unchanged:

* `effectiveQuotientEquivalenceDiscrete`: `EffectiveQuotient (ActionCategory K N)` is categorically
  equivalent to the unit groupoid `Discrete N` (`N ⇒ N`).
* `effectiveQuotientObjHomeomorphDiscrete`, `effectiveQuotientArrowHomeomorphDiscrete`: the
  equivalence is a homeomorphism on both objects and total arrows (giving `Discrete N` and
  `Quiver.Total (Discrete N)` the topologies from `TauCeti.UnitGroupoid`).
* `effectiveQuotientCoarseHomeomorphOfSMulEqSelf`: the coarse space of the effective quotient is
  homeomorphic to `N`.
* `isEmpty_equivalence_discrete_of_smul_eq_self`,
  `isEmpty_equivalence_effectiveQuotient_of_smul_eq_self`: when `K` is nontrivial and `N` is
  nonempty, `ActionCategory K N` is not equivalent to `Discrete N` or to its own effective
  quotient, witnessing that effective reduction preserves the coarse space while discarding global
  trivial isotropy and is not an equivalence of presentations.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public noncomputable section

open CategoryTheory MulAction Set Topology TauCeti.MulAction

namespace TauCeti.ActionGroupoid

section Algebraic

variable {K N : Type*} [Group K] [MulAction K N]

/-- Under a trivial action, the stabilizer at every point is the whole group. -/
theorem stabilizer_eq_top_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) (x : N) :
    stabilizer K x = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun k ↦ mem_stabilizer_iff.mpr (htriv k x)

/-- Under a trivial action, forgetting the group label sends `ActionCategory K N` to the unit
groupoid `Discrete N`. -/
def toDiscreteOfSMulEqSelf (htriv : ∀ (k : K) (x : N), k • x = x) :
    ActionCategory K N ⥤ Discrete N where
  obj a := Discrete.mk a.back
  map {a _} f := Discrete.eqToHom ((htriv f.hom a.back).symm.trans f.map_val)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- If a nontrivial group acts trivially on a nonempty type, the action groupoid is not equivalent
to any thin category, since every equivalence preserves isotropy groups up to isomorphism. -/
theorem isEmpty_equivalence_of_isThin_of_smul_eq_self [Nontrivial K] [Nonempty N]
    (htriv : ∀ (k : K) (x : N), k • x = x) {D : Type*} [Category D] [Quiver.IsThin D] :
    IsEmpty (ActionCategory K N ≌ D) := by
  obtain ⟨x⟩ := ‹Nonempty N›
  refine ⟨fun e ↦ ?_⟩
  have h := ActionCategory.stabilizer_eq_bot_of_faithful e.functor x
  rw [stabilizer_eq_top_of_smul_eq_self htriv x] at h
  exact top_ne_bot h

/-- If a nontrivial group acts trivially on a nonempty type, the trivial gerbe `K × N ⇒ N` is not
equivalent to the unit groupoid `Discrete N`. -/
theorem isEmpty_equivalence_discrete_of_smul_eq_self [Nontrivial K] [Nonempty N]
    (htriv : ∀ (k : K) (x : N), k • x = x) :
    IsEmpty (ActionCategory K N ≌ Discrete N) :=
  isEmpty_equivalence_of_isThin_of_smul_eq_self htriv

end Algebraic

section TopologicalSpace

variable {K N : Type*} [Group K] [MulAction K N] [TopologicalSpace N]

/-- A trivial action acts by continuous maps. -/
theorem continuousConstSMul_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) :
    ContinuousConstSMul K N :=
  ⟨fun k ↦ by simpa only [htriv k] using continuous_id'⟩

/-- Under a trivial action, the germ kernel at every point is the whole group. -/
theorem germKernel_eq_top_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) (x : N) :
    germKernel K x = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun k ↦ mem_germKernel.mpr (.of_forall (htriv k))

/-- Under a trivial action, the orbit quotient is homeomorphic to the space itself. -/
def orbitQuotientHomeomorphOfSMulEqSelf (htriv : ∀ (k : K) (x : N), k • x = x) :
    orbitRel.Quotient K N ≃ₜ N where
  toFun := _root_.Quotient.lift id fun _ y ⟨k, hk⟩ ↦ hk.symm.trans (htriv k y)
  invFun := _root_.Quotient.mk (orbitRel K N)
  left_inv := _root_.Quotient.ind fun _ ↦ rfl
  right_inv _ := rfl
  continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr continuous_id
  continuous_invFun := continuous_quotient_mk'

@[simp]
theorem orbitQuotientHomeomorphOfSMulEqSelf_mk (htriv : ∀ (k : K) (x : N), k • x = x) (x : N) :
    orbitQuotientHomeomorphOfSMulEqSelf htriv (_root_.Quotient.mk _ x) = x :=
  (rfl)

@[simp]
theorem orbitQuotientHomeomorphOfSMulEqSelf_symm_apply
    (htriv : ∀ (k : K) (x : N), k • x = x) (x : N) :
    (orbitQuotientHomeomorphOfSMulEqSelf htriv).symm x = _root_.Quotient.mk _ x :=
  (rfl)

/-- Under a trivial action, the coarse space of `ActionCategory K N` is homeomorphic to `N`. -/
def coarseHomeomorphOfSMulEqSelf (htriv : ∀ (k : K) (x : N), k • x = x) :
    _root_.Quotient (isIsomorphicSetoid (ActionCategory K N)) ≃ₜ N :=
  (orbitQuotientHomeomorphIsomorphismClasses K N).symm.trans
    (orbitQuotientHomeomorphOfSMulEqSelf htriv)

@[simp]
theorem coarseHomeomorphOfSMulEqSelf_mk (htriv : ∀ (k : K) (x : N), k • x = x)
    (a : ActionCategory K N) :
    coarseHomeomorphOfSMulEqSelf htriv (_root_.Quotient.mk _ a) = a.back := by
  simp [coarseHomeomorphOfSMulEqSelf]

section GroupTopology

variable [TopologicalSpace K]

/-- A trivial action of any topological group on a topological space is jointly continuous. -/
theorem continuousSMul_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) :
    ContinuousSMul K N :=
  ⟨by simpa only [htriv] using continuous_snd⟩

/-- A trivial action of a compact group on a Hausdorff space is proper. -/
theorem properSMul_of_smul_eq_self [CompactSpace K] [T2Space N]
    (htriv : ∀ (k : K) (x : N), k • x = x) : ProperSMul K N := by
  let _ := continuousSMul_of_smul_eq_self htriv
  exact TauCeti.properSMul_of_compactSpace K N

/-- For a compact group acting trivially on a Hausdorff space, the source-target map of the action
groupoid is proper. -/
theorem isProperMap_source_target_of_smul_eq_self [CompactSpace K] [T2Space N]
    (htriv : ∀ (k : K) (x : N), k • x = x) :
    IsProperMap fun f : Quiver.Total (ActionCategory K N) ↦ (f.left, f.right) :=
  (isProperMap_source_target_iff K N).mpr (properSMul_of_smul_eq_self htriv)

/-- The functor from the effective quotient of a trivial action groupoid to the unit groupoid
`Discrete N` obtained by descending `toDiscreteOfSMulEqSelf`. -/
def effectiveQuotientToDiscrete (htriv : ∀ (k : K) (x : N), k • x = x) :
    EffectiveQuotient (ActionCategory K N) ⥤ Discrete N :=
  CategoryTheory.Quotient.lift (TauCeti.germRel (ActionCategory K N))
    (toDiscreteOfSMulEqSelf htriv) fun _ _ _ _ _ ↦ Subsingleton.elim _ _

@[simp]
theorem effectiveQuotientToDiscrete_obj_mk (htriv : ∀ (k : K) (x : N), k • x = x)
    (a : ActionCategory K N) :
    (effectiveQuotientToDiscrete htriv).obj
      ((toEffectiveQuotient (ActionCategory K N)).obj a) = Discrete.mk a.back :=
  (rfl)

variable (K N) in
/-- Inclusion of the unit groupoid `Discrete N` into `EffectiveQuotient (ActionCategory K N)` by
identity arrows. -/
def discreteToEffectiveQuotient : Discrete N ⥤ EffectiveQuotient (ActionCategory K N) where
  obj x := (toEffectiveQuotient (ActionCategory K N)).obj (ActionCategory.objEquiv K N x.as)
  map f := eqToHom (by rw [Discrete.eq_of_hom f])
  map_id _ := by simp
  map_comp _ _ := by simp

@[simp]
theorem discreteToEffectiveQuotient_obj (x : Discrete N) :
    (discreteToEffectiveQuotient K N).obj x =
      (toEffectiveQuotient (ActionCategory K N)).obj (ActionCategory.objEquiv K N x.as) :=
  (rfl)

variable (K N) in
/-- On objects, `EffectiveQuotient (ActionCategory K N)` is homeomorphic to `Discrete N`. -/
def effectiveQuotientObjHomeomorphDiscrete :
    EffectiveQuotient (ActionCategory K N) ≃ₜ Discrete N :=
  (EffectiveQuotient.objHomeomorph (ActionCategory K N)).symm.trans
    ((objectHomeomorph K N).trans (UnitGroupoid.objectHomeomorph N).symm)

@[simp]
theorem effectiveQuotientObjHomeomorphDiscrete_apply
    (y : EffectiveQuotient (ActionCategory K N)) :
    effectiveQuotientObjHomeomorphDiscrete K N y =
      ⟨((EffectiveQuotient.objEquiv (ActionCategory K N)).symm y).back⟩ := by
  simp [effectiveQuotientObjHomeomorphDiscrete]

/-- Under a trivial action, `effectiveQuotientObjHomeomorphDiscrete` agrees on objects with
`effectiveQuotientToDiscrete`. -/
theorem effectiveQuotientObjHomeomorphDiscrete_apply_eq
    (htriv : ∀ (k : K) (x : N), k • x = x) (y : EffectiveQuotient (ActionCategory K N)) :
    effectiveQuotientObjHomeomorphDiscrete K N y = (effectiveQuotientToDiscrete htriv).obj y := by
  obtain ⟨a, rfl⟩ : ∃ a, (toEffectiveQuotient (ActionCategory K N)).obj a = y :=
    ⟨_, toEffectiveQuotient_obj_objEquiv_symm y⟩
  simp

@[simp]
theorem effectiveQuotientObjHomeomorphDiscrete_symm_apply (x : Discrete N) :
    (effectiveQuotientObjHomeomorphDiscrete K N).symm x =
      (discreteToEffectiveQuotient K N).obj x := by
  simp [effectiveQuotientObjHomeomorphDiscrete]

/-- Under a trivial action, the coarse space of `EffectiveQuotient (ActionCategory K N)` is
homeomorphic to `N`. -/
def effectiveQuotientCoarseHomeomorphOfSMulEqSelf (htriv : ∀ (k : K) (x : N), k • x = x) :
    _root_.Quotient (isIsomorphicSetoid (EffectiveQuotient (ActionCategory K N))) ≃ₜ N :=
  (EffectiveQuotient.isomorphismClassesHomeomorph (ActionCategory K N)).symm.trans
    (coarseHomeomorphOfSMulEqSelf htriv)

@[simp]
theorem effectiveQuotientCoarseHomeomorphOfSMulEqSelf_mk
    (htriv : ∀ (k : K) (x : N), k • x = x) (a : ActionCategory K N) :
    effectiveQuotientCoarseHomeomorphOfSMulEqSelf htriv
      (_root_.Quotient.mk _ ((toEffectiveQuotient (ActionCategory K N)).obj a)) = a.back := by
  have hsymm : (EffectiveQuotient.isomorphismClassesHomeomorph (ActionCategory K N)).symm
      (_root_.Quotient.mk _ ((toEffectiveQuotient (ActionCategory K N)).obj a)) =
      _root_.Quotient.mk _ a :=
    ((EffectiveQuotient.isomorphismClassesHomeomorph (ActionCategory K N)).symm_apply_eq).mpr
      (EffectiveQuotient.isomorphismClassesHomeomorph_apply_mk a).symm
  simp [effectiveQuotientCoarseHomeomorphOfSMulEqSelf, hsymm]

end GroupTopology

section Discrete

variable [TopologicalSpace K] [DiscreteTopology K]

/-- For a discrete group acting trivially, every arrow of `ActionCategory K N` is ineffective. -/
theorem ineffectiveArrows_eq_univ_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) :
    ineffectiveArrows (ActionCategory K N) = Set.univ := by
  refine eq_univ_iff_forall.mpr fun a ↦ mem_ineffectiveArrows_actionCategory_iff.mpr ?_
  rw [germKernel_eq_top_of_smul_eq_self htriv]
  exact Subgroup.mem_top _

/-- For a discrete group acting trivially, the set of ineffective arrows is closed. -/
theorem isClosed_ineffectiveArrows_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) :
    IsClosed (ineffectiveArrows (ActionCategory K N)) := by
  rw [ineffectiveArrows_eq_univ_of_smul_eq_self htriv]
  exact isClosed_univ

/-- For a discrete group acting trivially, the ineffective kernel at every object is all of
`Aut a`. -/
theorem ineffectiveKernel_eq_top_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x)
    (a : ActionCategory K N) :
    letI := continuousSMul_of_smul_eq_self htriv
    letI : IsTopologicalGroup K :=
      { continuous_mul := continuous_of_discreteTopology
        continuous_inv := continuous_of_discreteTopology }
    ineffectiveKernel (isLocalHomeomorph_source K N) a = ⊤ := by
  let _ := continuousSMul_of_smul_eq_self htriv
  let _ : IsTopologicalGroup K :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  rw [Subgroup.eq_top_iff']
  intro g
  rw [mem_ineffectiveKernel, ineffectiveArrows_eq_univ_of_smul_eq_self htriv]
  exact mem_univ _

/-- For a discrete group acting trivially, the effective quotient `EffectiveQuotient (K ⋉ N)` is a
thin category: parallel arrows have equal endpoints and are identified by the germ relation. -/
theorem isThin_effectiveQuotient_of_smul_eq_self (htriv : ∀ (k : K) (x : N), k • x = x) :
    Quiver.IsThin (EffectiveQuotient (ActionCategory K N)) := by
  let _ := continuousSMul_of_smul_eq_self htriv
  let _ : IsTopologicalGroup K :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  intro x y
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  refine ⟨fun φ ψ ↦ ?_⟩
  obtain ⟨f, rfl⟩ := (toEffectiveQuotient (ActionCategory K N)).map_surjective φ
  obtain ⟨g, rfl⟩ := (toEffectiveQuotient (ActionCategory K N)).map_surjective ψ
  refine (toEffectiveQuotient_map_eq_iff (isLocalHomeomorph_source K N)).mpr ?_
  rw [ineffectiveArrows_eq_univ_of_smul_eq_self htriv]
  exact mem_univ _

/-- **Categorical effective reduction of a trivial gerbe.** When a discrete group `K` acts
trivially on `N`, the effective quotient of `ActionCategory K N` is equivalent to the unit groupoid
`Discrete N`. -/
def effectiveQuotientEquivalenceDiscrete (htriv : ∀ (k : K) (x : N), k • x = x) :
    EffectiveQuotient (ActionCategory K N) ≌ Discrete N := by
  let _ : Quiver.IsThin (EffectiveQuotient (ActionCategory K N)) :=
    isThin_effectiveQuotient_of_smul_eq_self htriv
  refine
    { functor := effectiveQuotientToDiscrete htriv
      inverse := discreteToEffectiveQuotient K N
      unitIso := NatIso.ofComponents
        (fun x ↦ eqToIso (by
          obtain ⟨a, rfl⟩ : ∃ a, (toEffectiveQuotient (ActionCategory K N)).obj a = x :=
            ⟨_, toEffectiveQuotient_obj_objEquiv_symm x⟩
          simp only [Functor.id_obj, Functor.comp_obj, effectiveQuotientToDiscrete_obj_mk,
            discreteToEffectiveQuotient_obj]
          exact congrArg (toEffectiveQuotient (ActionCategory K N)).obj
            (ActionCategory.back_coe a).symm))
        (fun _ ↦ Subsingleton.elim _ _)
      counitIso := NatIso.ofComponents
        (fun x ↦ Discrete.eqToIso (by
          simp only [Functor.comp_obj, Functor.id_obj, discreteToEffectiveQuotient_obj,
            effectiveQuotientToDiscrete_obj_mk]
          rw [ActionCategory.objEquiv, Equiv.coe_fn_mk, ActionCategory.coe_back]))
        (fun _ ↦ Subsingleton.elim _ _)
      functor_unitIso_comp := fun _ ↦ Subsingleton.elim _ _ }

@[simp]
theorem effectiveQuotientEquivalenceDiscrete_functor (htriv : ∀ (k : K) (x : N), k • x = x) :
    (effectiveQuotientEquivalenceDiscrete htriv).functor = effectiveQuotientToDiscrete htriv :=
  (rfl)

@[simp]
theorem effectiveQuotientEquivalenceDiscrete_inverse (htriv : ∀ (k : K) (x : N), k • x = x) :
    (effectiveQuotientEquivalenceDiscrete htriv).inverse = discreteToEffectiveQuotient K N :=
  (rfl)

/-- If a nontrivial discrete group acts trivially on a nonempty space, the projection to the
effective quotient is not faithful. -/
theorem not_faithful_toEffectiveQuotient_of_smul_eq_self [Nontrivial K] [Nonempty N]
    (htriv : ∀ (k : K) (x : N), k • x = x) :
    ¬ (toEffectiveQuotient (ActionCategory K N)).Faithful := by
  let _ := continuousSMul_of_smul_eq_self htriv
  let _ : IsTopologicalGroup K :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  obtain ⟨x⟩ := ‹Nonempty N›
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  rw [toEffectiveQuotient_faithful_iff (isLocalHomeomorph_source K N)]
  intro h
  have ha := h (ActionCategory.objEquiv K N x)
  rw [ineffectiveKernel_eq_top_of_smul_eq_self htriv] at ha
  have hfix : x ∈ fixedPoints K N := fun g ↦ htriv g x
  let e := ActionCategory.autMulEquivOfMemFixedPoints K hfix
  have hmem : e.symm k ∈ (⊤ : Subgroup (Aut (ActionCategory.objEquiv K N x))) :=
    Subgroup.mem_top _
  rw [ha, Subgroup.mem_bot] at hmem
  exact hk ((e.apply_symm_apply k).symm.trans ((congrArg e hmem).trans (map_one e)))

/-- If a nontrivial discrete group acts trivially on a nonempty space, the action groupoid is not
equivalent to its effective quotient. -/
theorem isEmpty_equivalence_effectiveQuotient_of_smul_eq_self [Nontrivial K] [Nonempty N]
    (htriv : ∀ (k : K) (x : N), k • x = x) :
    IsEmpty (ActionCategory K N ≌ EffectiveQuotient (ActionCategory K N)) := by
  let _ : Quiver.IsThin (EffectiveQuotient (ActionCategory K N)) :=
    isThin_effectiveQuotient_of_smul_eq_self htriv
  exact isEmpty_equivalence_of_isThin_of_smul_eq_self htriv

/-- **Topological effective reduction of a trivial gerbe.** On total arrow spaces, the effective
quotient of `ActionCategory K N` is homeomorphic to the unit groupoid `Quiver.Total (Discrete N)`
via the total-arrow maps of `effectiveQuotientToDiscrete` and `discreteToEffectiveQuotient`. -/
def effectiveQuotientArrowHomeomorphDiscrete (htriv : ∀ (k : K) (x : N), k • x = x) :
    Quiver.Total (EffectiveQuotient (ActionCategory K N)) ≃ₜ Quiver.Total (Discrete N) := by
  let _ := continuousSMul_of_smul_eq_self htriv
  let _ : IsTopologicalGroup K :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  refine
    { toFun := (effectiveQuotientToDiscrete htriv).toPrefunctor.mapTotal
      invFun := (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal
      left_inv := fun α ↦ ?_
      right_inv := fun β ↦ ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · obtain ⟨⟨a, b, f⟩, rfl⟩ := EffectiveQuotient.mapTotal_surjective α
    have hback : a.back = b.back := (htriv f.hom a.back).symm.trans f.map_val
    have hab : a = b := (ActionCategory.back_coe a).symm.trans
      ((congrArg (ActionCategory.objEquiv K N) hback).trans (ActionCategory.back_coe b))
    subst b
    have hfid : (toEffectiveQuotient (ActionCategory K N)).map f = 𝟙 _ := by
      rw [toEffectiveQuotient_map_eq_id_iff (isLocalHomeomorph_source K N),
        ineffectiveArrows_eq_univ_of_smul_eq_self htriv]
      exact mem_univ _
    have hobj_eq : (discreteToEffectiveQuotient K N).obj
        ((effectiveQuotientToDiscrete htriv).obj
          ((toEffectiveQuotient (ActionCategory K N)).obj a)) =
        (toEffectiveQuotient (ActionCategory K N)).obj a := by
      rw [effectiveQuotientToDiscrete_obj_mk, discreteToEffectiveQuotient_obj]
      exact congrArg _ (ActionCategory.back_coe a)
    dsimp only [Prefunctor.mapTotal, Functor.toPrefunctor_obj, Functor.toPrefunctor_map]
    rw [hfid, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun y ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total _)) hobj_eq
  · rcases β with ⟨⟨x⟩, ⟨y⟩, ψ⟩
    have hxy : x = y := Discrete.eq_of_hom ψ
    subst y
    have hψ : ψ = 𝟙 (Discrete.mk x) := Subsingleton.elim _ _
    subst hψ
    rfl
  · apply (UnitGroupoid.arrowHomeomorph N).isInducing.continuous_iff.mpr
    have hcont : Continuous fun α : Quiver.Total (EffectiveQuotient (ActionCategory K N)) ↦
        objectHomeomorph K N
          ((EffectiveQuotient.objHomeomorph (ActionCategory K N)).symm α.left) :=
      (objectHomeomorph K N).continuous.comp
        ((EffectiveQuotient.objHomeomorph (ActionCategory K N)).symm.continuous.comp
          EffectiveQuotient.continuous_source)
    refine hcont.congr fun α ↦ ?_
    obtain ⟨⟨a, b, f⟩, rfl⟩ := EffectiveQuotient.mapTotal_surjective α
    simp [Prefunctor.mapTotal]
  · have hcont : Continuous ((toEffectiveQuotient (ActionCategory K N)).toPrefunctor.mapTotal ∘
        (fun a : ActionCategory K N ↦ (⟨a, a, 𝟙 a⟩ : Quiver.Total (ActionCategory K N))) ∘
        (objectHomeomorph K N).symm ∘ UnitGroupoid.arrowHomeomorph N) :=
      EffectiveQuotient.isQuotientMap_mapTotal.continuous.comp
        ((continuous_unit K N).comp
          ((objectHomeomorph K N).symm.continuous.comp (UnitGroupoid.arrowHomeomorph N).continuous))
    refine hcont.congr fun β ↦ ?_
    rcases β with ⟨⟨x⟩, ⟨y⟩, ψ⟩
    have hxy : x = y := Discrete.eq_of_hom ψ
    subst y
    have hψ : ψ = 𝟙 (Discrete.mk x) := Subsingleton.elim _ _
    subst hψ
    dsimp only [Function.comp_def, Prefunctor.mapTotal, Functor.toPrefunctor_obj,
      Functor.toPrefunctor_map]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun y ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total _)) (by simp)

@[simp]
theorem effectiveQuotientArrowHomeomorphDiscrete_apply
    (htriv : ∀ (k : K) (x : N), k • x = x)
    (α : Quiver.Total (EffectiveQuotient (ActionCategory K N))) :
    effectiveQuotientArrowHomeomorphDiscrete htriv α =
      (effectiveQuotientToDiscrete htriv).toPrefunctor.mapTotal α :=
  (rfl)

@[simp]
theorem effectiveQuotientArrowHomeomorphDiscrete_symm_apply
    (htriv : ∀ (k : K) (x : N), k • x = x)
    (β : Quiver.Total (Discrete N)) :
    (effectiveQuotientArrowHomeomorphDiscrete htriv).symm β =
      (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal β :=
  (rfl)

end Discrete

end TopologicalSpace

end TauCeti.ActionGroupoid
