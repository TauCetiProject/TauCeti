/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Topology.CategoryTheory.Etale

import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth local actions in proper étale groupoids

The local isotropy action of a proper étale groupoid is smooth whenever source and target are
local diffeomorphisms. The action is on an open neighbourhood with the restricted charts of the
object manifold. Its action groupoid maps fully faithfully to the original groupoid, and the
arrows carrying each isotropy label form an open submanifold, parametrized by a local
diffeomorphism from that neighbourhood. The isotropy acts by smooth maps and fixes the centre,
so this local model can be used with finite-group linearization.

The result retains the given object and total-arrow charts. Distinct isotropy arrows remain
distinct labels, including arrows acting trivially on the whole neighbourhood. Only continuity
of units and composition is needed in addition to the local-diffeomorphism hypotheses.

The underlying continuous local action is
`TauCeti.exists_isotropy_action_of_proper_source_target`; this file upgrades its regularity.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]

/-- A proper groupoid whose source and target are `C^n` local diffeomorphisms is locally the
action groupoid of a `C^n` isotropy action fixing the centre. The fully faithful functor is the
inclusion on objects. Each label parametrizes an open set of arrows by a local diffeomorphism,
and its arrow at the centre is the original isotropy arrow, even for ineffective labels. -/
theorem exists_contMDiff_isotropy_action_of_proper_source_target [T2Space (Quiver.Total C)]
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2)
    (x : C) :
    ∃ (U : TopologicalSpace.Opens C) (hxU : x ∈ U) (_ : MulAction (Aut x) U)
      (F : ActionCategory (Aut x) U ⥤ C),
      ContMDiffConstSMul I n (Aut x) U ∧
      (∀ g : Aut x, g • (⟨x, hxU⟩ : U) = ⟨x, hxU⟩) ∧
      (∀ a, F.obj a = (a.back : C)) ∧ F.Full ∧ F.Faithful ∧
      (∀ g : Aut x, IsOpenEmbedding fun y : U ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, y)).hom⟩ :
          Quiver.Total C)) ∧
      (∀ g : Aut x, IsLocalDiffeomorph I J n fun y : U ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, y)).hom⟩ :
          Quiver.Total C)) ∧
      ∀ g : Aut x,
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, ⟨x, hxU⟩)).hom⟩ :
          Quiver.Total C) = ⟨x, x, g.asIso.hom⟩ := by
  obtain ⟨U, hxU, inst, F, hU, -, hobj, hfull, hfaithful, hopen, hcentre⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs.isLocalHomeomorph
      ht.isLocalHomeomorph hu hc x
  let V : TopologicalSpace.Opens C := ⟨U, hU⟩
  let : MulAction (Aut x) V := inst
  let σ (g : Aut x) (y : V) : Quiver.Total C :=
    ⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, y)).hom⟩
  have hback (y : V) : (ActionCategory.objEquiv (Aut x) V y).back = y :=
    (ActionCategory.objEquiv (Aut x) V).left_inv y
  have hsource (g : Aut x) : Quiver.Total.left ∘ σ g = (Subtype.val : V → C) := by
    funext y
    simp only [Function.comp_apply, σ, hobj, ActionCategory.totalEquiv_symm_apply_left, hback]
  have htarget (g : Aut x) :
      Quiver.Total.right ∘ σ g = fun y : V ↦ (g • y : V).val := by
    funext y
    simp only [Function.comp_apply, σ, hobj, ActionCategory.totalEquiv_symm_apply_right, hback]
  -- Source coordinates identify each continuous labelled section with a local inverse of source.
  have hsmooth (g : Aut x) : IsLocalDiffeomorph I J n (σ g) := by
    have hcomp : IsLocalDiffeomorph I I n (Quiver.Total.left ∘ σ g) := by
      rw [hsource]
      exact isLocalDiffeomorph_subtype_val
    exact fun y ↦ (hcomp y).of_comp_left (hs _) ((hopen g).continuous.continuousAt)
  refine ⟨V, hxU, inst, F, ⟨fun g ↦ ?_⟩, ?_, hobj, hfull, hfaithful,
    hopen, hsmooth, hcentre⟩
  · apply (ContMDiff.subtypeVal_comp_iff V _).mp
    have h := ht.contMDiff.comp (hsmooth g).contMDiff
    rw [htarget] at h
    exact h
  · intro g
    apply Subtype.ext
    have h := congrArg Quiver.Total.right (hcentre g)
    exact (congrFun (htarget g) ⟨x, hxU⟩).symm.trans h

end TauCeti
