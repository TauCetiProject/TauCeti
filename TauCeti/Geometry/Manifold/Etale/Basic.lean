/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Topology.CategoryTheory.Etale
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic

import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth structure maps and local actions in étale groupoids

In a topological groupoid whose source and target are `C^n` local diffeomorphisms, all remaining
groupoid structure maps are automatically `C^n` local diffeomorphisms: the unit map is a
continuous section of the source, inversion intertwines source and target and hence forms a `C^n`
diffeomorphism of the arrow space, and pulling arrow charts back along the second projection makes
the subspace of composable pairs a charted space on which both projections and composition are
`C^n` local diffeomorphisms.

When the groupoid is also proper with Hausdorff arrow space, its local isotropy action is smooth.
The action is on an open neighbourhood with the restricted charts of the object manifold. Its
action groupoid maps fully faithfully to the original groupoid, and the arrows carrying each
isotropy label form an open submanifold, parametrized by a local diffeomorphism from that
neighbourhood. The isotropy acts by smooth maps and fixes the centre, so this local model can be
used with finite-group linearization.

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

/-- A proper groupoid with Hausdorff arrow space, continuous units and composition, and `C^n`
source and target local diffeomorphisms is locally the action groupoid of a `C^n` isotropy action
fixing the centre. The fully faithful functor is the
inclusion on objects. Each label parametrizes an open set of arrows by a local diffeomorphism,
its source is the parameter and its target is the action of the label on that parameter.
Its arrow at the centre is the original isotropy arrow, even for ineffective labels. -/
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
      (∀ g : Aut x, Quiver.Total.left ∘ (fun y : U ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, y)).hom⟩ :
          Quiver.Total C)) = (Subtype.val : U → C)) ∧
      (∀ g : Aut x, Quiver.Total.right ∘ (fun y : U ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, y)).hom⟩ :
          Quiver.Total C)) = fun y : U ↦ (g • y : U).val) ∧
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
    hopen, hsmooth, hsource, htarget, hcentre⟩
  · apply (ContMDiff.subtypeVal_comp_iff V _).mp
    have h := ht.contMDiff.comp (hsmooth g).contMDiff
    rw [htarget] at h
    exact h
  · intro g
    apply Subtype.ext
    have h := congrArg Quiver.Total.right (hcentre g)
    exact (congrFun (htarget g) ⟨x, hxU⟩).symm.trans h

namespace IsTopologicalGroupoid

section StructureMaps

variable {D : Type*} [Category D] [IsGroupoid D]
  [TopologicalSpace D] [ChartedSpace H D]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace H' (Quiver.Total D)]
  [IsTopologicalGroupoid D]

/-- In a topological groupoid whose source is a `C^n` local diffeomorphism, the unit map is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_unit
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D)) :
    IsLocalDiffeomorph I J n fun x : D ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total D) := by
  intro x
  have hcomp : IsLocalDiffeomorphAt I I n
      (Quiver.Total.left ∘ fun y : D ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total D)) x :=
    (Diffeomorph.refl I D n).isLocalDiffeomorph x
  exact hcomp.of_comp_left (hs ⟨x, x, 𝟙 x⟩) continuous_unit.continuousAt

/-- In a topological groupoid whose source is a `C^n` local diffeomorphism, the unit map is
`C^n`. -/
theorem contMDiff_unit
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D)) :
    ContMDiff I J n fun x : D ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total D) :=
  (isLocalDiffeomorph_unit hs).contMDiff

/-- In a topological groupoid whose source and target are `C^n` local diffeomorphisms, inversion is
a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_inverse
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    IsLocalDiffeomorph J J n
      fun a : Quiver.Total D ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total D) := by
  intro a
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.left ∘
        fun b : Quiver.Total D ↦ (⟨b.right, b.left, inv b.hom⟩ : Quiver.Total D)) a :=
    ht a
  exact hcomp.of_comp_left (hs _) continuous_inverse.continuousAt

/-- In a topological groupoid whose source and target are `C^n` local diffeomorphisms, inversion is
`C^n`. -/
theorem contMDiff_inverse
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    ContMDiff J J n
      fun a : Quiver.Total D ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total D) :=
  (isLocalDiffeomorph_inverse hs ht).contMDiff

/-- Inversion on the total arrows of a topological groupoid with `C^n` locally diffeomorphic
source and target is a `C^n` diffeomorphism. -/
noncomputable def inverseDiffeomorph
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    Quiver.Total D ≃ₘ^n⟮J, J⟯ Quiver.Total D where
  toFun a := ⟨a.right, a.left, inv a.hom⟩
  invFun a := ⟨a.right, a.left, inv a.hom⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  contMDiff_toFun := contMDiff_inverse hs ht
  contMDiff_invFun := contMDiff_inverse hs ht

@[simp]
theorem inverseDiffeomorph_apply
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D))
    (a : Quiver.Total D) :
    inverseDiffeomorph hs ht a = ⟨a.right, a.left, inv a.hom⟩ :=
  (rfl)

@[simp]
theorem inverseDiffeomorph_symm_apply
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D))
    (a : Quiver.Total D) :
    (inverseDiffeomorph hs ht).symm a = ⟨a.right, a.left, inv a.hom⟩ :=
  (rfl)

@[simp]
theorem inverseDiffeomorph_toHomeomorph
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    (inverseDiffeomorph hs ht).toHomeomorph = inverseHomeomorph D :=
  Homeomorph.ext fun a ↦ (inverseHomeomorph_apply D a).symm

/-- In an étale topological groupoid, the subspace of composable pairs carries the charted-space
structure pulled back from total arrows along the second projection. -/
@[instance_reducible]
noncomputable def composablePairsChartedSpace
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D)) :
    ChartedSpace H' {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} :=
  (((isLocalHomeomorph_source_iff_target D).mp hs).pullback_snd
    continuous_source).chartedSpaceComap

/-- The pulled-back charts on composable pairs form a `C^n` manifold whenever the arrow space is a
`C^n` manifold. -/
theorem isManifold_composablePairs [IsManifold J n (Quiver.Total D)]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D)) :
    letI := composablePairsChartedSpace (H' := H') hs
    IsManifold J n {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} :=
  (((isLocalHomeomorph_source_iff_target D).mp hs).pullback_snd
    continuous_source).isManifold_chartedSpaceComap

/-- The second projection from composable pairs to total arrows is a `C^n` local diffeomorphism for
the pulled-back charts. -/
theorem isLocalDiffeomorph_composablePairs_snd
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D)) :
    letI := composablePairsChartedSpace (H' := H') hs
    IsLocalDiffeomorph J J n
      (fun p : {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} ↦ p.1.2) :=
  (((isLocalHomeomorph_source_iff_target D).mp hs).pullback_snd
    continuous_source).isLocalDiffeomorph_chartedSpaceComap

/-- For an étale topological groupoid, a map into composable pairs is `C^n` if and only if it is
continuous and its second projection is `C^n`. -/
theorem contMDiff_composablePairs_iff
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
    {f : N → {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left}}
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total D → D)) :
    letI := composablePairsChartedSpace (H' := H') hs
    ContMDiff I'' J n f ↔ Continuous f ∧ ContMDiff I'' J n (fun z ↦ (f z).1.2) :=
  (((isLocalHomeomorph_source_iff_target D).mp hs).pullback_snd
    continuous_source).contMDiff_chartedSpaceComap_iff

/-- The first projection from composable pairs to total arrows is a `C^n` local diffeomorphism when
source and target are `C^n` local diffeomorphisms. -/
theorem isLocalDiffeomorph_composablePairs_fst
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    letI := composablePairsChartedSpace (H' := H') hs.isLocalHomeomorph
    IsLocalDiffeomorph J J n
      (fun p : {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} ↦ p.1.1) := by
  let := composablePairsChartedSpace (H' := H') hs.isLocalHomeomorph
  intro p
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.right ∘
        fun q : {q : Quiver.Total D × Quiver.Total D // q.1.right = q.2.left} ↦ q.1.1) p := by
    have heq : (Quiver.Total.right ∘
        fun q : {q : Quiver.Total D × Quiver.Total D // q.1.right = q.2.left} ↦ q.1.1) =
        Quiver.Total.left ∘ fun q ↦ q.1.2 :=
      funext fun q ↦ q.2
    rw [heq]
    exact (isLocalDiffeomorph_composablePairs_snd (J := J) (n := n) hs.isLocalHomeomorph p).comp
      (hg := hs p.1.2)
  exact hcomp.of_comp_left (ht p.1.1) (continuous_fst.comp continuous_subtype_val).continuousAt

/-- Composition of composable pairs is a `C^n` local diffeomorphism when source and target are `C^n`
local diffeomorphisms. -/
theorem isLocalDiffeomorph_comp
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    letI := composablePairsChartedSpace (H' := H') hs.isLocalHomeomorph
    IsLocalDiffeomorph J J n
      fun p : {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2 := by
  let := composablePairsChartedSpace (H' := H') hs.isLocalHomeomorph
  intro p
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.left ∘
        fun q : {q : Quiver.Total D × Quiver.Total D // q.1.right = q.2.left} ↦
          q.1.1.comp q.1.2 q.2) p := by
    have heq : (Quiver.Total.left ∘
        fun q : {q : Quiver.Total D × Quiver.Total D // q.1.right = q.2.left} ↦
          q.1.1.comp q.1.2 q.2) =
        Quiver.Total.left ∘ fun q ↦ q.1.1 :=
      funext fun q ↦ Quiver.Total.comp_left q.1.1 q.1.2 q.2
    rw [heq]
    exact (isLocalDiffeomorph_composablePairs_fst hs ht p).comp (hg := hs p.1.1)
  exact hcomp.of_comp_left (hs _) continuous_comp.continuousAt

/-- Composition of composable pairs is `C^n` when source and target are `C^n` local
diffeomorphisms. -/
theorem contMDiff_comp
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total D → D))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total D → D)) :
    letI := composablePairsChartedSpace (H' := H') hs.isLocalHomeomorph
    ContMDiff J J n
      fun p : {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2 := by
  let := composablePairsChartedSpace (H' := H') hs.isLocalHomeomorph
  exact (isLocalDiffeomorph_comp hs ht).contMDiff

end StructureMaps

end IsTopologicalGroupoid

end TauCeti
