/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Identifying the image of a compact set by its fibres

Let `π : X → Y` be continuous on a compact set `S ⊆ X`, with `Y` Hausdorff. To identify the image
`π '' S` with a model space `T`, it suffices to give a continuous surjection `S → T` onto a
Hausdorff space with the same fibres as `π`. The map `S → π '' S` is a quotient map, since `S` is
compact, so `f` descends to a continuous bijection `π '' S → T` from a compact space to a Hausdorff
one. The same compactness argument makes a continuous injection on a compact set a homeomorphism
onto its Hausdorff image, `IsCompact.imageHomeomorph`.
-/

public section

open Set Function

namespace TauCeti

/-- **Compact images by fibres.** Let `π : X → Y` be continuous on a compact set `S ⊆ X`, with `Y`
Hausdorff. If `f : S → T` is a continuous surjection onto a Hausdorff space whose fibres are the
fibres of `π` on `S`, then the image `π '' S` is homeomorphic to `T`, by a homeomorphism sending
`π x` to `f x`. -/
theorem exists_homeomorph_image_of_forall_eq_iff {X Y T : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace T] [T2Space Y] [T2Space T] {π : X → Y} {S : Set X}
    (hπ : ContinuousOn π S) (hS : IsCompact S) (f : S → T) (hf : Continuous f)
    (hsurj : Surjective f) (hfib : ∀ x y : S, f x = f y ↔ π x = π y) :
    ∃ h : π '' S ≃ₜ T, ∀ x : S, h ⟨π x, mem_image_of_mem π x.2⟩ = f x := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let q : C(S, π '' S) :=
    ⟨fun x ↦ ⟨π x, x, x.2, rfl⟩, hπ.domRestrict.subtype_mk _⟩
  have hqs : Surjective q := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hq : Topology.IsQuotientMap q :=
    .of_surjective_continuous hqs q.continuous
  have : CompactSpace (π '' S) := isCompact_iff_compactSpace.mp (hS.image_of_continuousOn hπ)
  -- Descend `f` along the quotient map `q`; the result is a continuous bijection out of a compact
  -- space into a Hausdorff one.
  have hfq : FactorsThrough f q := fun x y h ↦ (hfib x y).2 (congrArg Subtype.val h)
  let g := hq.lift ⟨f, hf⟩ hfq
  have hgq (x : S) : g (q x) = f x := DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfq) x
  have hginj : Injective g := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hqs y
    obtain ⟨x', rfl⟩ := hqs y'
    rw [hgq, hgq] at h
    exact Subtype.ext ((hfib x x').1 h)
  have hgs : Surjective g := fun t ↦
    let ⟨x, hx⟩ := hsurj t
    ⟨q x, (hgq x).trans hx⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgs⟩) g.continuous,
    hgq⟩

end TauCeti

namespace IsCompact

/-- A continuous injection defined on a compact set is a homeomorphism onto its image, when the
image is Hausdorff. This is the set-level form of `Continuous.homeoOfEquivCompactToT2`. -/
noncomputable def imageHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {C : Set X} (hC : IsCompact C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) [T2Space (g '' C)] : C ≃ₜ g '' C :=
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  Continuous.homeoOfEquivCompactToT2 (f := hgi.bijOn_image.equiv g)
    (hg.mapsToRestrict hgi.bijOn_image.mapsTo)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {C : Set X} (hC : IsCompact C)
  {g : X → Y} (hg : ContinuousOn g C) (hgi : InjOn g C) [T2Space (g '' C)]

/-- The homeomorphism `IsCompact.imageHomeomorph` sends a point `x` of `C` to `g x`. -/
@[simp]
theorem imageHomeomorph_apply (x : C) :
    hC.imageHomeomorph hg hgi x = ⟨g x, mem_image_of_mem g x.2⟩ := by
  unfold imageHomeomorph
  rfl

/-- The inverse of `IsCompact.imageHomeomorph` is a section of `g`: applying `g` to the inverse
image of `y` gives back `y`. -/
theorem apply_imageHomeomorph_symm (y : g '' C) :
    g ((hC.imageHomeomorph hg hgi).symm y) = y := by
  have h := hC.imageHomeomorph_apply hg hgi ((hC.imageHomeomorph hg hgi).symm y)
  rw [Homeomorph.apply_symm_apply] at h
  exact (congrArg Subtype.val h).symm

end IsCompact
