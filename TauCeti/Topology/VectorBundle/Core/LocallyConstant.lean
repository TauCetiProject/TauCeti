/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Topology.VectorBundle.Core.Congr
import Mathlib.Logic.Equiv.Sum

/-!
# Gluing vector-bundle cores along a locally constant partition of the base

Given a locally constant map `c : B → α` and a family of coordinate cores
`Z a : VectorBundleCore R {x : B // c x = a} F (ι a)` with common model fibre `F` on the clopen
fibres of `c`, `IsLocallyConstant.sigmaVectorBundleCore` assembles them into a single
`VectorBundleCore R B F (Σ a : α, ι a)` over `B`. Charts from distinct fibres of `c` have disjoint
open base sets in `B`, while charts from the same fibre retain the transitions of `Z a`.

`IsLocallyConstant.sigmaVectorBundleCoreHomeomorph` identifies the disjoint union
`Σ a : α, (Z a).TotalSpace` with the reconstructed total space over `B`, and
`IsLocallyConstant.continuous_mk_sigmaVectorBundleCore_iff` characterizes continuity into the glued
total space by continuity into each fibre core `(Z a).TotalSpace`.

When each fibre core `Z a` is indexed by the points of `{x : B // c x = a}`, reindexing along
`(Equiv.sigmaFiberEquiv c).symm` produces a core `IsLocallyConstant.pointIndexedVectorBundleCore`
indexed by `B` itself, preserving the property `indexAt x = x` whenever each `Z a` satisfies it.
No finite-cover, decidable-equality, separation, or completeness assumption is required.
-/

public section

open Topology

namespace IsLocallyConstant

variable {R B F α : Type*} [NontriviallyNormedField R] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace R F]
  {ι : α → Type*} {c : B → α}

section Sigma

open scoped Classical in
/-- Glue a family of `VectorBundleCore`s on the clopen fibres of a locally constant function
`c : B → α` into a single `VectorBundleCore` over `B`. -/
noncomputable def sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) :
    VectorBundleCore R B F (Σ a : α, ι a) where
  baseSet p := Subtype.val '' (Z p.1).baseSet p.2
  isOpen_baseSet p :=
    (hc.isOpen_fiber p.1).isOpenEmbedding_subtypeVal.isOpenMap _ ((Z p.1).isOpen_baseSet p.2)
  indexAt x := ⟨c x, (Z (c x)).indexAt ⟨x, rfl⟩⟩
  mem_baseSet_at x := ⟨⟨x, rfl⟩, (Z (c x)).mem_baseSet_at ⟨x, rfl⟩, rfl⟩
  coordChange p q x :=
    if hp : c x = p.1 then
      if hq : p.1 = q.1 then (Z p.1).coordChange p.2 (hq ▸ q.2) ⟨x, hp⟩
      else ContinuousLinearMap.id R F
    else ContinuousLinearMap.id R F
  coordChange_self := by
    rintro ⟨a, i⟩ x hx v
    dsimp only at hx ⊢
    rw [Subtype.coe_image] at hx
    obtain ⟨rfl, hxi⟩ := hx
    simp [(Z (c x)).coordChange_self i ⟨x, rfl⟩ hxi v]
  continuousOn_coordChange := by
    rintro ⟨a, i⟩ ⟨b, j⟩
    dsimp only
    by_cases hab : a = b
    · subst hab
      rw [Subtype.coe_image, Subtype.coe_image, continuousOn_iff_continuous_domRestrict]
      let f : ↥({x | ∃ h : c x = a, ⟨x, h⟩ ∈ (Z a).baseSet i} ∩
          {x | ∃ h : c x = a, ⟨x, h⟩ ∈ (Z a).baseSet j}) → {y : B // c y = a} :=
        fun x => ⟨x.val, x.property.1.choose⟩
      have hf : Continuous f := continuous_subtypeVal.subtype_mk _
      refine (((Z a).continuousOn_coordChange i j).comp_continuous hf
        fun x => ⟨x.property.1.choose_spec, x.property.2.choose_spec⟩).congr fun x => ?_
      dsimp only [Function.comp_apply, Set.domRestrict]
      rw [dite_eq_left (f x).property, dite_eq_left rfl]
    · refine (continuousOn_const (c := ContinuousLinearMap.id R F)).congr fun x _ => ?_
      by_cases hx : c x = a <;> simp [hx, hab]
  coordChange_comp := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨d, k⟩ x ⟨⟨hx₁, hx₂⟩, hx₃⟩ v
    dsimp only at hx₁ hx₂ hx₃ ⊢
    rw [Subtype.coe_image] at hx₁ hx₂ hx₃
    obtain ⟨rfl, hi⟩ := hx₁
    obtain ⟨hb, hj⟩ := hx₂
    obtain ⟨hd, hk⟩ := hx₃
    subst hb hd
    simp [(Z (c x)).coordChange_comp i j k ⟨x, rfl⟩ ⟨⟨hi, hj⟩, hk⟩ v]

/-- Each chart domain of `hc.sigmaVectorBundleCore Z` is the image in `B` of the corresponding
fibre chart domain. -/
theorem baseSet_sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) (p : Σ a : α, ι a) :
    (hc.sigmaVectorBundleCore Z).baseSet p = Subtype.val '' (Z p.1).baseSet p.2 := (rfl)

/-- Base set of a local trivialization of `hc.sigmaVectorBundleCore Z`. -/
@[simp]
theorem localTriv_baseSet_sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) (p : Σ a : α, ι a) :
    ((hc.sigmaVectorBundleCore Z).localTriv p).baseSet =
      Subtype.val '' ((Z p.1).localTriv p.2).baseSet := (rfl)

/-- Preferred chart index of `hc.sigmaVectorBundleCore Z` at a base point `x : B`. -/
@[simp]
theorem indexAt_sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) (x : B) :
    (hc.sigmaVectorBundleCore Z).indexAt x = ⟨c x, (Z (c x)).indexAt ⟨x, rfl⟩⟩ := (rfl)

/-- Preferred chart index of `hc.sigmaVectorBundleCore Z` at a point of the fibre `c ⁻¹' {a}`. -/
theorem indexAt_sigmaVectorBundleCore_coe (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (x : {x : B // c x = a}) :
    (hc.sigmaVectorBundleCore Z).indexAt x.val = ⟨a, (Z a).indexAt x⟩ := by
  rcases x with ⟨x, rfl⟩
  rfl

/-- Transition operator of `hc.sigmaVectorBundleCore Z` between two charts on the same fibre. -/
@[simp]
theorem coordChange_sigmaVectorBundleCore_same (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (i j : ι a) (x : {x : B // c x = a}) :
    (hc.sigmaVectorBundleCore Z).coordChange ⟨a, i⟩ ⟨a, j⟩ x.val =
      (Z a).coordChange i j x := by
  rcases x with ⟨x, rfl⟩
  simp [sigmaVectorBundleCore]

/-- On each clopen fibre `c ⁻¹' {a}`, the preferred trivialization of the glued core agrees with
the preferred trivialization of `Z a`. -/
theorem localTrivAt_sigmaVectorBundleCore_snd (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (x₀ x : {x : B // c x = a}) (v : F) :
    ((hc.sigmaVectorBundleCore Z).localTrivAt x₀.val ⟨x.val, v⟩).2 =
      ((Z a).localTrivAt x₀ ⟨x, v⟩).2 := by
  simp only [← VectorBundleCore.localTrivAt_def, VectorBundleCore.localTriv_apply,
    hc.indexAt_sigmaVectorBundleCore_coe Z a x, hc.indexAt_sigmaVectorBundleCore_coe Z a x₀,
    hc.coordChange_sigmaVectorBundleCore_same Z a _ _ x]

/-- The disjoint union of the fibre total spaces `(Z a).TotalSpace` is homeomorphic over `B` to the
reconstructed total space of `hc.sigmaVectorBundleCore Z`. -/
noncomputable def sigmaVectorBundleCoreHomeomorph (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) :
    (Σ a : α, (Z a).TotalSpace) ≃ₜ (hc.sigmaVectorBundleCore Z).TotalSpace where
  toFun p := ⟨p.2.proj.val, p.2.snd⟩
  invFun p := ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩
  left_inv := by rintro ⟨a, ⟨⟨x, rfl⟩, v⟩⟩; rfl
  right_inv := fun ⟨_, _⟩ => rfl
  continuous_toFun := by
    refine continuous_sigma fun a => continuous_iff_continuousAt.2 fun p₀ => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    have hp₀ := (FiberBundle.continuousAt_totalSpace _ _).1
      ((continuous_id (X := (Z a).TotalSpace)).continuousAt (x := p₀))
    refine ⟨(continuous_subtypeVal.comp (Z a).continuous_proj).continuousAt, ?_⟩
    convert hp₀.2 using 1
    funext p
    simp only [id_eq, VectorBundleCore.trivializationAt]
    exact hc.localTrivAt_sigmaVectorBundleCore_snd Z a p₀.proj p.proj p.snd
  continuous_invFun := by
    refine continuous_of_cover_nhds
      (s := fun a : α => {p : (hc.sigmaVectorBundleCore Z).TotalSpace | c p.proj = a})
      (fun p => ⟨c p.proj, ((hc.isOpen_fiber _).preimage
        (hc.sigmaVectorBundleCore Z).continuous_proj).mem_nhds rfl⟩) fun a => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have hsub : Continuous fun q :
        {p : (hc.sigmaVectorBundleCore Z).TotalSpace // c p.proj = a} =>
        (⟨⟨q.val.proj, q.property⟩, q.val.snd⟩ : (Z a).TotalSpace) := by
      refine continuous_iff_continuousAt.2 fun q₀ => ?_
      rw [FiberBundle.continuousAt_totalSpace]
      have hq₀ := (FiberBundle.continuousAt_totalSpace _ _).1
        (continuous_subtypeVal.continuousAt (x := q₀))
      refine ⟨(((hc.sigmaVectorBundleCore Z).continuous_proj.comp
        continuous_subtypeVal).subtype_mk _).continuousAt, ?_⟩
      convert hq₀.2 using 1
      funext q
      simp only [VectorBundleCore.trivializationAt]
      exact (hc.localTrivAt_sigmaVectorBundleCore_snd Z a ⟨q₀.val.proj, q₀.property⟩
        ⟨q.val.proj, q.property⟩ q.val.snd).symm
    refine (continuous_sigmaMk.comp hsub).congr ?_
    rintro ⟨⟨_, _⟩, rfl⟩
    rfl

/-- Evaluation of `sigmaVectorBundleCoreHomeomorph` on an element of a fibre total space. -/
@[simp]
theorem sigmaVectorBundleCoreHomeomorph_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (p : Σ a : α, (Z a).TotalSpace) :
    hc.sigmaVectorBundleCoreHomeomorph Z p = ⟨p.2.proj.val, p.2.snd⟩ := (rfl)

/-- Evaluation of the inverse of `sigmaVectorBundleCoreHomeomorph`. -/
@[simp]
theorem sigmaVectorBundleCoreHomeomorph_symm_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (p : (hc.sigmaVectorBundleCore Z).TotalSpace) :
    (hc.sigmaVectorBundleCoreHomeomorph Z).symm p = ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩ := (rfl)

/-- A map into `(hc.sigmaVectorBundleCore Z).TotalSpace` over a continuous base map `b : Y → B` is
continuous if and only if its restriction to every clopen fibre `{y : Y // c (b y) = a}` is
continuous into `(Z a).TotalSpace`. -/
theorem continuous_mk_sigmaVectorBundleCore_iff {Y : Type*} [TopologicalSpace Y]
    (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    {b : Y → B} (hb : Continuous b) (s : Y → F) :
    Continuous (fun y => (⟨b y, s y⟩ : (hc.sigmaVectorBundleCore Z).TotalSpace)) ↔
      ∀ a : α, Continuous (fun y : {y : Y // c (b y) = a} =>
        (⟨⟨b y.val, y.property⟩, s y.val⟩ : (Z a).TotalSpace)) := by
  constructor
  · intro hs a
    apply (IsEmbedding.sigmaMk (σ := fun a => (Z a).TotalSpace)).continuous_iff.2
    convert (hc.sigmaVectorBundleCoreHomeomorph Z).symm.continuous.comp
      (hs.comp continuous_subtypeVal) using 1
    funext ⟨y, hy⟩
    cases hy
    rfl
  · intro hs
    refine continuous_of_cover_nhds (s := fun a : α => {y : Y | c (b y) = a})
      (fun y => ⟨c (b y), ((hc.isOpen_fiber (c (b y))).preimage hb).mem_nhds rfl⟩) fun a => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    exact ((hc.sigmaVectorBundleCoreHomeomorph Z).continuous.comp
      (continuous_sigmaMk.comp (hs a))).congr fun _ => rfl

end Sigma

section PointIndexed

/-- Glue point-indexed `VectorBundleCore`s on the clopen fibres of a locally constant function
`c : B → α` into a point-indexed `VectorBundleCore` on `B`. -/
noncomputable def pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) :
    VectorBundleCore R B F B :=
  (hc.sigmaVectorBundleCore Z).reindex (Equiv.sigmaFiberEquiv c).symm

/-- Chart domain of `hc.pointIndexedVectorBundleCore Z` at a base point `x : B`. -/
theorem baseSet_pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) (x : B) :
    (hc.pointIndexedVectorBundleCore Z).baseSet x =
      Subtype.val '' (Z (c x)).baseSet ⟨x, rfl⟩ := by
  rw [pointIndexedVectorBundleCore, VectorBundleCore.baseSet_reindex,
    baseSet_sigmaVectorBundleCore]
  rfl

/-- Base set of the local trivialization of `hc.pointIndexedVectorBundleCore Z` at `x : B`. -/
@[simp]
theorem localTriv_baseSet_pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) (x : B) :
    ((hc.pointIndexedVectorBundleCore Z).localTriv x).baseSet =
      Subtype.val '' ((Z (c x)).localTriv ⟨x, rfl⟩).baseSet := by
  simp only [pointIndexedVectorBundleCore, VectorBundleCore.localTriv_baseSet_reindex,
    localTriv_baseSet_sigmaVectorBundleCore]
  rfl

/-- Preferred chart index of `hc.pointIndexedVectorBundleCore Z` in terms of the fibre core. -/
@[simp]
theorem indexAt_pointIndexedVectorBundleCore_eq (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) (x : B) :
    (hc.pointIndexedVectorBundleCore Z).indexAt x = ((Z (c x)).indexAt ⟨x, rfl⟩).val := by
  simp [pointIndexedVectorBundleCore]

/-- If every fibre core satisfies `indexAt x = x`, so does `hc.pointIndexedVectorBundleCore Z`. -/
theorem indexAt_pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (hZ : ∀ a x, (Z a).indexAt x = x) (x : B) :
    (hc.pointIndexedVectorBundleCore Z).indexAt x = x := by
  simp [hZ]

/-- Transition operator of `hc.pointIndexedVectorBundleCore Z` between points on the same fibre. -/
@[simp]
theorem coordChange_pointIndexedVectorBundleCore_same (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (a : α) (i j x : {x : B // c x = a}) :
    (hc.pointIndexedVectorBundleCore Z).coordChange i.val j.val x.val =
      (Z a).coordChange i j x := by
  have hi : (Equiv.sigmaFiberEquiv c).symm i.val = ⟨a, i⟩ := by
    rcases i with ⟨i, rfl⟩; rfl
  have hj : (Equiv.sigmaFiberEquiv c).symm j.val = ⟨a, j⟩ := by
    rcases j with ⟨j, rfl⟩; rfl
  rw [pointIndexedVectorBundleCore, VectorBundleCore.coordChange_reindex, hi, hj,
    hc.coordChange_sigmaVectorBundleCore_same Z a i j x]

/-- Homeomorphism between the disjoint union of the fibre total spaces and the reconstructed total
space of `hc.pointIndexedVectorBundleCore Z`. -/
noncomputable def pointIndexedVectorBundleCoreHomeomorph (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) :
    (Σ a : α, (Z a).TotalSpace) ≃ₜ (hc.pointIndexedVectorBundleCore Z).TotalSpace :=
  (hc.sigmaVectorBundleCoreHomeomorph Z).trans
    ((hc.sigmaVectorBundleCore Z).reindexHomeomorph (Equiv.sigmaFiberEquiv c).symm)

/-- Evaluation of `pointIndexedVectorBundleCoreHomeomorph` on a fibre total-space point. -/
@[simp]
theorem pointIndexedVectorBundleCoreHomeomorph_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (p : Σ a : α, (Z a).TotalSpace) :
    hc.pointIndexedVectorBundleCoreHomeomorph Z p = ⟨p.2.proj.val, p.2.snd⟩ :=
  (hc.sigmaVectorBundleCore Z).reindexHomeomorph_apply (Equiv.sigmaFiberEquiv c).symm
    (hc.sigmaVectorBundleCoreHomeomorph Z p)

/-- Evaluation of the inverse of `pointIndexedVectorBundleCoreHomeomorph`. -/
@[simp]
theorem pointIndexedVectorBundleCoreHomeomorph_symm_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (p : (hc.pointIndexedVectorBundleCore Z).TotalSpace) :
    (hc.pointIndexedVectorBundleCoreHomeomorph Z).symm p =
      ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩ := by
  rw [Homeomorph.symm_apply_eq, pointIndexedVectorBundleCoreHomeomorph_apply]

/-- Continuity into `(hc.pointIndexedVectorBundleCore Z).TotalSpace` over a continuous base map
`b : Y → B` reduces to continuity into `(Z a).TotalSpace` on each clopen fibre
`{y : Y // c (b y) = a}`. -/
theorem continuous_mk_pointIndexedVectorBundleCore_iff {Y : Type*} [TopologicalSpace Y]
    (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    {b : Y → B} (hb : Continuous b) (s : Y → F) :
    Continuous (fun y => (⟨b y, s y⟩ : (hc.pointIndexedVectorBundleCore Z).TotalSpace)) ↔
      ∀ a : α, Continuous (fun y : {y : Y // c (b y) = a} =>
        (⟨⟨b y.val, y.property⟩, s y.val⟩ : (Z a).TotalSpace)) :=
  ((hc.sigmaVectorBundleCore Z).continuous_mk_reindex_iff _).trans
    (hc.continuous_mk_sigmaVectorBundleCore_iff Z hb s)

end PointIndexed

end IsLocallyConstant
