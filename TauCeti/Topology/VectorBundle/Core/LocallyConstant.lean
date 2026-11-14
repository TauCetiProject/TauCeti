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

open Bundle Set Topology

namespace IsLocallyConstant

variable {R B F α : Type*} [NontriviallyNormedField R] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace R F]
  {ι : α → Type*} {c : B → α}

section Sigma

/-- Helper extracting the fibre membership and chart membership from an image chart in `B`. -/
private theorem mem_image_baseSet_iff
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (i : ι a) (x : B) :
    x ∈ Subtype.val '' (Z a).baseSet i ↔
      ∃ hx : c x = a, (⟨x, hx⟩ : {y : B // c y = a}) ∈ (Z a).baseSet i := by
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact ⟨hy, hmem⟩
  · rintro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

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
      if hq : p.1 = q.1 then
        (Z p.1).coordChange p.2 (hq ▸ q.2) ⟨x, hp⟩
      else
        ContinuousLinearMap.id R F
    else
      ContinuousLinearMap.id R F
  coordChange_self p x hx v := by
    rcases p with ⟨a, i⟩
    obtain ⟨hxa, hxi⟩ := (mem_image_baseSet_iff Z a i x).1 hx
    subst hxa
    simp [(Z (c x)).coordChange_self i ⟨x, rfl⟩ hxi v]
  continuousOn_coordChange p q := by
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, j⟩
    by_cases hab : a = b
    · subst hab
      rw [continuousOn_iff_continuous_domRestrict]
      let f : ↥((Subtype.val '' (Z a).baseSet i) ∩ (Subtype.val '' (Z a).baseSet j)) →
          {y : B // c y = a} :=
        fun x => ⟨x.1, ((mem_image_baseSet_iff Z a i x.1).1 x.2.1).choose⟩
      have hf : Continuous f := continuous_subtype_val.subtype_mk _
      have hf_mem : ∀ x, f x ∈ (Z a).baseSet i ∩ (Z a).baseSet j := fun x => by
        obtain ⟨_, hi⟩ := (mem_image_baseSet_iff Z a i x.1).1 x.2.1
        obtain ⟨_, hj⟩ := (mem_image_baseSet_iff Z a j x.1).1 x.2.2
        exact ⟨hi, hj⟩
      refine (((Z a).continuousOn_coordChange i j).comp_continuous hf hf_mem).congr fun x => ?_
      dsimp only [Function.comp_apply, Set.domRestrict]
      rw [dite_eq_left (f x).2, dite_eq_left rfl]
    · refine (continuousOn_const (c := ContinuousLinearMap.id R F)).congr fun x _ => ?_
      by_cases hx : c x = a <;> simp [hx, hab]
  coordChange_comp p q r x hx v := by
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, j⟩
    rcases r with ⟨d, k⟩
    obtain ⟨ha, hi⟩ := (mem_image_baseSet_iff Z a i x).1 hx.1.1
    obtain ⟨hb, hj⟩ := (mem_image_baseSet_iff Z b j x).1 hx.1.2
    obtain ⟨hd, hk⟩ := (mem_image_baseSet_iff Z d k x).1 hx.2
    subst ha
    have hba : b = c x := hb.symm
    have hda : d = c x := hd.symm
    subst hba hda
    simp [(Z (c x)).coordChange_comp i j k ⟨x, rfl⟩ ⟨⟨hi, hj⟩, hk⟩ v]

theorem baseSet_sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) (p : Σ a : α, ι a) :
    (hc.sigmaVectorBundleCore Z).baseSet p = Subtype.val '' (Z p.1).baseSet p.2 := (rfl)

@[simp]
theorem localTriv_baseSet_sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) (p : Σ a : α, ι a) :
    ((hc.sigmaVectorBundleCore Z).localTriv p).baseSet =
      Subtype.val '' ((Z p.1).localTriv p.2).baseSet := (rfl)

@[simp]
theorem indexAt_sigmaVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) (x : B) :
    (hc.sigmaVectorBundleCore Z).indexAt x = ⟨c x, (Z (c x)).indexAt ⟨x, rfl⟩⟩ := (rfl)

theorem indexAt_sigmaVectorBundleCore_coe (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (x : {x : B // c x = a}) :
    (hc.sigmaVectorBundleCore Z).indexAt x.1 = ⟨a, (Z a).indexAt x⟩ := by
  rcases x with ⟨x, hx⟩
  cases hx
  rfl

@[simp]
theorem coordChange_sigmaVectorBundleCore_same (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (i j : ι a) (x : {x : B // c x = a}) :
    (hc.sigmaVectorBundleCore Z).coordChange ⟨a, i⟩ ⟨a, j⟩ x.1 =
      (Z a).coordChange i j x := by
  rcases x with ⟨x, hx⟩
  cases hx
  simp [sigmaVectorBundleCore]

/-- On each clopen fibre `c ⁻¹' {a}`, the preferred trivialization of the glued core agrees with
the preferred trivialization of `Z a`. -/
theorem localTrivAt_sigmaVectorBundleCore_snd (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (a : α) (x₀ x : {x : B // c x = a}) (v : F) :
    ((hc.sigmaVectorBundleCore Z).localTrivAt x₀.1 ⟨x.1, v⟩).2 =
      ((Z a).localTrivAt x₀ ⟨x, v⟩).2 := by
  simp only [← VectorBundleCore.localTrivAt_def, VectorBundleCore.localTriv_apply,
    hc.indexAt_sigmaVectorBundleCore_coe Z a x, hc.indexAt_sigmaVectorBundleCore_coe Z a x₀,
    hc.coordChange_sigmaVectorBundleCore_same Z a _ _ x]

/-- The disjoint union of the fibre total spaces `(Z a).TotalSpace` is homeomorphic over `B` to the
reconstructed total space of `hc.sigmaVectorBundleCore Z`. -/
noncomputable def sigmaVectorBundleCoreHomeomorph (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a)) :
    (Σ a : α, (Z a).TotalSpace) ≃ₜ (hc.sigmaVectorBundleCore Z).TotalSpace where
  toFun p := ⟨p.2.proj.1, p.2.2⟩
  invFun p := ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩
  left_inv := by
    rintro ⟨a, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv := by
    rintro ⟨x, v⟩
    rfl
  continuous_toFun := by
    refine continuous_sigma fun a => continuous_iff_continuousAt.2 fun p₀ => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    have hp₀ := (FiberBundle.continuousAt_totalSpace _ _).1
      ((continuous_id (X := (Z a).TotalSpace)).continuousAt (x := p₀))
    refine ⟨(continuous_subtype_val.comp (Z a).continuous_proj).continuousAt, ?_⟩
    convert hp₀.2 using 1
    funext p
    simp only [id_eq, VectorBundleCore.trivializationAt]
    exact hc.localTrivAt_sigmaVectorBundleCore_snd Z a p₀.proj p.proj p.2
  continuous_invFun := by
    apply continuous_of_cover_nhds
      (s := fun a : α => {p : (hc.sigmaVectorBundleCore Z).TotalSpace | c p.proj = a})
    · intro p
      exact ⟨c p.proj,
        ((hc.isOpen_fiber (c p.proj)).preimage
          (hc.sigmaVectorBundleCore Z).continuous_proj).mem_nhds rfl⟩
    · intro a
      rw [continuousOn_iff_continuous_domRestrict]
      have hsub : Continuous fun q :
          {p : (hc.sigmaVectorBundleCore Z).TotalSpace // c p.proj = a} =>
          (⟨⟨q.1.proj, q.2⟩, q.1.2⟩ : (Z a).TotalSpace) := by
        refine continuous_iff_continuousAt.2 fun q₀ => ?_
        rw [FiberBundle.continuousAt_totalSpace]
        have hq₀ := (FiberBundle.continuousAt_totalSpace _ _).1
          (continuous_subtype_val.continuousAt (x := q₀))
        refine ⟨(((hc.sigmaVectorBundleCore Z).continuous_proj.comp
          continuous_subtype_val).subtype_mk _).continuousAt, ?_⟩
        convert hq₀.2 using 1
        funext q
        simp only [VectorBundleCore.trivializationAt]
        exact (hc.localTrivAt_sigmaVectorBundleCore_snd Z a ⟨q₀.1.proj, q₀.2⟩
          ⟨q.1.proj, q.2⟩ q.1.2).symm
      refine (continuous_sigmaMk.comp hsub).congr fun q => ?_
      rcases q with ⟨⟨x, v⟩, hx⟩
      cases hx
      rfl

@[simp]
theorem sigmaVectorBundleCoreHomeomorph_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (p : Σ a : α, (Z a).TotalSpace) :
    hc.sigmaVectorBundleCoreHomeomorph Z p = ⟨p.2.proj.1, p.2.2⟩ := (rfl)

@[simp]
theorem sigmaVectorBundleCoreHomeomorph_symm_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    (p : (hc.sigmaVectorBundleCore Z).TotalSpace) :
    (hc.sigmaVectorBundleCoreHomeomorph Z).symm p = ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := (rfl)

/-- A map into `(hc.sigmaVectorBundleCore Z).TotalSpace` over a continuous base map `b : Y → B` is
continuous if and only if its restriction to every clopen fibre `{y : Y // c (b y) = a}` is
continuous into `(Z a).TotalSpace`. -/
theorem continuous_mk_sigmaVectorBundleCore_iff {Y : Type*} [TopologicalSpace Y]
    (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F (ι a))
    {b : Y → B} (hb : Continuous b) (s : Y → F) :
    Continuous (fun y => (⟨b y, s y⟩ : (hc.sigmaVectorBundleCore Z).TotalSpace)) ↔
      ∀ a : α, Continuous (fun y : {y : Y // c (b y) = a} =>
        (⟨⟨b y.1, y.2⟩, s y.1⟩ : (Z a).TotalSpace)) := by
  constructor
  · intro hs a
    apply (IsEmbedding.sigmaMk (σ := fun a => (Z a).TotalSpace)).continuous_iff.2
    convert (hc.sigmaVectorBundleCoreHomeomorph Z).symm.continuous.comp
      (hs.comp continuous_subtype_val) using 1
    funext ⟨y, hy⟩
    cases hy
    rfl
  · intro hs
    apply continuous_of_cover_nhds (s := fun a : α => {y : Y | c (b y) = a})
    · intro y
      exact ⟨c (b y), ((hc.isOpen_fiber (c (b y))).preimage hb).mem_nhds rfl⟩
    · intro a
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

theorem baseSet_pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) (x : B) :
    (hc.pointIndexedVectorBundleCore Z).baseSet x =
      Subtype.val '' (Z (c x)).baseSet ⟨x, rfl⟩ := by
  rw [pointIndexedVectorBundleCore, VectorBundleCore.baseSet_reindex,
    baseSet_sigmaVectorBundleCore]
  rfl

@[simp]
theorem localTriv_baseSet_pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) (x : B) :
    ((hc.pointIndexedVectorBundleCore Z).localTriv x).baseSet =
      Subtype.val '' ((Z (c x)).localTriv ⟨x, rfl⟩).baseSet := by
  simp only [pointIndexedVectorBundleCore, VectorBundleCore.localTriv_baseSet_reindex,
    localTriv_baseSet_sigmaVectorBundleCore]
  rfl

@[simp]
theorem indexAt_pointIndexedVectorBundleCore_eq (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a}) (x : B) :
    (hc.pointIndexedVectorBundleCore Z).indexAt x = ((Z (c x)).indexAt ⟨x, rfl⟩).1 := by
  simp [pointIndexedVectorBundleCore]

theorem indexAt_pointIndexedVectorBundleCore (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (hZ : ∀ a x, (Z a).indexAt x = x) (x : B) :
    (hc.pointIndexedVectorBundleCore Z).indexAt x = x := by
  simp [hZ]

@[simp]
theorem coordChange_pointIndexedVectorBundleCore_same (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (a : α) (i j x : {x : B // c x = a}) :
    (hc.pointIndexedVectorBundleCore Z).coordChange i.1 j.1 x.1 =
      (Z a).coordChange i j x := by
  have hi : (Equiv.sigmaFiberEquiv c).symm i.1 = ⟨a, i⟩ := by
    rcases i with ⟨i, rfl⟩; rfl
  have hj : (Equiv.sigmaFiberEquiv c).symm j.1 = ⟨a, j⟩ := by
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

@[simp]
theorem pointIndexedVectorBundleCoreHomeomorph_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (p : Σ a : α, (Z a).TotalSpace) :
    hc.pointIndexedVectorBundleCoreHomeomorph Z p = ⟨p.2.proj.1, p.2.2⟩ :=
  (hc.sigmaVectorBundleCore Z).reindexHomeomorph_apply (Equiv.sigmaFiberEquiv c).symm
    (hc.sigmaVectorBundleCoreHomeomorph Z p)

@[simp]
theorem pointIndexedVectorBundleCoreHomeomorph_symm_apply (hc : IsLocallyConstant c)
    (Z : ∀ a : α, VectorBundleCore R {x : B // c x = a} F {x : B // c x = a})
    (p : (hc.pointIndexedVectorBundleCore Z).TotalSpace) :
    (hc.pointIndexedVectorBundleCoreHomeomorph Z).symm p =
      ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := by
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
        (⟨⟨b y.1, y.2⟩, s y.1⟩ : (Z a).TotalSpace)) :=
  ((hc.sigmaVectorBundleCore Z).continuous_mk_reindex_iff _).trans
    (hc.continuous_mk_sigmaVectorBundleCore_iff Z hb s)

end PointIndexed

end IsLocallyConstant
