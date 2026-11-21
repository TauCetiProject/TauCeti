/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Maps on one-point compactifications

The extension `OnePoint.map f` sends infinity, and only infinity, to infinity. Its range is the
range of `f`, embedded in the target compactification, together with infinity, and it is injective
exactly when `f` is injective; it is an involution when `f` is. For a proper map between
arbitrary topological spaces, this extension is continuous, and it is a closed embedding exactly
when `f` is. These lemmas allow proper parametrizations to be compactified, with an explicit
description of their range after adjoining infinity and a criterion for injectivity.
-/

public section

open Set OnePoint

namespace TauCeti

/-- Extension to one-point compactifications preserves and reflects injectivity. -/
@[simp]
theorem onePointMap_injective_iff {X Y : Type*} {f : X → Y} :
    Function.Injective (OnePoint.map f) ↔ Function.Injective f :=
  ⟨fun hf _ _ h ↦ coe_injective <| hf <| by simp [h], Option.map_injective⟩

/-- Extension to one-point compactifications preserves involutions. -/
theorem onePointMap_involutive {X : Type*} {f : X → X} (hf : Function.Involutive f) :
    Function.Involutive (OnePoint.map f) := by
  intro x
  induction x using OnePoint.rec <;> simp [hf _]

/-- The range of the extension to one-point compactifications is the embedded range together
with the point at infinity. -/
@[simp]
theorem range_onePointMap {X Y : Type*} (f : X → Y) :
    range (OnePoint.map f) = insert ∞ (((↑) : Y → OnePoint Y) '' range f) := by
  -- `Option.range_eq` splits the domain into infinity and the finite points.
  exact (Option.range_eq (OnePoint.map f)).trans
    (congrArg (insert ∞) (range_comp ((↑) : Y → OnePoint Y) f))

/-- Infinity is the only point that the extension to one-point compactifications sends to
infinity. -/
@[simp]
theorem preimage_onePointMap_infty {X Y : Type*} (f : X → Y) :
    OnePoint.map f ⁻¹' {∞} = {∞} := by
  ext x
  induction x using OnePoint.rec <;> simp

/-- A proper map between arbitrary topological spaces extends continuously
to the one-point compactifications, sending infinity to infinity. -/
theorem continuous_onePointMap_of_isProperMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) : Continuous (OnePoint.map f) :=
  continuous_map hf.continuous <| Filter.hasBasis_coclosedCompact.tendsto_right_iff.2
    fun _ hK ↦ (hf.isCompact_preimage hK.2).compl_mem_coclosedCompact_of_isClosed
      (hK.1.preimage hf.continuous)

/-- Extension to one-point compactifications preserves and reflects closed embeddings between
arbitrary topological spaces. -/
@[simp]
theorem isClosedEmbedding_onePointMap_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} :
    Topology.IsClosedEmbedding (OnePoint.map f) ↔ Topology.IsClosedEmbedding f := by
  -- The finite part of an image under `OnePoint.map f` is the image of the finite part.
  have hpre (s : Set (OnePoint X)) :
      ((↑) : Y → OnePoint Y) ⁻¹' (OnePoint.map f '' s) = f '' ((↑) ⁻¹' s) := by
    ext y
    simp [OnePoint.exists]
  refine ⟨fun h ↦ .of_continuous_injective_isClosedMap (continuous_map_iff.1 h.continuous).1
    (onePointMap_injective_iff.1 h.injective) fun C hC ↦ ?_, fun hf ↦
    .of_continuous_injective_isClosedMap (continuous_onePointMap_of_isProperMap hf.isProperMap)
    (onePointMap_injective_iff.2 hf.injective) fun s hs ↦ ?_⟩
  · -- Adjoining infinity to `C` gives a closed set whose image has finite part `f '' C`.
    have hpreC : ((↑) : X → OnePoint X) ⁻¹' insert ∞ ((↑) '' C) = C := by ext; simp
    have hC' : IsClosed (insert ∞ (((↑) : X → OnePoint X) '' C)) :=
      (isClosed_iff_of_mem (mem_insert _ _)).2 (by rwa [hpreC])
    have := (h.isClosedMap _ hC').preimage continuous_coe
    rwa [hpre, hpreC] at this
  · have hinfty : ∞ ∈ OnePoint.map f '' s ↔ ∞ ∈ s := by simp [OnePoint.exists]
    have hcl : IsClosed (f '' ((↑) ⁻¹' s)) := hf.isClosedMap _ (hs.preimage continuous_coe)
    by_cases h : ∞ ∈ s
    · rwa [isClosed_iff_of_mem (hinfty.2 h), hpre]
    · rw [isClosed_iff_of_notMem (hinfty.not.2 h), hpre]
      exact ⟨hcl, ((isClosed_iff_of_notMem h).1 hs).2.image hf.continuous⟩

end TauCeti
