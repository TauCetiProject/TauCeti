/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Hom

/-!+# Reconstructing sections in a vector-bundle frame

A field of model vectors determines a section through the inverse of an atlas trivialization.
The section has the regularity of that field on the frame domain. For Hom bundles, this is
the inverse coordinate conjugation, with no algebraic condition on the field.
-/

public noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

namespace Bundle.Trivialization

variable {𝕜 M F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [e.IsLinear 𝕜]

/-- Reconstruct a section from its model coordinates in a chosen frame. -/
def sectionFromCoordinates (A : M → F) (x : M) : V x := e.symmL 𝕜 x (A x)

/-- Evaluate the reconstructed section through the native inverse frame map. -/
@[simp]
theorem sectionFromCoordinates_apply (A : M → F) (x : M) :
    sectionFromCoordinates (𝕜 := 𝕜) e A x = e.symmL 𝕜 x (A x) := by rfl

/-- Reading the reconstructed section in the same frame recovers the model field. -/
theorem continuousLinearMapAt_sectionFromCoordinates (A : M → F) {x : M}
    (hx : x ∈ e.baseSet) :
    e.continuousLinearMapAt 𝕜 x (sectionFromCoordinates (𝕜 := 𝕜) e A x) = A x := by
  rw [sectionFromCoordinates_apply, e.continuousLinearMapAt_symmL hx]

/-- Reconstructing the coordinates of a section recovers it on the frame domain. -/
theorem sectionFromCoordinates_continuousLinearMapAt (s : ∀ x, V x) {x : M}
    (hx : x ∈ e.baseSet) :
    sectionFromCoordinates (𝕜 := 𝕜) e (fun y ↦ e.continuousLinearMapAt 𝕜 y (s y)) x = s x := by
  rw [sectionFromCoordinates_apply, e.symmL_continuousLinearMapAt hx]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] [MemTrivializationAtlas e]

/-- A reconstructed section has the regularity of its coordinates on the frame domain. -/
theorem contMDiffOn_sectionFromCoordinates (A : M → F)
    (hA : ContMDiffOn I 𝓘(𝕜, F) n A e.baseSet) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (sectionFromCoordinates (𝕜 := 𝕜) e A x)) e.baseSet := by
  intro x hx
  apply ((e.contMDiffAt_section_iff hx).2 ?_).contMDiffWithinAt
  refine (hA.contMDiffAt (e.open_baseSet.mem_nhds hx)).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hy,
    continuousLinearMapAt_sectionFromCoordinates (𝕜 := 𝕜) e A hy]

/-- A globally covering frame reconstructs a global section of the same regularity. -/
theorem contMDiff_sectionFromCoordinates (he : e.baseSet = univ) (A : M → F)
    (hA : ContMDiff I 𝓘(𝕜, F) n A) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (sectionFromCoordinates (𝕜 := 𝕜) e A x)) := by
  rw [← contMDiffOn_univ, ← he]
  exact contMDiffOn_sectionFromCoordinates (𝕜 := 𝕜) e A hA.contMDiffOn

end Bundle.Trivialization
