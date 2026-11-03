/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The fibre coordinate near a point of a fibre bundle

Near a point `v₀` of the total space of a fibre bundle, every point can be read in the preferred
trivialization at the base point `v₀.proj`. For a `C^n` model of the total space, the fibre
coordinate of such a point in that trivialization is `C^n` at `v₀`. That points near `v₀` lie over
the base set of the trivialization is the topological fact
`Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`.

For a vector bundle, the same reading applies to a `C^n` map from a normed space into the total
space: its fibre part, read through the linear map of the trivialization at the image of the base
point, is a `C^n` map between normed spaces there.

## Main results

* `Bundle.TotalSpace.contMDiffAt_trivializationAt_snd`: the fibre coordinate in the
  trivialization at `v₀.proj` is `C^n` at `v₀`.
* `ContMDiffAt.contDiffAt_continuousLinearMapAt_trivializationAt`: a `C^n` map from a normed space
  into the total space of a vector bundle has `C^n` fibre coordinates in the trivialization at the
  base point of its value.
-/

public section

open Bundle
open scoped Manifold

namespace Bundle.TotalSpace

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E]

/-- The fibre coordinate in the trivialization at `v₀.proj` is `C^n` at `v₀`. -/
theorem contMDiffAt_trivializationAt_snd (v₀ : TotalSpace F E) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun v ↦ (trivializationAt F E v₀.proj v).2) v₀ :=
  (contMDiffAt_totalSpace_iff.1 contMDiffAt_id).2

end Bundle.TotalSpace

namespace ContMDiffAt

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {b : G → B} {s : ∀ z, E (b z)} {z₀ : G}

/-- A `C^n` map `z ↦ (b z, s z)` from a normed space into the total space of a vector bundle has
`C^n` fibre coordinates in the trivialization at `b z₀`, read through its linear map. -/
theorem contDiffAt_continuousLinearMapAt_trivializationAt
    (h : ContMDiffAt 𝓘(𝕜, G) (IB.prod 𝓘(𝕜, F)) n (fun z ↦ TotalSpace.mk' F (b z) (s z)) z₀) :
    ContDiffAt 𝕜 n (fun z ↦ (trivializationAt F E (b z₀)).continuousLinearMapAt 𝕜 (b z) (s z))
      z₀ := by
  refine (contMDiffAt_iff_contDiffAt.mp
    (contMDiffAt_totalSpace_iff.mp h).2).congr_of_eventuallyEq ?_
  filter_upwards [(contMDiffAt_totalSpace_iff.mp h).1.continuousAt.preimage_mem_nhds
    ((trivializationAt F E (b z₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F E _))] with z hz
  exact (trivializationAt F E (b z₀)).continuousLinearMapAt_apply_of_mem (R := 𝕜) hz _

end ContMDiffAt
