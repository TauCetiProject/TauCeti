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
trivialization at the base point `v₀.proj`. This file records the two facts that make such a
reading usable locally: points near `v₀` lie over the base set of that trivialization, and, for
a `C^n` model of the total space, their fibre coordinate in it is `C^n` at `v₀`.

## Main results

* `TauCeti.FiberBundle.eventually_proj_mem_baseSet_trivializationAt`: near `v₀`, points lie
  over the base set of the trivialization at `v₀.proj`.
* `TauCeti.FiberBundle.contMDiffAt_trivializationAt_snd`: the fibre coordinate in the
  trivialization at `v₀.proj` is `C^n` at `v₀`.
-/

public section

open Bundle Filter
open scoped Manifold Topology

namespace TauCeti.FiberBundle

section Topology

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- Near a point `v₀` of the total space, every point lies over the base set of the
trivialization at `v₀.proj`. -/
theorem eventually_proj_mem_baseSet_trivializationAt (v₀ : TotalSpace F E) :
    ∀ᶠ v in 𝓝 v₀, v.proj ∈ (trivializationAt F E v₀.proj).baseSet :=
  (_root_.FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    ((trivializationAt F E v₀.proj).open_baseSet.mem_nhds
      (_root_.FiberBundle.mem_baseSet_trivializationAt' v₀.proj))

end Topology

section Manifold

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E]

/-- The fibre coordinate in the trivialization at `v₀.proj` is `C^n` at `v₀`. -/
theorem contMDiffAt_trivializationAt_snd (v₀ : TotalSpace F E) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun v ↦ (trivializationAt F E v₀.proj v).2) v₀ :=
  (contMDiffAt_totalSpace.1 contMDiffAt_id).2

end Manifold

end TauCeti.FiberBundle
