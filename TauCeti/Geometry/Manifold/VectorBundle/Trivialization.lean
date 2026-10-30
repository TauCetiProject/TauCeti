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

## Main results

* `Bundle.TotalSpace.contMDiffAt_trivializationAt_snd`: the fibre coordinate in the
  trivialization at `v₀.proj` is `C^n` at `v₀`.
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
  (contMDiffAt_totalSpace.1 contMDiffAt_id).2

end Bundle.TotalSpace
