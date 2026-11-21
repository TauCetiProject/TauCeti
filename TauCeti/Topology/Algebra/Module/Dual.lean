/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Dense range of evaluation against linearly independent dual families

For a `K`-linearly independent family `f : ι → (V →ₗ[K] K)` over a field `K` equipped with any
topology, the product map `LinearMap.pi f : V →ₗ[K] (ι → K)` surjects onto every finite
subfamily of coordinates and hence has dense range (`LinearIndependent.denseRange_pi`).
-/

public section

open Filter Topology

namespace LinearIndependent

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {f : ι → (V →ₗ[K] K)}

/-- Evaluation against any `K`-linearly independent family of linear forms `V →ₗ[K] K` has dense
range in `ι → K` for any topology on `K`. -/
theorem denseRange_pi [TopologicalSpace K] (hf : LinearIndependent K f) :
    DenseRange (LinearMap.pi f) := fun y ↦ mem_closure_iff_nhds.mpr fun W hW ↦ by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨s, t, ht, hst⟩ := hW
  obtain ⟨v, hv⟩ := (hf.comp Subtype.val Subtype.val_injective).pi_surjective fun i : s ↦ y i.val
  refine ⟨LinearMap.pi f v, hst fun i hi ↦ ?_, v, rfl⟩
  rw [LinearMap.pi_apply, show f i v = y i by simpa [LinearMap.pi_apply] using congr_fun hv ⟨i, hi⟩]
  exact mem_of_mem_nhds (ht i)

end Field

end LinearIndependent
