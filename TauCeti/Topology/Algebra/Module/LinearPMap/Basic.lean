/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Basic topological lemmas on partial linear maps

General topological lemmas on `LinearPMap` that Mathlib does not provide.

## Main results

* `LinearPMap.IsClosed.isClosed_ker`: a closed partial linear map has a closed kernel, the preimage
  of its graph under `x ↦ (x, 0)`.
-/

public section

namespace LinearPMap

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

/-- The kernel of a closed partial linear map is closed: it is the preimage of the graph under the
continuous map `x ↦ (x, 0)` (`LinearPMap.mem_ker_iff_mem_graph`). -/
theorem IsClosed.isClosed_ker {f : E →ₗ.[R] F} (hf : f.IsClosed) :
    _root_.IsClosed (f.ker : Set E) := by
  have h : (f.ker : Set E) = (fun x : E ↦ (x, (0 : F))) ⁻¹' f.graph := by
    ext x
    exact mem_ker_iff_mem_graph f
  rw [h]
  exact hf.preimage (continuous_id.prodMk continuous_const)

end LinearPMap
