/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.Restrict

/-!
# Closedness of restrictions of partial linear maps

The restriction of a closed partial linear map to an invariant submodule is closed, because its
graph is the preimage of the original graph under the continuous inclusion `U × U → E × E`. No
closedness of the submodule itself is needed.
-/

public section

namespace LinearPMap

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E]

/-- The restriction of a closed partial linear map to an invariant submodule is closed. -/
theorem IsClosed.restrict {A : E →ₗ.[R] E} (hA : A.IsClosed) {U : Submodule R E}
    (hU : A.IsInvariant U) : (A.restrict hU).IsClosed := by
  rw [LinearPMap.IsClosed, graph_restrict, Submodule.comap_coe]
  exact hA.preimage (continuous_subtype_val.prodMap continuous_subtype_val)

end LinearPMap
