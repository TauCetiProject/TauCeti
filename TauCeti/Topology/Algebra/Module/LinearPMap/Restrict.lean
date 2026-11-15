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

The restriction of a closed partial linear map `A : E →ₗ.[R] F` to submodules `U` of `E` and `V`
of `F` is closed, because its graph is the preimage of the original graph under the continuous
inclusion `U × V → E × F`. No closedness of the submodules themselves is needed. In particular the
restriction of a closed partial linear map to an invariant submodule is closed.
-/

public section

namespace LinearPMap

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

/-- The restriction of a closed partial linear map to submodules of its source and target is
closed. -/
theorem IsClosed.restrict {A : E →ₗ.[R] F} (hA : A.IsClosed) {U : Submodule R E}
    {V : Submodule R F} (hUV : ∀ x : A.domain, (x : E) ∈ U → A x ∈ V) :
    (A.restrict hUV).IsClosed := by
  rw [LinearPMap.IsClosed, graph_restrict, Submodule.comap_coe]
  exact hA.preimage (continuous_subtype_val.prodMap continuous_subtype_val)

end LinearPMap
