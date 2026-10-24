/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Fixed-scalar continuity on submodule quotients

Multiplication by a fixed scalar descends continuously to a submodule quotient with its
quotient topology. This requires no topology on the scalar ring and no continuity of addition.
-/

public section

namespace TauCeti

/-- Multiplication by a fixed scalar remains continuous on a submodule quotient. -/
instance instContinuousConstSMulSubmoduleQuotient {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [ContinuousConstSMul R M] (S : Submodule R M) :
    ContinuousConstSMul R (M ⧸ S) where
  continuous_const_smul r := S.isQuotientMap_mkQ.continuous_iff.2 <| by
    simpa only [Function.comp_def, map_smul] using
      S.continuous_mkQ.comp (continuous_const_smul r)

end TauCeti
