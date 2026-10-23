/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Inverses of continuous families of homeomorphisms

For a family of homeomorphisms with compact source and Hausdorff target, joint continuity of
forward evaluation implies joint continuity of inverse evaluation. This allows inverse points
to vary continuously without imposing a topology on the type of homeomorphisms itself.
The proof uses Mathlib's compact-codomain closed-graph criterion
`continuous_of_isClosed_graph`.
-/

public section

namespace TauCeti

open Topology

/-- Inverse evaluation is jointly continuous for a continuous family of homeomorphisms from a
compact space to a Hausdorff space. The parameter space is arbitrary. -/
theorem continuous_homeomorph_symm_eval {P X Y : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (e : P → X ≃ₜ Y)
    (he : Continuous fun p : P × X ↦ e p.1 p.2) :
    Continuous fun p : P × Y ↦ (e p.1).symm p.2 := by
  apply continuous_of_isClosed_graph
  have hclosed := isClosed_eq
    (he.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    (continuous_snd.comp continuous_fst)
  convert hclosed using 1
  ext p
  simp only [Function.graph, Set.mem_ofPred_eq, Function.comp_apply]
  exact (e p.1.1).symm_apply_eq.trans eq_comm

end TauCeti
