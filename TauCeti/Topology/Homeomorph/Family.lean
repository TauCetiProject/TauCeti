/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Inverses of continuous families of equivalences

For a family of equivalences from a compact space to a Hausdorff space, joint continuity of
forward evaluation implies joint continuity of inverse evaluation. This is the parametric form of
Mathlib's `Continuous.continuous_symm_of_equiv_compact_to_t2`; in particular it applies to
families of homeomorphisms. It allows inverse points to vary continuously without imposing a
topology on the type of equivalences itself. The proof uses Mathlib's compact-codomain
closed-graph criterion `continuous_of_isClosed_graph`.
-/

public section

namespace TauCeti

/-- Inverse evaluation is jointly continuous for a family of equivalences from a compact space
to a Hausdorff space whose forward evaluation is jointly continuous. The parameter space is
arbitrary. -/
theorem continuous_equiv_symm_eval {P X Y : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (e : P → X ≃ Y)
    (he : Continuous fun p : P × X ↦ e p.1 p.2) :
    Continuous fun p : P × Y ↦ (e p.1).symm p.2 := by
  refine continuous_of_isClosed_graph ?_
  have hgraph : Function.graph (fun p : P × Y ↦ (e p.1).symm p.2) =
      {q | e q.1.1 q.2 = q.1.2} := by
    ext ⟨⟨p, y⟩, x⟩
    exact (e p).symm_apply_eq.trans eq_comm
  rw [hgraph]
  exact isClosed_eq (by fun_prop) (by fun_prop)

end TauCeti
