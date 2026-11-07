/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Closedness of conjugacy in compact groups

For a compact Hausdorff topological group, conjugacy is a closed relation on the product.
The binary form allows both elements to vary, as needed when imposing conjugacy conditions
on a family of group elements.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

/-- In a compact Hausdorff topological group, the set of conjugate pairs is closed. -/
theorem isClosed_isConj_prod : IsClosed {q : G × G | IsConj q.1 q.2} := by
  have h : {q : G × G | IsConj q.1 q.2} = Set.range fun p : G × G ↦ (p.2, p.1 * p.2 * p.1⁻¹) := by
    ext ⟨a, b⟩
    simp [isConj_iff]
  rw [h]
  exact (isCompact_range (continuous_snd.prodMk IsTopologicalGroup.continuous_conj_prod)).isClosed

end TauCeti
