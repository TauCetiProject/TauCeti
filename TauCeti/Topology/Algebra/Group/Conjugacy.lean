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

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

/-- In a compact Hausdorff topological group, the set of conjugate pairs is closed. -/
theorem isClosed_isConj_pair : IsClosed {q : G × G | IsConj q.1 q.2} := by
  let f : G × G → G × G := fun q ↦ (q.2, q.1 * q.2 * q.1⁻¹)
  have hf : Continuous f := continuous_snd.prodMk IsTopologicalGroup.continuous_conj_prod
  have hrange : Set.range f = {q : G × G | IsConj q.1 q.2} := by
    ext q
    constructor
    · rintro ⟨⟨g, x⟩, rfl⟩
      exact isConj_iff.mpr ⟨g, rfl⟩
    · intro h
      obtain ⟨g, hg⟩ := isConj_iff.mp h
      exact ⟨(g, q.1), Prod.ext rfl hg⟩
  rw [← hrange]
  exact (isCompact_range hf).isClosed

end TauCeti
