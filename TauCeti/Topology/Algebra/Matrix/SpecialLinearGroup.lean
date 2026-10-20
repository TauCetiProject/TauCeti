/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Convergence in special linear groups

The special linear group `SL(n, R)` carries the topology induced from the matrices, which is the
product topology on the entries. So a sequence, or more generally a function along any filter,
converges in `SL(n, R)` exactly when each of its entries converges.

## Main results

* `Matrix.SpecialLinearGroup.tendsto_iff_tendsto_apply`: convergence in `SL(n, R)` is entrywise
  convergence.
-/

public section

open Filter Topology

namespace Matrix.SpecialLinearGroup

variable {n R α : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]

/-- Convergence in `SL(n, R)` is entrywise convergence. -/
theorem tendsto_iff_tendsto_apply {l : Filter α} {M : α → SpecialLinearGroup n R}
    {D : SpecialLinearGroup n R} :
    Tendsto M l (𝓝 D) ↔ ∀ i j, Tendsto (fun x ↦ M x i j) l (𝓝 (D i j)) := by
  have hind : IsInducing ((↑) : SpecialLinearGroup n R → Matrix n n R) := ⟨rfl⟩
  exact hind.tendsto_nhds_iff.trans <|
    tendsto_pi_nhds.trans <| forall_congr' fun _ ↦ tendsto_pi_nhds

end Matrix.SpecialLinearGroup
