/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.UnitInterval

/-!
# The unit interval is contractible

The unit interval `[0, 1]` is a convex subset of `ℝ`, so it is contractible.
-/

public section

namespace unitInterval

/-- The unit interval is contractible, as a convex subset of `ℝ`. -/
instance contractibleSpace : ContractibleSpace unitInterval :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩

end unitInterval
