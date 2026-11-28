/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import TauCeti.Order.Lattice.Submodular

/-!
# Scalar multiplication of submodular functions

Nonnegative scalar multiplication preserves the submodular inequality because it is order
preserving and distributes over addition.
-/

public section

namespace TauCeti.IsSubmodular

variable {K L : Type*}

/-- Pointwise multiplication by a nonnegative scalar preserves submodularity. -/
theorem smul {R : Type*} [Zero R] [Preorder R] [AddZeroClass K] [Preorder K]
    [DistribSMul R K] [PosSMulMono R K] [Lattice L] {f : L → K} (hf : IsSubmodular f)
    {c : R} (hc : 0 ≤ c) : IsSubmodular (c • f) := by
  rw [isSubmodular_def]
  intro a b
  simpa only [Pi.smul_apply, smul_add] using smul_le_smul_of_nonneg_left (hf.apply a b) hc

end TauCeti.IsSubmodular
