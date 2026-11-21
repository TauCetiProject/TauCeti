/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summable real powers

A nonnegative family `f` with a summable positive power `f ^ p` tends to `0` along the cofinite
filter, since its terms are the `p`-th roots of a summable family.

## Main results

* `TauCeti.tendsto_cofinite_zero_of_summable_rpow` — a nonnegative family with a summable positive
  power tends to `0`.
-/

public section

namespace TauCeti

/-- A nonnegative family `f` with `f ^ p` summable for some `0 < p` tends to `0` along the
cofinite filter. -/
theorem tendsto_cofinite_zero_of_summable_rpow {ι : Type*} {f : ι → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (h : Summable fun i ↦ f i ^ p) :
    Filter.Tendsto f Filter.cofinite (nhds 0) := by
  have h' := h.tendsto_cofinite_zero.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.2 hp.le))
  rw [Real.zero_rpow (inv_ne_zero hp.ne')] at h'
  exact h'.congr fun i ↦ Real.rpow_rpow_inv (hf i) hp.ne'

end TauCeti
