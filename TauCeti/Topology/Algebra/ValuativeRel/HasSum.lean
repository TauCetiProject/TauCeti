/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Valuation bounds on sums of series in a valuative topology

Let `R` be a ring whose topology is induced by its valuative relation. For `γ ≠ 0` the open ball
`{z | v z < γ}` is an open, hence closed, additive subgroup of `R`. So it contains the sum of any
series, convergent along any nontrivial summation filter, all of whose terms lie in it: this is
`TauCeti.valuation_lt_of_hasSum`.
-/

public section

open ValuativeRel

namespace TauCeti

variable {R : Type*} [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-- If a series converges to `s` along a nontrivial summation filter and every term has valuation
less than the nonzero value `γ`, then `s` has valuation less than `γ`. -/
theorem valuation_lt_of_hasSum {ι : Type*} {f : ι → R} {s : R} {L : SummationFilter ι}
    [L.NeBot] (hf : HasSum f s L) (γ : (ValueGroupWithZero R)ˣ)
    (h : ∀ i, valuation R (f i) < γ) : valuation R s < γ := by
  let S := (valuation R).ltAddSubgroup γ
  refine hf.mem (s := S) (S.isClosed_of_isOpen (S.isOpen_of_mem_nhds (g := 0) ?_)) h
  exact (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨γ, fun z hz => hz⟩

end TauCeti
