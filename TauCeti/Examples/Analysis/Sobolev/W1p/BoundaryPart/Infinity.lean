/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Infinity
public import TauCeti.Analysis.Sobolev.W1p.Interval.Trace

/-!
# Example: `x ∉ W^{1,∞}_{{0}}(0, 1)`

On `(0, 1)` with `Γ = {0}`, every generator of `W^{1,∞}_Γ(0, 1)` has derivative `0` near `0`,
while `u(x) = x` has `u' = 1`; so `u` is at `W^{1,∞}` distance at least `1` from
`W^{1,∞}_Γ(0, 1)` and does not lie in it, although its trace `u(0)` is `0`. Thus the kernel of
the trace at `0` is not contained in `W^{1,∞}_Γ(0, 1)`.
-/

public section

open MeasureTheory Set TauCeti TauCeti.W1p
open scoped ENNReal

namespace TauCeti.W1pVanishingOnInfinityExamples

/-- `x` vanishes at `0`, but is at `W^{1,∞}` distance at least `1` from `W^{1,∞}_{{0}}(0, 1)`,
and not in it. -/
example : (intervalTraceL zero_lt_one (intervalCoord (a := 0) (b := 1) (p := ⊤))).1 = 0 ∧
    (∀ v ∈ w1pVanishingOnSubmodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤ {0},
      1 ≤ dist (intervalCoord (a := 0) (b := 1) (p := ⊤)) v) ∧
    intervalCoord (a := 0) (b := 1) (p := ⊤) ∉
      w1pVanishingOnSubmodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤ {0} := by
  have hdist (v) (hv : v ∈ w1pVanishingOnSubmodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤ {0}) :
      1 ≤ dist (intervalCoord (a := 0) (b := 1) (p := ⊤)) v := by
    simpa using abs_gradient_le_dist_of_mem_w1pVanishingOnSubmodule zero_lt_one
      (g := fun _ ↦ 1) continuousOn_const gradient_intervalCoord hv
      (left_mem_Icc.2 zero_le_one) (subset_closure rfl)
  exact ⟨by simp [intervalTraceL_intervalCoord], hdist,
    fun h ↦ one_ne_zero (gradient_eq_zero_of_mem_w1pVanishingOnSubmodule zero_lt_one
      (g := fun _ ↦ (1 : ℝ)) continuousOn_const gradient_intervalCoord h
      (left_mem_Icc.2 zero_le_one) (subset_closure rfl))⟩

end TauCeti.W1pVanishingOnInfinityExamples
