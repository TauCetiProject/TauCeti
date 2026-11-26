/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.VanishingOn

/-!
# Sobolev functions on `(0, 1)` vanishing at the midpoint

On `Ω = (0, 1)` with `Γ = {1/2}`, a set that meets `Ω` rather than lying on its boundary:

* for `1 ≤ p ≤ ∞`, every `u ∈ W^{1,p}_Γ(0, 1)` has continuous representative vanishing at `1/2`
  (`TauCeti.Examples.UnitIntervalMidpoint.intervalRepresentativeL_eq_zero_of_mem`), since every
  generator vanishes near `1/2`;
* `W^{1,p}_0(0, 1)` is not contained in `W^{1,p}_Γ(0, 1)`
  (`TauCeti.Examples.UnitIntervalMidpoint.not_w1p0Submodule_le_w1pVanishingOnSubmodule`): a smooth
  bump supported in `(0, 1)` with value `1` at `1/2` lies in the first space but not in the second.

So the inclusion `W^{1,p}_0(Ω) ⊆ W^{1,p}_Γ(Ω)` of `TauCeti.w1p0Submodule_le_w1pVanishingOnSubmodule`
needs `Γ` to miss `Ω`. These are the instances `a = 0`, `b = 1`, `Γ = {1/2}` of
`TauCeti.Analysis.Sobolev.W1p.Interval.VanishingOn`.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti.Examples.UnitIntervalMidpoint

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every `u ∈ W^{1,p}_{{1/2}}(0, 1)` has continuous representative vanishing at `1/2`, for every
`1 ≤ p ≤ ∞`. -/
theorem intervalRepresentativeL_eq_zero_of_mem {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p}
    (hu : u ∈ w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ p {1 / 2}) :
    W1p.intervalRepresentativeL zero_lt_one u ⟨1 / 2, by norm_num⟩ = 0 :=
  W1p.intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule zero_lt_one hu
    (subset_closure (mem_singleton _))

/-- `W^{1,p}_0(0, 1)` is not contained in `W^{1,p}_{{1/2}}(0, 1)`, for every `1 ≤ p ≤ ∞`, since
`{1/2}` meets `(0, 1)`. -/
theorem not_w1p0Submodule_le_w1pVanishingOnSubmodule :
    ¬ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p ≤
      w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ p {1 / 2} := by
  rw [W1p.w1p0Submodule_Ioo_le_w1pVanishingOnSubmodule_iff, disjoint_singleton_left]
  norm_num

end TauCeti.Examples.UnitIntervalMidpoint
