/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint
public import TauCeti.Analysis.Sobolev.W1p.Interval.PoincareFriedrichs

/-!
# Sobolev functions on `(0, 1)` vanishing at `0`

On `Ω = (0, 1)` with the boundary part `Γ = {0}`:

* for `1 ≤ p < ∞`, the coordinate `x` lies in `W^{1,p}_Γ(0, 1)`
  (`TauCeti.Examples.UnitIntervalLeftEndpoint.intervalCoord_mem_w1pVanishingOnSubmodule`), since
  its continuous representative vanishes at `0`, although it does not vanish at `1` and so is not
  in `W^{1,p}_0(0, 1)`;
* for `1 ≤ p ≤ ∞`, every `u ∈ W^{1,p}_Γ(0, 1)` satisfies `|u(x)| ≤ x^{1 - 1/p} ‖u'‖_{Lᵖ}` on
  `[0, 1]` (`TauCeti.Examples.UnitIntervalLeftEndpoint.abs_intervalRepresentativeL_le`), and
  hence the Poincaré–Friedrichs inequality `‖u‖_{Lᵖ} ≤ ‖u'‖_{Lᵖ}` with constant `1`
  (`TauCeti.Examples.UnitIntervalLeftEndpoint.norm_value_le_norm_gradient`);
* for `p = 2` the optimal constant is `2 / π`
  (`TauCeti.Examples.UnitIntervalLeftEndpoint.isLeast_norm_value_le_mul_norm_gradient`), that is,
  the best constant in `C ‖u‖²_{L²} ≤ ‖u'‖²_{L²}` is `π² / 4`
  (`TauCeti.Examples.UnitIntervalLeftEndpoint.isGreatest_mul_norm_value_sq_le_norm_gradient_sq`),
  attained by `sin (π x / 2)`.

These are the instances `a = 0`, `b = 1` of the trace characterization of `W^{1,p}_{{a}}(a, b)`
and of the Poincaré–Friedrichs inequality on an interval in
`TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint`, and of its sharp form for `p = 2` in
`TauCeti.Analysis.Sobolev.W1p.Interval.PoincareFriedrichs`.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Real

namespace TauCeti.Examples.UnitIntervalLeftEndpoint

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On `(0, 1)` the coordinate `x` lies in `W^{1,p}_{{0}}(0, 1)` for every finite `p`. -/
theorem intervalCoord_mem_w1pVanishingOnSubmodule (hp : p ≠ ⊤) :
    (W1p.intervalCoord : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p) ∈
      w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ p {0} := by
  rw [W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero hp zero_lt_one,
    W1p.intervalTraceL_intervalCoord]

/-- The coordinate `x` on `(0, 1)` is not in `W^{1,p}_0(0, 1)`, since it is `1` at `1`. -/
theorem intervalCoord_notMem_w1p0Submodule :
    (W1p.intervalCoord : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p) ∉
      w1p0Submodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ p := fun h ↦ by
  simpa using congrArg Prod.snd (W1p.intervalTraceL_eq_zero_of_mem_w1p0Submodule zero_lt_one h)

/-- On `(0, 1)`, every `u ∈ W^{1,p}_{{0}}(0, 1)` satisfies `|u(x)| ≤ x^{1 - 1/p} ‖u'‖_{Lᵖ}`. -/
theorem abs_intervalRepresentativeL_le {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p}
    (hu : u ∈ w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ p {0}) (x : Icc (0 : ℝ) 1) :
    |W1p.intervalRepresentativeL zero_lt_one u x| ≤
      (x : ℝ) ^ (1 - 1 / p.toReal) * ‖W1p.gradient u‖ := by
  simpa using W1p.abs_intervalRepresentativeL_le_of_intervalTraceL_fst_eq_zero zero_lt_one
    (W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton zero_lt_one hu) x

/-- **The Poincaré–Friedrichs constant of `(0, 1)` with `Γ = {0}` is at most `1`**: every
`u ∈ W^{1,p}_{{0}}(0, 1)` satisfies `‖u‖_{Lᵖ} ≤ ‖u'‖_{Lᵖ}`. -/
theorem norm_value_le_norm_gradient {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p}
    (hu : u ∈ w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ p {0}) :
    ‖W1p.value u‖ ≤ ‖W1p.gradient u‖ := by
  simpa using W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero zero_lt_one
    (W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton zero_lt_one hu)

/-- **The optimal `L²` Poincaré–Friedrichs constant of `(0, 1)` with `Γ = {0}` is `2 / π`**: it is
the least `C ≥ 0` with `‖u‖_{L²} ≤ C ‖u'‖_{L²}` for every `u ∈ H¹_{{0}}(0, 1)`. -/
theorem isLeast_norm_value_le_mul_norm_gradient :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 {0},
      ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖} (2 / π) := by
  simpa using W1p.isLeast_norm_value_le_mul_norm_gradient_singleton_left (zero_lt_one' ℝ)

/-- On `H¹_{{0}}(0, 1)` the best constant `C` in `C ‖u‖²_{L²} ≤ ‖u'‖²_{L²}` is `π² / 4`, the
reciprocal of the square of the optimal Poincaré–Friedrichs constant `2 / π`. -/
theorem isGreatest_mul_norm_value_sq_le_norm_gradient_sq :
    IsGreatest {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 {0},
      C * ‖W1p.value u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2} (π ^ 2 / 4) := by
  convert W1p.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_singleton_left (zero_lt_one' ℝ)
    using 1
  ring

end TauCeti.Examples.UnitIntervalLeftEndpoint
