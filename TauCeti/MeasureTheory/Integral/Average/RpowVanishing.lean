/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average

/-!
# Vanishing from a pointwise bound on a power average

Let `s ⊆ t` with `μ t < ∞`, and let `w ≥ 0` be in `Lᵠ` of `t`. Suppose the `p`-th power average
of `w` over `t` is controlled by `w` pointwise on `s`: `(⨍_t w^p)^{1/p} ≤ C w(x)` for almost every
`x ∈ s`. If `w` is below every `ε > 0` on subsets of `s` of positive measure, then the average
vanishes, and so `w = 0` almost everywhere on `s`. This is the step of the strong maximum
principle that turns a weak Harnack inequality into vanishing on a ball.

## Main results

* `TauCeti.ae_eq_zero_of_frequently_lt_of_ae_setAverage_rpow_le`: under the bound above, a
  nonnegative function that is essentially arbitrarily small on `s` vanishes almost everywhere on
  `s`.
-/

public section

namespace TauCeti

open _root_.MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If `w ≥ 0` in `Lᵠ` of a set `t` of finite measure satisfies the bound
`(⨍_t w^p)^{1/p} ≤ C w(x)` for almost every `x` in a subset `s ⊆ t`, with `0 < p ≤ q`, and `w` is
below every `ε > 0` on a subset of `s` of positive measure, then `w = 0` almost everywhere on
`s`. -/
theorem ae_eq_zero_of_frequently_lt_of_ae_setAverage_rpow_le {s t : Set α} {p C : ℝ}
    {q : ℝ≥0∞} {w : α → ℝ} (hst : s ⊆ t) (ht : μ t ≠ ⊤) (hp : 0 < p)
    (hpq : ENNReal.ofReal p ≤ q) (hw : MemLp w q (μ.restrict t))
    (hw0 : ∀ᵐ x ∂μ.restrict t, 0 ≤ w x)
    (hH : ∀ᵐ x ∂μ.restrict s, (⨍ z in t, w z ^ p ∂μ) ^ p⁻¹ ≤ C * w x)
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂μ.restrict s, w x < ε) :
    ∀ᵐ x ∂μ.restrict s, w x = 0 := by
  have hs0 : μ s ≠ 0 := fun hs => by
    simpa [Measure.restrict_eq_zero.2 hs] using hfreq 1 one_pos
  have hA0 : 0 ≤ ⨍ x in t, w x ^ p ∂μ :=
    average_nonneg_of_ae (hw0.mono fun x hx => Real.rpow_nonneg hx _)
  -- Since `w` is essentially as small as we like on `s`, the average vanishes.
  have hA : (⨍ x in t, w x ^ p ∂μ) ^ p⁻¹ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hC : 0 < |C| + 1 := by positivity
    obtain ⟨x, hx1, hx2, hx3⟩ := ((hfreq (ε / (|C| + 1)) (div_pos hε hC)).and_eventually
      (hH.and (ae_restrict_of_ae_restrict_of_subset hst hw0))).exists
    calc _ ≤ C * w x := hx2
      _ ≤ (|C| + 1) * w x := by gcongr; linarith [le_abs_self C]
      _ ≤ (|C| + 1) * (ε / (|C| + 1)) := by gcongr
      _ = 0 + ε := by field_simp; ring
  have havg : ⨍ x in t, w x ^ p ∂μ = 0 :=
    (Real.rpow_eq_zero hA0 (inv_ne_zero hp.ne')).1 (hA.antisymm (Real.rpow_nonneg hA0 _))
  exact ae_restrict_of_ae_restrict_of_subset hst (ae_eq_zero_of_setAverage_rpow_eq_zero hp hpq
    (fun h => hs0 (measure_mono_null hst h)) ht hw hw0 havg)

end TauCeti
