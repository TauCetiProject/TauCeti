/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Exponential moments of bounded functions by slabs of the range

Let `f : X → ℝ` satisfy `|f| ≤ M`, and let `δ > 0`. Splitting the range `[-M, M]` of `f` into
finitely many superlevel slabs `{c k ≤ f}` with lower edges `c k = -M + k δ` bounds the
exponential moment `∫⁻ exp (f / e) dν` by a finite sum of `exp ((c k + δ) / e) ν {c k ≤ f}`.
No measurability of `f` is needed: `ν` of a set is its outer measure. This is the step of the
upper bound of Varadhan's lemma that reduces an exponential moment to measures of closed sets.

## Main results

* `TauCeti.lintegral_ofReal_exp_div_le_sum_slabs`: the slab bound.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-- **Slab bound.** Let `|f| ≤ M` and `δ > 0`, and split the range `[-M, M]` of `f` into the
slabs `{c k ≤ f}` with lower edges `c k = -M + k δ`, `k < ⌊2 M / δ⌋₊ + 1`. Then the exponential
moment `∫⁻ exp (f / e) dν` is at most the sum over the slabs of `exp ((c k + δ) / e) ν {c k ≤ f}`.
No measurability is needed: `ν` of a set is its outer measure. -/
theorem lintegral_ofReal_exp_div_le_sum_slabs {f : X → ℝ} {M : ℝ} (hf : ∀ x, |f x| ≤ M) {δ : ℝ}
    (hδ : 0 < δ) (e : ℝ≥0) (ν : Measure X) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (f x / e)) ∂ν ≤
      ∑ k ∈ Finset.range (⌊2 * M / δ⌋₊ + 1),
        ENNReal.ofReal (Real.exp ((-M + k * δ + δ) / e)) * ν {x | -M + k * δ ≤ f x} := by
  -- Integrate indicators of measurable hulls of the slabs, which have the same measure.
  set T : ℕ → Set X := fun k => toMeasurable ν {x | -M + k * δ ≤ f x}
  have hT (k : ℕ) : MeasurableSet (T k) := measurableSet_toMeasurable ν _
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (f x / e)) ∂ν
      ≤ ∫⁻ x, ∑ k ∈ Finset.range (⌊2 * M / δ⌋₊ + 1),
          (T k).indicator (fun _ => ENNReal.ofReal (Real.exp ((-M + k * δ + δ) / e))) x ∂ν :=
        lintegral_mono fun x => ?_
    _ = _ := by
        rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hT k)]
        simp only [lintegral_indicator_const (hT _), T, measure_toMeasurable]
  -- The point `x` lies in the slab with index `⌊(f x + M) / δ⌋₊`.
  have hfx := abs_le.1 (hf x)
  have h0 : 0 ≤ (f x + M) / δ := div_nonneg (by linarith) hδ.le
  have hk1 := (le_div_iff₀ hδ).1 (Nat.floor_le h0)
  have hk2 := (div_lt_iff₀ hδ).1 (Nat.lt_floor_add_one ((f x + M) / δ))
  have hkN : ⌊(f x + M) / δ⌋₊ ∈ Finset.range (⌊2 * M / δ⌋₊ + 1) :=
    Finset.mem_range.2 <| Nat.lt_succ_of_le <|
      Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hδ.le)
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hkN)
  rw [Set.indicator_of_mem (subset_toMeasurable ν _ (Set.mem_ofPred.2 (by linarith)))]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    (div_le_div_of_nonneg_right (by linarith) e.coe_nonneg))

end TauCeti
