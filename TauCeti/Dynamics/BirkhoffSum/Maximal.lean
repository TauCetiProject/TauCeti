/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Maximal

/-!
# Companion lemmas for the maximal ergodic operator

Complements `Mathlib.Dynamics.BirkhoffSum.Maximal` with almost-everywhere finiteness of
`birkhoffAverageSup T (‖f ·‖)` for an integrable observable under a measure-preserving
endomorphism of a finite measure space.

## Main results

* `MeasureTheory.MeasurePreserving.ae_birkhoffAverageSup_norm_lt_top` — almost-everywhere
  finiteness of `birkhoffAverageSup T (‖f ·‖)` for an integrable observable on a finite measure
  space, derived from Mathlib's `mul_measureReal_lt_birkhoffAverageSup_le_norm`.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory.MeasurePreserving

/-- For a measure-preserving endomorphism of a finite measure space and an integrable observable,
the maximal ergodic function `birkhoffAverageSup T (‖f ·‖)` is almost everywhere finite. -/
theorem ae_birkhoffAverageSup_norm_lt_top {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, birkhoffAverageSup T (fun y ↦ ‖f y‖) x < ⊤ := by
  rw [ae_iff]
  have hreal : μ.real {x | ¬ birkhoffAverageSup T (fun y ↦ ‖f y‖) x < ⊤} = 0 := by
    refine le_antisymm ?_ measureReal_nonneg
    refine ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (∫ y, ‖f y‖ ∂μ)) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsub : {x | ¬ birkhoffAverageSup T (fun y ↦ ‖f y‖) x < ⊤} ⊆
        {x | ((n : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ ‖f y‖) x} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, not_lt, top_le_iff] at hx ⊢
      rw [hx]
      exact EReal.coe_lt_top (n : ℝ)
    rw [le_div_iff₀' hn']
    calc
      (n : ℝ) * μ.real {x | ¬ birkhoffAverageSup T (fun y ↦ ‖f y‖) x < ⊤}
        ≤ (n : ℝ) * μ.real {x | ((n : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ ‖f y‖) x} :=
          mul_le_mul_of_nonneg_left (measureReal_mono hsub) hn'.le
      _ ≤ ∫ y, ‖f y‖ ∂μ := mul_measureReal_lt_birkhoffAverageSup_le_norm μ hT hf (n : ℝ)
  exact (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hreal

end MeasureTheory.MeasurePreserving
