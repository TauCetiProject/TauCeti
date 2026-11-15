/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerHarmonic
public import Mathlib.Probability.Kernel.Invariance

/-!
# No finite invariant law for symmetric integer walk

For the kernel taking a unit step in either direction with equal probability,
every finite invariant measure is zero. In particular there is no invariant
probability. The statement uses the kernel's rows directly, so it applies to any
construction of this walk, without introducing a second transition kernel.

Together with recurrence and the invariant-probability characterization of
positive recurrence, this obstruction distinguishes null recurrence of symmetric
integer walk from positive recurrence. Recurrence itself is not asserted here.

See J. R. Norris, *Markov Chains* (1997), §§1.6–1.7.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel.Invariant

/-- A finite invariant measure for symmetric nearest-neighbor walk on `ℤ` is zero.
Consequently an invariant probability cannot exist. No normalization of the
candidate invariant measure is required. -/
theorem eq_zero_of_symmetric_int_steps {κ : Kernel ℤ ℤ} {μ : Measure ℤ}
    [IsFiniteMeasure μ] (h : κ.Invariant μ)
    (hκ : ∀ z, κ z = (2 : ℝ≥0∞)⁻¹ • Measure.dirac (z + 1) +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (z - 1)) : μ = 0 := by
  apply μ.eq_zero_of_eq_average_int_translates
  calc
    μ = μ.bind κ := h.def.symm
    _ = _ := by
      ext s hs
      rw [Measure.bind_apply hs κ.aemeasurable]
      simp_rw [hκ, add_apply, smul_apply, smul_eq_mul]
      rw [lintegral_add_left (measurable_of_countable _),
        lintegral_const_mul _ (measurable_of_countable _),
        lintegral_const_mul _ (measurable_of_countable _)]
      congr 1 <;> congr 1
      all_goals
        rw [← Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
          Measure.bind_dirac_eq_map μ (measurable_of_countable _)]

end ProbabilityTheory.Kernel.Invariant
