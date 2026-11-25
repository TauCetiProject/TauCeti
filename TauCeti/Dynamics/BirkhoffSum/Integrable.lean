/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Integrable
import Mathlib.Probability.HasLaw

/-!
# Bochner integral invariance of Birkhoff sums and averages

Complements `Mathlib.Dynamics.BirkhoffSum.Integrable` with Bochner integral identities for
Birkhoff sums and averages under a measure-preserving endomorphism.

## Main results

* `MeasureTheory.MeasurePreserving.integral_birkhoffSum` — the Bochner integral of the `n`-th
  Birkhoff sum of an integrable observable is `n • ∫ x, f x ∂μ`.
* `MeasureTheory.MeasurePreserving.integral_birkhoffAverage` — the Bochner integral of a nonempty
  Birkhoff average of an integrable observable equals `∫ x, f x ∂μ`.
-/

public section

namespace MeasureTheory.MeasurePreserving

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {T : Ω → Ω} {f : Ω → E}

/-- The integral of the `n`-th Birkhoff sum of an integrable observable under a measure-preserving
map is `n` times the integral of the observable. -/
theorem integral_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    ∫ x, birkhoffSum T f n x ∂μ = n • ∫ x, f x ∂μ := by
  simp_rw [birkhoffSum]
  rw [integral_finsetSum (Finset.range n) (f := fun k x ↦ f (T^[k] x))
    fun k _ ↦ (hT.iterate k).integrable_comp_of_integrable hf]
  have hterm (k : ℕ) : ∫ x, f (T^[k] x) ∂μ = ∫ x, f x ∂μ :=
    (hT.iterate k).hasLaw.integral_comp hf.aestronglyMeasurable
  simp [hterm]

/-- The integral of a nonempty Birkhoff average of an integrable observable under a
measure-preserving map equals the integral of the observable. -/
theorem integral_birkhoffAverage (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ x, birkhoffAverage ℝ T f n x ∂μ = ∫ x, f x ∂μ := by
  simp_rw [birkhoffAverage]
  rw [integral_smul, hT.integral_birkhoffSum hf n, ← Nat.cast_smul_eq_nsmul ℝ,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr hn)]

end MeasureTheory.MeasurePreserving
