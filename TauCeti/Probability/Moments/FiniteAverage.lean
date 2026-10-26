/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Second moments of finite averages about a random reference

If the centered functions `e i - q` have common integrated square `c` and their distinct
cross products integrate to zero, their average has integrated squared deviation `c / #s`
from `q`. The reference `q` may itself be random. This is useful for empirical frequencies
centered at a random probability, where the centered functions need not be independent.

Only the centered products are required to be integrable: neither a finite ambient measure
nor boundedness, independence, or a prescribed mean is needed. The nonempty index set is
essential, since the empty average need not agree with the reference function.

The calculation is extracted from the empirical-frequency proof in
`TauCeti.Probability.Exchangeability.ConditionallyIID.Moments`.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace TauCeti

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open scoped Classical in
/-- The integrated squared error of a finite average about a possibly random reference is
`c / #s` when the centered products have integral `c` on the diagonal and zero off it.
Only integrability of those products is required. -/
theorem integral_sq_average_sub {e : ι → Ω → ℝ} {q : Ω → ℝ} {c : ℝ} {s : Finset ι}
    (hs : s.Nonempty)
    (hint : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω ↦ (e i ω - q ω) * (e j ω - q ω)) μ)
    (hcov : ∀ i ∈ s, ∀ j ∈ s,
      ∫ ω, (e i ω - q ω) * (e j ω - q ω) ∂μ = if i = j then c else 0) :
    ∫ ω, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, e i ω) - q ω) ^ 2 ∂μ = (s.card : ℝ)⁻¹ * c := by
  classical
  simp_rw [average_sub_sq_eq_sum_sum hs]
  rw [integral_const_mul,
    integral_finsetSum _ fun i hi ↦ integrable_finsetSum _ fun j hj ↦ hint i hi j hj]
  have hrow : ∀ i ∈ s,
      ∫ ω, ∑ j ∈ s, (e i ω - q ω) * (e j ω - q ω) ∂μ = c := by
    intro i hi
    rw [integral_finsetSum _ fun j hj ↦ hint i hi j hj]
    rw [Finset.sum_congr rfl fun j hj ↦ hcov i hi j hj]
    simp [hi]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  field_simp

end TauCeti
