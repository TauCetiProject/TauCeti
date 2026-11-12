/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Operations
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Exponential.Support

/-!
# Support and atoms of hypoexponential laws

A nonempty sum of independent exponential variables is absolutely continuous with respect to
Lebesgue measure, hence atomless, and its topological support is the closed half-line
`[0, ∞)`. Absolute continuity follows by splitting off one exponential summand as a
convolution factor. Every positive point is the sum of a constant vector of positive
coordinates, and neighbourhoods of that vector have positive product measure.

These facts give continuity and strict increase of the cdf without the partial-fraction
formula for the density.

The proof of `support_hypoexponentialMeasure` closely follows
`TauCeti.Probability.support_irwinHallMeasure` from
`TauCeti.Probability.Distributions.IrwinHall.Support`.

## References

* S. M. Ross, *Introduction to Probability Models*, 12th ed., Academic Press (2019), Chapter 5.
-/

public section

open MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- A nonempty hypoexponential law is absolutely continuous with respect to Lebesgue measure.
This includes invalid rates, where the law is zero. -/
theorem hypoexponentialMeasure_absolutelyContinuous [Nonempty ι] (r : ι → ℝ) :
    hypoexponentialMeasure r ≪ volume := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let e := Equiv.sumCompl fun i : ι ↦ i ≠ i₀
  let _ : Nonempty {i : ι // ¬i ≠ i₀} := ⟨⟨i₀, not_not.2 rfl⟩⟩
  have hsplit : r ∘ e =
      Sum.elim (fun j : {i : ι // i ≠ i₀} ↦ r j) (fun _ : {i : ι // ¬i ≠ i₀} ↦ r i₀) := by
    funext j
    cases j with
    | inl j => simp [e]
    | inr j => simp [e, not_not.1 j.2]
  by_cases hr : 0 < r i₀
  · rw [← hypoexponentialMeasure_reindex r e, hsplit,
      ← hypoexponentialMeasure_conv_hypoexponentialMeasure, hypoexponentialMeasure_const hr,
      gammaMeasure]
    exact Measure.conv_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
  · rw [hypoexponentialMeasure_eq_zero_of_invalid fun h ↦ hr (h i₀)]
    exact Measure.AbsolutelyContinuous.zero _

/-- Nonempty hypoexponential laws have no atoms. -/
instance nullSingletonClass_hypoexponentialMeasure [Nonempty ι] (r : ι → ℝ) :
    NullSingletonClass (hypoexponentialMeasure r) :=
  ⟨fun x ↦ hypoexponentialMeasure_absolutelyContinuous r (measure_singleton x)⟩

/-- A nonempty hypoexponential law with positive rates has topological support `[0, ∞)`. -/
@[simp]
theorem support_hypoexponentialMeasure [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    (hypoexponentialMeasure r).support = Ici 0 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici
      ((ae_pos_hypoexponentialMeasure r).mono fun _ hx ↦ le_of_lt hx)
  · have hpos : Ioi (0 : ℝ) ⊆ (hypoexponentialMeasure r).support := by
      intro x hx
      rw [Measure.support_eq_forall_isOpen]
      intro U hxU hU
      have hsum : (∑ _ : ι, x / (Fintype.card ι : ℝ)) = x := by
        simp [div_eq_mul_inv, mul_left_comm, hn.ne']
      have hpre : (fun y : ι → ℝ ↦ ∑ i, y i) ⁻¹' U ∈
          𝓝 (fun _ : ι ↦ x / (Fintype.card ι : ℝ)) := by
        apply ContinuousAt.preimage_mem_nhds (by fun_prop)
        simpa only [hsum] using hU.mem_nhds hxU
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
      let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
        isProbabilityMeasure_expMeasure (hr i)
      rw [hypoexponentialMeasure_eq_map hr, Measure.map_apply (by fun_prop) hU.measurableSet]
      refine lt_of_lt_of_le ?_ (measure_mono hball)
      rw [Measure.pi_ball _ _ hε]
      apply pos_iff_ne_zero.2
      apply Finset.prod_ne_zero_iff.2
      intro i _
      apply ne_of_gt
      apply (Measure.mem_support_iff_forall _).1 ?_ _ (Metric.ball_mem_nhds _ hε)
      rw [support_expMeasure (hr i)]
      exact (div_pos (mem_Ioi.1 hx) hn).le
    simpa only [closure_Ioi] using closure_minimal hpos Measure.isClosed_support

end TauCeti.Probability
