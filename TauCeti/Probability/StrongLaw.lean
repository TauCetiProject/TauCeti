/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.StrongLaw
-- Public: the statement is about `Measure.infinitePi`; the proof uses `iIndepFun_infinitePi`.
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Strong laws of large numbers

Mathlib's `ProbabilityTheory.strong_law_ae` takes a sequence of pairwise independent, identically
distributed, integrable random variables on an abstract probability space. The canonical carrier of
such a sequence is the countable power `Measure.infinitePi fun _ : ℕ => Q` with its coordinate maps,
and this file specializes the strong law to it. It also proves the infinite-mean extension for
nonnegative real variables: their averages tend almost surely to infinity. This form permits
inverting sums in renewal and occupation limit theorems without a finite-mean hypothesis.

## Main results

* `TauCeti.Probability.strong_law_ae_infinitePi` — for `f` measurable and integrable against `Q`,
  the averages `n⁻¹ • ∑_{i < n} f (xᵢ)` converge `Q^{⊗ℕ}`-almost everywhere to `∫ f dQ`.
* `TauCeti.Probability.measurableSet_tendsto_average_integral` — the corresponding convergence
  event is measurable when the probability measure is allowed to vary.
* `TauCeti.Probability.measure_compl_tendsto_average_integral_eq_zero` — the tagged product law
  `δ_Q ⊗ Q^{⊗ℕ}` gives that event full measure.
* `TauCeti.Probability.strong_law_ae_real_of_lintegral_eq_top` — nonnegative i.i.d. averages
  diverge almost surely when their extended mean is infinite; pairwise independence suffices.

## Implementation

Independence of the coordinates is Mathlib's `ProbabilityTheory.iIndepFun_infinitePi` for the
identity variables. Nothing is reproved about product measures.

The strong law itself is then Mathlib's, applied to `x ↦ f (x i)`: the three hypotheses come from
that independence and from `measurePreserving_eval_infinitePi`, which makes the coordinates
identically distributed, transports integrability, and identifies the limit `𝔼[f ∘ eval 0]` with
`∫ f dQ`.

`f` is assumed measurable, not merely almost-everywhere strongly measurable as `Integrable f Q`
gives: it has to be composed with the coordinate maps, so that independence and identical
distribution of the coordinates transfer to the summands.

The measurable tagged form packages the same theorem for integration over a random law. This is
general probability theory with no exchangeability in its statements. It is used by the conditional
strong law for conditionally i.i.d. processes in
`TauCeti.Probability.Exchangeability.ConditionallyIID.StrongLaw`, where the conditional statement is
reduced fibrewise to this one over the mixing law.

The infinite-mean extension applies Mathlib's strong law to bounded truncations and uses
monotone convergence to make their expectations arbitrarily large.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter XI, §1 (infinite-mean renewal limits).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **The strong law of large numbers on the canonical i.i.d. model.** For an `f` that is measurable
and integrable against `Q`, the averages of `f` along the coordinates of `Q^{⊗ℕ}` converge almost
everywhere to `∫ f dQ`.

This is Mathlib's `ProbabilityTheory.strong_law_ae` for the coordinate process of a countable
power; it is the form in which a statement about *some* i.i.d. sequence becomes a statement about
the product measure itself, and so can be integrated over a mixing law. -/
theorem strong_law_ae_infinitePi (Q : Measure α) [IsProbabilityMeasure Q] {f : α → E}
    (hf : Measurable f) (hint : Integrable f Q) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => Q),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (x i)) atTop
        (𝓝 (∫ y, f y ∂Q)) := by
  set P : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ => Q
  -- Every coordinate is measure preserving onto `Q`; integrability, identical distribution and the
  -- value of the limit all come from that one fact.
  have heval : ∀ i : ℕ, MeasurePreserving (fun x : ℕ → α => x i) P Q := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => Q) i
  have hint' : ∀ i : ℕ, Integrable (fun x : ℕ → α => f (x i)) P := fun i =>
    ((heval i).integrable_comp hint.1).2 hint
  have hident : ∀ i : ℕ,
      IdentDistrib (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x 0)) P P := fun i =>
    IdentDistrib.comp ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [(heval i).map_eq, (heval 0).map_eq]⟩ hf
  have hindep : ∀ i j : ℕ, i ≠ j →
      IndepFun (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x j)) P :=
    fun _ _ hij =>
      ((iIndepFun_infinitePi (P := fun _ : ℕ => Q) (X := fun _ x => x)
        fun _ => measurable_id).comp (fun _ => f) fun _ => hf).indepFun hij
  have hlimit : ∫ x, f (x 0) ∂P = ∫ y, f y ∂Q := by
    rw [← (heval 0).map_eq, integral_map (measurable_pi_apply 0).aemeasurable
      (by rw [(heval 0).map_eq]; exact hint.1)]
  simpa only [hlimit] using
    strong_law_ae (fun i (x : ℕ → α) => f (x i)) (hint' 0) hindep hident

variable [SecondCountableTopology E]

omit [CompleteSpace E] in
/-- The set of a probability measure and a path for which the path averages of `f` converge to its
integral against that measure is measurable. -/
theorem measurableSet_tendsto_average_integral {f : α → E} (hf : Measurable f) :
    MeasurableSet {z : ProbabilityMeasure α × (ℕ → α) |
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
        (𝓝 (∫ y, f y ∂(z.1 : Measure α)))} :=
  MeasureTheory.measurableSet_tendsto_fun
    (fun _n => (Finset.measurable_sum _ fun i _ =>
      hf.comp ((measurable_pi_apply i).comp measurable_snd)).const_smul _)
    ((hf.stronglyMeasurable.integral_kernel
      (κ := ⟨((↑) : ProbabilityMeasure α → Measure α), measurable_subtype_coe⟩)).measurable.comp
        measurable_fst)

/-- The tagged i.i.d. product law `δ_Q ⊗ Q^{⊗ℕ}` gives full measure to the event that the path
averages of `f` converge to its integral against `Q`. -/
theorem measure_compl_tendsto_average_integral_eq_zero {f : α → E} (hf : Measurable f)
    (Q : ProbabilityMeasure α) (hint : Integrable f (Q : Measure α)) :
    ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α)))
      {z : ProbabilityMeasure α × (ℕ → α) |
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
          (𝓝 (∫ y, f y ∂(z.1 : Measure α)))}ᶜ = 0 := by
  have hsl : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => (Q : Measure α)),
      (Q, x) ∈ {z : ProbabilityMeasure α × (ℕ → α) |
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
          (𝓝 (∫ y, f y ∂(z.1 : Measure α)))} := by
    filter_upwards [strong_law_ae_infinitePi (Q : Measure α) hf hint] with x hx
    simpa only [Set.mem_ofPred_eq] using hx
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
    (measurableSet_tendsto_average_integral hf).compl]
  exact ae_iff.mp hsl

section InfiniteMean

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- For pairwise independent identically distributed nonnegative real random variables with
infinite extended mean, the sample averages tend almost surely to infinity.
No integrability of the untruncated variables is required. -/
theorem strong_law_ae_real_of_lintegral_eq_top (X : ℕ → Ω → ℝ)
    (hpos : 0 ≤ᵐ[μ] X 0) (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ = ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X i ω) / n) atTop atTop := by
  let Y (k n : ℕ) (ω : Ω) : ℝ := min (X n ω) k
  have hYm (k : ℕ) : Measurable (fun x : ℝ ↦ min x (k : ℝ)) :=
    measurable_id.min measurable_const
  have hYi (k : ℕ) : Integrable (Y k 0) μ := by
    refine (integrable_const (k : ℝ)).mono'
      ((hYm k).comp_aemeasurable (hid 0).aemeasurable_fst).aestronglyMeasurable ?_
    filter_upwards [hpos] with ω hω
    simpa only [Y, Real.norm_eq_abs, abs_of_nonneg (le_min hω (Nat.cast_nonneg k))]
      using min_le_right (X 0 ω) (k : ℝ)
  -- Monotone convergence prevents all truncated expectations from sharing a finite bound.
  have hlarge (b : ℝ) : ∃ k, b < ∫ ω, Y k 0 ω ∂μ := by
    by_contra! h
    have hsup : (fun ω ↦ ENNReal.ofReal (X 0 ω)) =
        fun ω ↦ ⨆ k : ℕ, ENNReal.ofReal (Y k 0 ω) := by
      funext ω
      apply le_antisymm
      · obtain ⟨k, hk⟩ := exists_nat_ge (X 0 ω)
        exact le_iSup_of_le k (by simp [Y, min_eq_left hk])
      · exact iSup_le fun k ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)
    have hbound : ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ ≤ ENNReal.ofReal b := by
      rw [hsup, lintegral_iSup']
      · refine iSup_le fun k ↦ ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hYi k)
          (hpos.mono fun ω hω ↦ le_min hω (Nat.cast_nonneg k))]
        exact ENNReal.ofReal_le_ofReal (h k)
      · intro k
        exact (hYm k).ennreal_ofReal.comp_aemeasurable
          (hid 0).aemeasurable_fst
      · exact Filter.Eventually.of_forall fun ω i j hij ↦
          ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hij))
    exact (ENNReal.ofReal_lt_top).not_ge (hmean ▸ hbound)
  have hsl (k : ℕ) : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y k i ω) / n) atTop
        (𝓝 (∫ ω, Y k 0 ω ∂μ)) :=
    strong_law_ae_real (Y k) (hYi k)
      (fun i j hij ↦ (hindep hij).comp (hYm k) (hYm k))
      (fun i ↦ (hid i).comp (hYm k))
  -- Intersect only countably many strong-law events, then choose the truncation for each bound.
  filter_upwards [ae_all_iff.2 hsl] with ω hω
  refine tendsto_atTop.2 fun b ↦ ?_
  obtain ⟨k, hk⟩ := hlarge b
  filter_upwards [(hω k).eventually (lt_mem_nhds hk)] with n hn
  exact hn.le.trans (div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ ↦ min_le_left _ _) (Nat.cast_nonneg n))

end InfiniteMean

end Probability

end TauCeti
