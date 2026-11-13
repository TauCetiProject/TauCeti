/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.StrongLaw
-- Public: the statement is about `Measure.infinitePi`.
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Probability.Independence.InfinitePi

/-!
# Strong laws of large numbers

Mathlib's `ProbabilityTheory.strong_law_ae` takes a sequence of pairwise independent, identically
distributed, integrable random variables on an abstract probability space. The canonical carrier of
such a sequence is the countable power `Measure.infinitePi fun _ : ℕ => Q` with its coordinate maps,
and this file specializes the strong law to it. It also proves the infinite-mean extension for
real variables whose positive part has infinite mean and whose negative part has finite mean: their
averages tend almost surely to infinity. This form permits inverting sums in renewal and occupation
limit theorems without a finite-mean hypothesis.

For variables with no moment assumptions, the fraction of coordinates whose norm exceeds a
threshold tending to infinity still tends almost surely to zero. The event is simultaneous for
all diverging thresholds; this is useful for removing large entries by rank bounds.

## Main results

* `TauCeti.Probability.strong_law_ae_infinitePi` — for `f` integrable against `Q`, the averages
  `n⁻¹ • ∑_{i < n} f (xᵢ)` converge `Q^{⊗ℕ}`-almost everywhere to `∫ f dQ`.
* `TauCeti.Probability.measurableSet_tendsto_average_integral` — the corresponding convergence
  event is measurable when the probability measure is allowed to vary.
* `TauCeti.Probability.measure_compl_tendsto_average_integral_eq_zero` — the tagged product law
  `δ_Q ⊗ Q^{⊗ℕ}` gives that event full measure.
* `TauCeti.Probability.strong_law_ae_real_of_lintegral_eq_top` — real i.i.d. averages diverge
  almost surely to `+∞` when the positive part has infinite extended mean and the negative part
  finite extended mean; pairwise independence suffices.
* `TauCeti.Probability.ae_tendsto_card_filter_norm_gt_div` — empirical tail frequencies at
  diverging thresholds tend almost surely to zero, without a moment assumption.

## Implementation

Independence and identical distribution of the coordinates are
`TauCeti.Probability.iIndepFun_eval_infinitePi` and
`MeasureTheory.Measure.identDistrib_eval_infinitePi`. Nothing is reproved about product measures.

The strong law itself is then Mathlib's, applied to `x ↦ f (x i)`: the three hypotheses come from
those coordinate facts and from `measurePreserving_eval_infinitePi`, which transports
integrability and identifies the limit `𝔼[f ∘ eval 0]` with `∫ f dQ`.

`f` need only be almost-everywhere strongly measurable, as `Integrable f Q` gives: since every
coordinate has law `Q`, `f` is almost-everywhere measurable for each coordinate's law, which is
what `IdentDistrib.comp_of_aemeasurable` and `iIndepFun.comp₀` need to transfer identical
distribution and independence to the summands. The measurable tagged form below still assumes `f`
measurable, as measurability of its convergence event requires.

The measurable tagged form packages the same theorem for integration over a random law. This is
general probability theory with no exchangeability in its statements. It is used by the conditional
strong law for conditionally i.i.d. processes in
`TauCeti.Probability.Exchangeability.ConditionallyIID.StrongLaw`, where the conditional statement is
reduced fibrewise to this one over the mixing law.

The infinite-mean extension applies Mathlib's strong law to bounded truncations of the positive
part and to the integrable negative part, and uses monotone convergence to make the truncated
expectations arbitrarily large.

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

/-- **The strong law of large numbers on the canonical i.i.d. model.** For an `f` integrable
against `Q`, the averages of `f` along the coordinates of `Q^{⊗ℕ}` converge almost
everywhere to `∫ f dQ`.

This is Mathlib's `ProbabilityTheory.strong_law_ae` for the coordinate process of a countable
power; it is the form in which a statement about *some* i.i.d. sequence becomes a statement about
the product measure itself, and so can be integrated over a mixing law. -/
theorem strong_law_ae_infinitePi (Q : Measure α) [IsProbabilityMeasure Q] {f : α → E}
    (hint : Integrable f Q) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => Q),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (x i)) atTop
        (𝓝 (∫ y, f y ∂Q)) := by
  set P : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ => Q
  -- Every coordinate is measure preserving onto `Q`; integrability, identical distribution and the
  -- value of the limit all come from that one fact.
  have heval : ∀ i : ℕ, MeasurePreserving (fun x : ℕ → α => x i) P Q := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => Q) i
  have hf : ∀ i : ℕ, AEMeasurable f (P.map fun x : ℕ → α => x i) := fun i => by
    rw [(heval i).map_eq]
    exact hint.1.aemeasurable
  have hident : ∀ i : ℕ,
      IdentDistrib (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x 0)) P P := fun i =>
    (Q.identDistrib_eval_infinitePi i 0).comp_of_aemeasurable (hf i)
  have hindep : ∀ i j : ℕ, i ≠ j →
      IndepFun (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x j)) P :=
    fun _ _ hij =>
      ((iIndepFun_eval_infinitePi _).comp₀ (fun _ => f)
        (fun i => (measurable_pi_apply i).aemeasurable) hf).indepFun hij
  have hlimit : ∫ x, f (x 0) ∂P = ∫ y, f y ∂Q := by
    rw [← (heval 0).map_eq, integral_map (measurable_pi_apply 0).aemeasurable
      (by rw [(heval 0).map_eq]; exact hint.1)]
  simpa only [hlimit] using
    strong_law_ae (fun i (x : ℕ → α) => f (x i)) (((heval 0).integrable_comp hint.1).2 hint)
      hindep hident

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
    filter_upwards [strong_law_ae_infinitePi (Q : Measure α) hint] with x hx
    simpa only [Set.mem_ofPred_eq] using hx
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
    (measurableSet_tendsto_average_integral hf).compl]
  exact ae_iff.mp hsl

section InfiniteMean

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- For pairwise independent identically distributed real random variables whose positive part
has infinite extended mean and whose negative part has finite extended mean, the sample averages
tend almost surely to infinity. This is the strong law with mean `+∞`. -/
theorem strong_law_ae_real_of_lintegral_eq_top (X : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hneg : ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ ≠ ⊤)
    (hmean : ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ = ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X i ω) / n) atTop atTop := by
  -- `Y k` truncates the positive part at `k`; `N` is the negative part, so `X ≥ Y k - N`.
  let Y (k n : ℕ) (ω : Ω) : ℝ := min (max (X n ω) 0) k
  let N (n : ℕ) (ω : Ω) : ℝ := max (-X n ω) 0
  have hYm (k : ℕ) : Measurable (fun x : ℝ ↦ min (max x 0) (k : ℝ)) :=
    (measurable_id.max measurable_const).min measurable_const
  have hNm : Measurable (fun x : ℝ ↦ max (-x) 0) := measurable_id.neg.max measurable_const
  have hYpos (k : ℕ) (ω : Ω) : 0 ≤ Y k 0 ω := le_min (le_max_right _ _) (Nat.cast_nonneg k)
  have hYi (k : ℕ) : Integrable (Y k 0) μ := by
    refine (integrable_const (k : ℝ)).mono'
      ((hYm k).comp_aemeasurable (hid 0).aemeasurable_fst).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simpa only [Y, Real.norm_eq_abs, abs_of_nonneg (hYpos k ω)]
      using min_le_right (max (X 0 ω) 0) (k : ℝ)
  have hNi : Integrable (N 0) μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      (hNm.comp_aemeasurable (hid 0).aemeasurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ le_max_right _ _)).1 ?_
    simpa [Function.comp_def] using hneg
  -- Monotone convergence prevents all truncated expectations from sharing a finite bound.
  have hlarge (b : ℝ) : ∃ k, b < ∫ ω, Y k 0 ω ∂μ := by
    by_contra! h
    have hsup : (fun ω ↦ ENNReal.ofReal (X 0 ω)) =
        fun ω ↦ ⨆ k : ℕ, ENNReal.ofReal (Y k 0 ω) := by
      funext ω
      apply le_antisymm
      · obtain ⟨k, hk⟩ := exists_nat_ge (max (X 0 ω) 0)
        exact le_iSup_of_le k (by simp [Y, min_eq_left hk])
      · -- `ENNReal.ofReal` already sends the negative values cut off by `max` to zero.
        exact iSup_le fun k ↦ (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (by simp)
    have hbound : ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ ≤ ENNReal.ofReal b := by
      rw [hsup, lintegral_iSup']
      · refine iSup_le fun k ↦ ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hYi k)
          (Filter.Eventually.of_forall (hYpos k))]
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
  have hslN := strong_law_ae_real N hNi (fun i j hij ↦ (hindep hij).comp hNm hNm)
    (fun i ↦ (hid i).comp hNm)
  -- Intersect only countably many strong-law events, then choose the truncation for each bound.
  filter_upwards [ae_all_iff.2 hsl, hslN] with ω hω hωN
  refine tendsto_atTop.2 fun b ↦ ?_
  obtain ⟨k, hk⟩ := hlarge (b + ∫ ω, N 0 ω ∂μ)
  filter_upwards [((hω k).sub hωN).eventually (lt_mem_nhds (lt_sub_iff_add_lt.2 hk))]
    with n hn
  rw [← sub_div, ← Finset.sum_sub_distrib] at hn
  -- Each summand of the truncated difference is at most `X i ω = max (X i ω) 0 - N i ω`.
  refine hn.le.trans (div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ ↦ ?_)
    (Nat.cast_nonneg n))
  calc Y k i ω - N i ω ≤ max (X i ω) 0 - max (-X i ω) 0 := sub_le_sub_right (min_le_left _ _) _
    _ = X i ω := max_zero_sub_max_neg_zero_eq_self _

end InfiniteMean

section EscapingThresholds

variable {Ω F : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup F]
  [MeasurableSpace F] [OpensMeasurableSpace F] {P : Measure Ω} [IsFiniteMeasure P]

/-- For pairwise independent identically distributed random variables, the proportion of the
first `n` coordinates exceeding any threshold tending to infinity tends almost surely to zero.
No moment assumption is needed. The full-measure event works simultaneously for all threshold
sequences, so the thresholds may even be chosen after the sample point is fixed. -/
theorem ae_tendsto_card_filter_norm_gt_div (X : ℕ → Ω → F)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, ∀ b : ℕ → ℝ, Tendsto b atTop atTop →
      Tendsto (fun n ↦
        (((Finset.range n).filter fun i ↦ b n < ‖X i ω‖).card : ℝ) / n)
        atTop (𝓝 0) := by
  classical
  let f (k : ℕ) : F → ℝ := {x | (k : ℝ) < ‖x‖}.indicator 1
  have hfm (k : ℕ) : Measurable (f k) :=
    measurable_const.indicator (measurableSet_lt measurable_const continuous_norm.measurable)
  have hbound (k : ℕ) (x : F) : ‖f k x‖ ≤ 1 := by
    simp only [f, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> norm_num
  have hfi (k : ℕ) : Integrable (fun ω ↦ f k (X 0 ω)) P :=
    Integrable.of_bound
      ((hfm k).comp_aemeasurable (hid 0).aemeasurable_fst).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ hbound k (X 0 ω))
  -- Apply the strong law only to bounded indicators at fixed integer thresholds.
  have hsl (k : ℕ) : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (∑ i ∈ Finset.range n, f k (X i ω)) / n) atTop
        (𝓝 (∫ ω, f k (X 0 ω) ∂P)) :=
    strong_law_ae_real (fun i ω ↦ f k (X i ω)) (hfi k)
      (fun i j hij ↦ (hindep hij).comp (hfm k) (hfm k))
      (fun i ↦ (hid i).comp (hfm k))
  -- The expectations vanish as the fixed threshold tends to infinity.
  have htail : Tendsto (fun k ↦ ∫ ω, f k (X 0 ω) ∂P) atTop (𝓝 0) := by
    have hpoint (ω : Ω) : Tendsto (fun k ↦ f k (X 0 ω)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop ‖X 0 ω‖)] with k hk
      simp [f, not_lt.mpr hk]
    simpa using tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun k ↦ (hfi k).aestronglyMeasurable)
      (integrable_const 1) (fun k ↦ ae_of_all _ fun ω ↦ hbound k (X 0 ω))
      (ae_of_all _ hpoint)
  -- Intersect countably many events before allowing an arbitrary threshold sequence.
  filter_upwards [ae_all_iff.2 hsl] with ω hω
  intro b hb
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (by positivity)
  · intro ε hε
    obtain ⟨k, hk⟩ := (htail.eventually (gt_mem_nhds hε)).exists
    filter_upwards [hb.eventually (eventually_ge_atTop (k : ℝ)),
      (hω k).eventually (gt_mem_nhds hk)] with n hn hsum
    refine lt_of_le_of_lt ?_ hsum
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [Finset.natCast_card_filter]
    simp only [f, Set.indicator_apply, Pi.one_apply]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h h' h'
    · rfl
    · exact False.elim (h' (hn.trans_lt h))
    · norm_num
    · rfl

end EscapingThresholds

end Probability

end TauCeti
