/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Series with summable mixed norms

Let `gᵢ : β → Lᵖ(α, μ)`, `i ∈ ι`, be countably many almost everywhere strongly measurable families
of `Lᵖ` functions, and let `1 ≤ q` and `1 ≤ r`. If their mixed norms are summable,

`∑ᵢ ‖gᵢ‖_{L^q_b L^r_x} < ∞`, where `‖gᵢ‖_{L^q_b L^r_x} = ‖b ↦ ‖gᵢ(b)‖_{L^r(μ)}‖_{L^q(ρ)}`,

then the series `∑ᵢ gᵢ` converges, although its terms need not lie in `L^r` at every `b` and the
series need not converge in `Lᵖ`: there is `U : β → L^r(α, μ)` such that

* for almost every `b`, the partial sums `∑_{i ∈ s} gᵢ(b)` converge to `U(b)` in `L^r(μ)` along the
  finite sets `s` of indices;
* the partial sums converge to `U` in the mixed norm `L^q_b L^r_x`;
* `‖U‖_{L^q_b L^r_x} ≤ ∑ᵢ ‖gᵢ‖_{L^q_b L^r_x}`

(`MeasureTheory.exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top`). This is how a solution
of an evolution equation is assembled from frequency-localized pieces `gⱼ(t) = T(t) fⱼ` once each
piece is controlled in a mixed norm: the data `∑ⱼ fⱼ` may lie only in a completed space of
distributions, with no meaning of `T(t)` on it, while the series of the pieces converges.

Minkowski's inequality for series (`eLpNorm_tsum_le`) bounds the mixed norm of
`b ↦ ∑ᵢ ‖gᵢ(b)‖_{L^r}` by `∑ᵢ ‖gᵢ‖_{L^q_b L^r_x}`, so `∑ᵢ ‖gᵢ(b)‖_{L^r}` is finite for almost every
`b`; at such `b` the series converges absolutely in the Banach space `L^r(μ)`, with tails
`‖U(b) - ∑_{i ∈ s} gᵢ(b)‖_{L^r} ≤ ∑_{i ∉ s} ‖gᵢ(b)‖_{L^r}`
(`MeasureTheory.exists_eLpNorm_sub_sum_le_tsum_compl`). Minkowski's inequality again bounds the
mixed norm of the tails by `∑_{i ∉ s} ‖gᵢ‖_{L^q_b L^r_x}`, which tends to zero.

## Main declarations

* `MeasureTheory.exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top`: a series of families
  with summable mixed norms converges almost everywhere in the parameter and in mixed norm.

## References

* A. Benedek and R. Panzone, *The space `Lᴾ`, with mixed norm*, Duke Math. J. 28 (1961), 301–324.
-/

public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {α ι F : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]
  {p r : ℝ≥0∞} [Fact (1 ≤ r)]

variable [Fact (1 ≤ p)] {β : Type*} {mβ : MeasurableSpace β} {ρ : Measure β} {q : ℝ≥0∞}

/-- For families with summable mixed norms, `∑ᵢ ‖gᵢ(b)‖_{L^r}` is finite for almost every `b`, and
at such `b` the series `∑ᵢ gᵢ(b)` has a sum `U(b)` in `L^r` as in
`MeasureTheory.exists_eLpNorm_sub_sum_le_tsum_compl`. -/
private theorem exists_ae_tsum_lt_top_and_eLpNorm_sub_sum_le [CompleteSpace F] [Countable ι]
    (hq : 1 ≤ q) {g : ι → β → Lp F p μ} (hg : ∀ i, AEStronglyMeasurable (g i) ρ)
    (hsum : ∑' i, eLpNorm (fun b ↦ eLpNorm (g i b) r μ) q ρ ≠ ∞) :
    ∃ U : β → Lp F r μ, ∀ᵐ b ∂ρ, ∑' i, eLpNorm (g i b) r μ < ∞ ∧
      (∀ s : Finset ι, eLpNorm (⇑(U b) - ⇑(∑ i ∈ s, g i b)) r μ ≤
        ∑' i : ↥(s : Set ι)ᶜ, eLpNorm (g i b) r μ) ∧
      ∀ s : Finset ι, Tendsto
        (fun t : Finset ι ↦ eLpNorm (⇑(∑ i ∈ t, g i b) - ⇑(∑ i ∈ s, g i b)) r μ) atTop
          (𝓝 (eLpNorm (⇑(U b) - ⇑(∑ i ∈ s, g i b)) r μ)) := by
  -- Minkowski's inequality: `b ↦ ∑ᵢ ‖gᵢ(b)‖_{L^r}` has finite mixed norm, so it is finite at
  -- almost every `b`.
  have hfin : ∀ᵐ b ∂ρ, ∑' i, eLpNorm (g i b) r μ < ∞ :=
    TauCeti.ae_lt_top_of_eLpNorm_ne_top (zero_lt_one.trans_le hq).ne'
      ((eLpNorm_tsum_le (fun i ↦ (hg i).aemeasurable_eLpNorm_Lp .rfl r) hq).trans_lt
        hsum.lt_top).ne
  have hex (b : β) : ∃ v : Lp F r μ, ∑' i, eLpNorm (g i b) r μ ≠ ∞ →
      (∀ s : Finset ι, eLpNorm (⇑v - ⇑(∑ i ∈ s, g i b)) r μ ≤
        ∑' i : ↥(s : Set ι)ᶜ, eLpNorm (g i b) r μ) ∧
      ∀ s : Finset ι, Tendsto
        (fun t : Finset ι ↦ eLpNorm (⇑(∑ i ∈ t, g i b) - ⇑(∑ i ∈ s, g i b)) r μ) atTop
          (𝓝 (eLpNorm (⇑v - ⇑(∑ i ∈ s, g i b)) r μ)) := by
    by_cases hb : ∑' i, eLpNorm (g i b) r μ ≠ ∞
    · obtain ⟨v, hv⟩ := exists_eLpNorm_sub_sum_le_tsum_compl hb
      exact ⟨v, fun _ ↦ hv⟩
    · exact ⟨0, fun h ↦ absurd h hb⟩
  choose U hU using hex
  exact ⟨U, by filter_upwards [hfin] with b hb using ⟨hb, hU b hb.ne⟩⟩

/-- **Series with summable mixed norms.** Let `1 ≤ q`, let `1 ≤ r`, and let `gᵢ : β → Lᵖ(μ)`,
`i ∈ ι`, be countably many almost everywhere strongly measurable families whose mixed norms
`‖gᵢ‖_{L^q_b L^r_x} = ‖b ↦ ‖gᵢ(b)‖_{L^r(μ)}‖_{L^q(ρ)}` are summable. Then there is
`U : β → L^r(μ)` such that the partial sums `∑_{i ∈ s} gᵢ` converge to `U` in `L^r(μ)` at almost
every `b`, and in the mixed norm `L^q_b L^r_x`, and `‖U‖_{L^q_b L^r_x} ≤ ∑ᵢ ‖gᵢ‖_{L^q_b L^r_x}`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top [CompleteSpace F] [Countable ι]
    (hq : 1 ≤ q) {g : ι → β → Lp F p μ} (hg : ∀ i, AEStronglyMeasurable (g i) ρ)
    (hsum : ∑' i, eLpNorm (fun b ↦ eLpNorm (g i b) r μ) q ρ ≠ ∞) :
    ∃ U : β → Lp F r μ,
      (∀ᵐ b ∂ρ, Tendsto (fun s : Finset ι ↦ eLpNorm (⇑(U b) - ⇑(∑ i ∈ s, g i b)) r μ) atTop
        (𝓝 0)) ∧
      Tendsto (fun s : Finset ι ↦
        eLpNorm (fun b ↦ eLpNorm (⇑(U b) - ⇑(∑ i ∈ s, g i b)) r μ) q ρ) atTop (𝓝 0) ∧
      eLpNorm (fun b ↦ ‖U b‖ₑ) q ρ ≤ ∑' i, eLpNorm (fun b ↦ eLpNorm (g i b) r μ) q ρ := by
  obtain ⟨U, hgood⟩ := exists_ae_tsum_lt_top_and_eLpNorm_sub_sum_le hq hg hsum
  -- The tails are almost everywhere measurable in `b`, as limits of the measurable functions
  -- `b ↦ ‖∑_{i ∈ t} gᵢ(b) - ∑_{i ∈ s} gᵢ(b)‖_{L^r}`.
  have hmeas (s : Finset ι) :
      AEMeasurable (fun b ↦ eLpNorm (⇑(U b) - ⇑(∑ i ∈ s, g i b)) r μ) ρ := by
    refine aemeasurable_of_tendsto_metrizable_ae (atTop : Filter (Finset ι)) (fun t ↦ ?_)
      (by filter_upwards [hgood] with b hb using hb.2.2 s)
    have hG : AEStronglyMeasurable (fun b ↦ ∑ i ∈ t, g i b - ∑ i ∈ s, g i b) ρ :=
      (t.aestronglyMeasurable_fun_sum fun i _ ↦ hg i).sub
        (s.aestronglyMeasurable_fun_sum fun i _ ↦ hg i)
    exact (hG.aemeasurable_eLpNorm_Lp .rfl r).congr
      (ae_of_all _ fun b ↦ eLpNorm_congr_ae (Lp.coeFn_sub _ _))
  -- The mixed norm of the tail beyond `s` is at most `∑_{i ∉ s} ‖gᵢ‖_{L^q_b L^r_x}`.
  have htail (s : Finset ι) :
      eLpNorm (fun b ↦ eLpNorm (⇑(U b) - ⇑(∑ i ∈ s, g i b)) r μ) q ρ ≤
        ∑' i : ↥(s : Set ι)ᶜ, eLpNorm (fun b ↦ eLpNorm (g i b) r μ) q ρ := by
    refine (eLpNorm_mono_eNorm_ae (hmeas s).aestronglyMeasurable ?_).trans
      (eLpNorm_tsum_le (ι := ↥(s : Set ι)ᶜ) (fun i ↦ (hg i).aemeasurable_eLpNorm_Lp .rfl r) hq)
    filter_upwards [hgood] with b hb
    simpa only [eNorm_eq_self] using hb.2.1 s
  refine ⟨U, ?_, ?_, ?_⟩
  · filter_upwards [hgood] with b hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_tsum_compl_atTop_zero hb.1.ne) (fun _ ↦ zero_le) hb.2.1
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_tsum_compl_atTop_zero hsum) (fun _ ↦ zero_le) htail
  · -- The partial sum over `∅` is `0`, and the tail beyond `∅` is the whole series.
    have hzero (b : β) :
        eLpNorm (⇑(U b) - ⇑(∑ i ∈ (∅ : Finset ι), g i b)) r μ = ‖U b‖ₑ := by
      rw [Finset.sum_empty, Lp.eNorm_def]
      exact eLpNorm_congr_ae (by
        filter_upwards [Lp.coeFn_zero (E := F) (p := p) (μ := μ)] with a ha
        rw [Pi.sub_apply, ha, Pi.zero_apply, sub_zero])
    refine le_of_eq_of_le ?_ ((htail ∅).trans (tsum_comp_le_tsum_of_injective
      Subtype.val_injective fun i ↦ eLpNorm (fun b ↦ eLpNorm (g i b) r μ) q ρ))
    simp only [hzero]

end MeasureTheory
