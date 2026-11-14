/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
public import TauCeti.MeasureTheory.Function.LpSeminorm.WithDensity
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Simultaneous drift and diffusion approximation of holdings

A stock holding must be approximated in two different norms: absolute drift variation
uses L¹, whereas diffusion energy uses L². Approximating the drift and diffusion
coefficients independently does not produce a single sequence of trading holdings.

Let the first measure on the predictable sigma-algebra be finite and the second finite on
bounded predictable rectangles, both with a null initial-time slice `{0} ×ˢ univ`. Then every
almost-everywhere predictable holding in L¹ of the first and L² of the second has one sequence
of bounded finite-grid approximants converging in both norms. The measures may be mutually
singular or vanish; in particular no lower bound on the volatility or drift is needed. Each
trading height is known at the left endpoint, and every grid starts at zero.

The construction uses Mathlib's `SimpleFunc.approxOn` quantizations in both norms,
followed by the existing predictable L² grid density theorem for the sum measure.
It does not require the original holding to be square integrable for the drift measure.
For stock trading, use absolute drift density for the first measure and squared
diffusion density for the second. The base measure may live on any sigma-algebra containing
the predictable one, such as the time-product sigma-algebra, so the coefficients need not be
predictable. Finiteness of the drift measure is an expected-variation hypothesis; almost-sure
local integrability alone requires a separate localization argument.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)

/-- One sequence of bounded elementary holdings converges simultaneously in predictable
L¹ for a finite measure `μ` and in predictable L² for a measure `ν` finite on bounded
predictable rectangles, provided both measures have null initial-time slices. These are the
distinct drift-variation and diffusion-energy topologies for stock holdings. The holding need
only be almost-everywhere predictable, and no L² hypothesis for `μ` is imposed. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_one_two
    (μ ν : @Measure (ℝ≥0 × Ω) ℱ.predictable) [IsFiniteMeasure μ]
    (hνfin : ∀ t, ν (Ioc 0 t ×ˢ (univ : Set Ω)) ≠ ∞)
    (hμ₀ : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    (hν₀ : ν ({0} ×ˢ (univ : Set Ω)) = 0)
    {H : ℝ≥0 → Ω → ℝ}
    (hH₁ : MemLp (Function.uncurry H) 1 μ) (hH₂ : MemLp (Function.uncurry H) 2 ν) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      Tendsto (fun k ↦ eLpNorm
        (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 1 μ) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ eLpNorm
        (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2 ν) atTop (𝓝 0) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  -- Replace the holding by a predictable version, equal almost everywhere for both measures.
  have hHm := hH₁.aestronglyMeasurable.add_measure hH₂.aestronglyMeasurable
  set G := hHm.mk (Function.uncurry H)
  have hGm : Measurable G := hHm.stronglyMeasurable_mk.measurable
  have hHG := ae_add_measure_iff.mp hHm.ae_eq_mk
  have hG₂ : MemLp G 2 ν := hH₂.ae_eq hHG.2
  -- Use the same finite-valued quantizations for both norms.
  let f (k : ℕ) := SimpleFunc.approxOn G hGm univ 0 (mem_univ _) k
  have happrox {p : ℝ≥0∞} {ρ : Measure (ℝ≥0 × Ω)} (hp : p ≠ ∞) (hGp : MemLp G p ρ) :
      Tendsto (fun k ↦ eLpNorm (fun x ↦ f k x - G x) p ρ) atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm hGm (mem_univ _) hp
    · simp
    · simpa only [sub_zero] using hGp.eLpNorm_lt_top
  have hzero : (μ + ν) ({0} ×ˢ (univ : Set Ω)) = 0 := by simp [hμ₀, hν₀]
  -- Bounded quantizations belong to L² of the sum measure and admit trading grids.
  have hex (k : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt (μ + ν)
    (fun s t A _ ↦ by
      simpa only [FunLike.coe_add, Pi.add_apply] using
        ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
          ne_top_of_le_ne_top (hνfin t)
            (measure_mono (prod_mono (Ioc_subset_Ioc_left bot_le) (subset_univ A)))⟩)
    hzero
    (H := fun t ω ↦ f k (t, ω))
    (((f k).memLp_of_isFiniteMeasure 2 μ).add_measure
      (SimpleFunc.memLp_approxOn hGm hG₂ (mem_univ _) MemLp.zero' k) |>.ae_eq
      (.of_forall fun p ↦ by
        rcases p with ⟨t, ω⟩
        simp only [Function.uncurry_apply_pair]))
    (ε := (k : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  choose n τ a C hτ₀ hτ ha hb herr using hex
  let E (k : ℕ) (p : ℝ≥0 × Ω) := simpleHolding (τ k) (n k) (a k) p.1 p.2 - f k p
  -- L² control for the sum measure controls L² diffusion and L¹ drift errors.
  have hsum : Tendsto (fun k ↦ eLpNorm (E k) 2 (μ + ν)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ bot_le) (fun k ↦ (herr k).le)
  have hdiff : Tendsto (fun k ↦ eLpNorm (E k) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ bot_le) (fun k ↦ eLpNorm_le_add_measure_left _ _ _)
  have hdrift : Tendsto (fun k ↦ eLpNorm (E k) 1 μ) atTop (𝓝 0) :=
    TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ ↦ bot_le) (fun k ↦ eLpNorm_le_add_measure_right _ _ _)
  -- Add the grid-to-quantization errors to the quantization-to-holding errors.
  have htotal (p : ℝ≥0∞) (ρ : Measure (ℝ≥0 × Ω)) (hp : 1 ≤ p) (hpfin : p ≠ ∞)
      (hE : Tendsto (fun k ↦ eLpNorm (E k) p ρ) atTop (𝓝 0))
      (hGp : MemLp G p ρ) (hHGρ : Function.uncurry H =ᵐ[ρ] G) :
      Tendsto (fun k ↦ eLpNorm
        (fun x ↦ simpleHolding (τ k) (n k) (a k) x.1 x.2 - H x.1 x.2) p ρ) atTop (𝓝 0) := by
    have hbound (k : ℕ) :
        eLpNorm (fun x ↦ simpleHolding (τ k) (n k) (a k) x.1 x.2 - H x.1 x.2) p ρ ≤
          eLpNorm (E k) p ρ + eLpNorm (fun x ↦ f k x - G x) p ρ := by
      have hae : (fun x ↦ simpleHolding (τ k) (n k) (a k) x.1 x.2 - H x.1 x.2) =ᵐ[ρ]
          E k + fun x ↦ f k x - G x := by
        filter_upwards [hHGρ] with x hx
        simp [E, ← hx, Function.uncurry_def]
      rw [eLpNorm_congr_ae hae]
      exact eLpNorm_add_le hp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hE.add (happrox hpfin hGp)) (fun _ ↦ bot_le) hbound
  exact ⟨n, τ, a, C, hτ₀, hτ, ha, hb,
    htotal 1 μ le_rfl (by simp) hdrift (hH₁.ae_eq hHG.1) hHG.1,
    htotal 2 ν one_le_two (by simp) hdiff hG₂ hHG.2⟩

/-- Approximate one stock holding simultaneously in its drift and diffusion gains
coefficients `D` and `V`: the products `D * (holding - H)` tend to zero in L¹ and
`V * (holding - H)` in L². The measure `ρ` may live on any sigma-algebra containing the
predictable one, such as the time-product sigma-algebra, so `D` and `V` need only be
`ρ`-almost-everywhere strongly measurable there; for instance `D = μ S` and `V = σ S` with
progressive `μ, σ`. The holding `H` must be almost everywhere predictable for the trace of `ρ`
on the predictable sigma-algebra, and the initial-time slice must be `ρ`-null. The drift
coefficient and gains need L¹, the diffusion gains L², and the diffusion coefficient only L²
on bounded predictable rectangles; no nonvanishing, boundedness or continuity assumption on
the coefficients is needed. This is an approximation theorem, not a construction of the
stochastic integral. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_mul_one_two
    {m : MeasurableSpace (ℝ≥0 × Ω)} (hm : ℱ.predictable ≤ m) (ρ : @Measure (ℝ≥0 × Ω) m)
    (hρ₀ : ρ ({0} ×ˢ (univ : Set Ω)) = 0)
    {H D V : ℝ≥0 → Ω → ℝ}
    (hH : AEStronglyMeasurable[ℱ.predictable] (Function.uncurry H) (ρ.trim hm))
    (hD₁ : MemLp (Function.uncurry D) 1 ρ)
    (hV₂ : ∀ t, MemLp (Function.uncurry V) 2
      (ρ.restrict (Ioc 0 t ×ˢ (univ : Set Ω))))
    (hHD₁ : MemLp (Function.uncurry D * Function.uncurry H) 1 ρ)
    (hHV₂ : MemLp (Function.uncurry V * Function.uncurry H) 2 ρ) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      Tendsto (fun k ↦ eLpNorm (fun p ↦ D p.1 p.2 *
        (simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)) 1 ρ) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ eLpNorm (fun p ↦ V p.1 p.2 *
        (simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)) 2 ρ) atTop (𝓝 0) := by
  -- The diffusion coefficient is measurable away from the null initial-time slice.
  have hV : AEStronglyMeasurable (Function.uncurry V) ρ := by
    have hcover : ∀ᵐ p ∂ρ, p ∈ ⋃ k : ℕ, Ioc 0 (k : ℝ≥0) ×ˢ (univ : Set Ω) := by
      refine ae_iff.2 (measure_mono_null (fun p hp ↦ ?_) hρ₀)
      obtain ⟨k, hk⟩ := exists_nat_ge p.1
      simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Ioc, mem_univ, and_true,
        not_exists, not_and, not_le] at hp
      simp only [mem_prod, mem_singleton_iff, mem_univ, and_true]
      by_contra h
      exact (hp k (pos_iff_ne_zero.2 h)).not_ge hk
    rw [← Measure.restrict_eq_self_of_ae_mem hcover]
    exact AEStronglyMeasurable.iUnion fun k ↦
      (hV₂ k).aestronglyMeasurable
  -- Weighting by a coefficient turns its products into predictable seminorms.
  have hweight {w g : ℝ≥0 × Ω → ℝ} {p : ℝ≥0∞} (hp : p ≠ ∞) (hw : AEStronglyMeasurable w ρ)
      (hg : AEStronglyMeasurable[ℱ.predictable] g (ρ.trim hm)) :
      eLpNorm (w * g) p ρ =
        eLpNorm g p ((ρ.withDensity fun x ↦ ‖w x‖ₑ ^ p.toReal).trim hm) := by
    rw [eLpNorm_trim_ae hm (hg.mono_ac ((withDensity_absolutelyContinuous _ _).trim hm)),
      ← eLpNorm_smul_eq_eLpNorm_withDensity hw
        (aestronglyMeasurable_of_aestronglyMeasurable_trim hm hg) hp]
    simp only [Pi.mul_def, smul_eq_mul]
  have hzero (d : ℝ≥0 × Ω → ℝ≥0∞) :
      (ρ.withDensity d).trim hm ({0} ×ˢ (univ : Set Ω)) = 0 := by
    rw [trim_measurableSet_eq hm (by
      simpa only [NNReal.bot_eq_zero] using
        measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ) MeasurableSet.univ)]
    exact withDensity_absolutelyContinuous _ _ hρ₀
  let μ := (ρ.withDensity fun p ↦ ‖Function.uncurry D p‖ₑ ^ (1 : ℝ≥0∞).toReal).trim hm
  let ν := (ρ.withDensity fun p ↦ ‖Function.uncurry V p‖ₑ ^ (2 : ℝ≥0∞).toReal).trim hm
  have : IsFiniteMeasure
      (ρ.withDensity fun p ↦ ‖Function.uncurry D p‖ₑ ^ (1 : ℝ≥0∞).toReal) :=
    isFiniteMeasure_withDensity
      (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top one_ne_zero (by simp)
        hD₁.eLpNorm_lt_top).ne
  have hνfin (t : ℝ≥0) : ν (Ioc 0 t ×ˢ (univ : Set Ω)) ≠ ∞ := by
    have hrect := measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 t MeasurableSet.univ
    rw [trim_measurableSet_eq hm hrect, withDensity_apply _ (hm _ hrect)]
    exact (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top two_ne_zero (by simp)
      (hV₂ t).eLpNorm_lt_top).ne
  have hH₁ : MemLp (Function.uncurry H) 1 μ := by
    rw [memLp_iff, ← hweight (by simp) hD₁.aestronglyMeasurable hH]
    exact hHD₁.eLpNorm_lt_top
  have hH₂ : MemLp (Function.uncurry H) 2 ν := by
    rw [memLp_iff, ← hweight (by simp) hV hH]
    exact hHV₂.eLpNorm_lt_top
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, hlim₁, hlim₂⟩ :=
    ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one_two μ ν hνfin (hzero _) (hzero _) hH₁ hH₂
  have herr (k : ℕ) : AEStronglyMeasurable[ℱ.predictable]
      (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) (ρ.trim hm) :=
    (isStronglyPredictable_simpleHolding (ha k)).aestronglyMeasurable.sub hH
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_, ?_⟩
  · convert hlim₁ using 1
    ext k
    exact hweight (by simp) hD₁.aestronglyMeasurable (herr k)
  · convert hlim₂ using 1
    ext k
    exact hweight (by simp) hV (herr k)

/-- On the finite-horizon Lebesgue-time × sample measure, one stock holding is approximated
simultaneously in its drift and diffusion gains coefficients. The coefficients need only be
almost-everywhere strongly measurable for the time-product sigma-algebra, as progressive
coefficients are, while the holding need only be almost-everywhere predictable for
`ℱ.predictableMeasure P T`. The drift coefficient and gains need L¹, and the diffusion
coefficient and gains need L². -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_mul_one_two_timeMeasure
    (P : Measure Ω) [SFinite P] (T : ℝ≥0)
    {H D V : ℝ≥0 → Ω → ℝ}
    (hH : AEStronglyMeasurable[ℱ.predictable] (Function.uncurry H) (ℱ.predictableMeasure P T))
    (hD₁ : MemLp (Function.uncurry D) 1 ((TauCeti.Probability.timeMeasure T).prod P))
    (hV₂ : MemLp (Function.uncurry V) 2 ((TauCeti.Probability.timeMeasure T).prod P))
    (hHD₁ : MemLp (Function.uncurry D * Function.uncurry H) 1
      ((TauCeti.Probability.timeMeasure T).prod P))
    (hHV₂ : MemLp (Function.uncurry V * Function.uncurry H) 2
      ((TauCeti.Probability.timeMeasure T).prod P)) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      Tendsto (fun k ↦ eLpNorm (fun p ↦ D p.1 p.2 *
        (simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)) 1
          ((TauCeti.Probability.timeMeasure T).prod P)) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ eLpNorm (fun p ↦ V p.1 p.2 *
        (simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)) 2
          ((TauCeti.Probability.timeMeasure T).prod P)) atTop (𝓝 0) :=
  ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_mul_one_two ℱ.predictable_le_prod _
    (by simp [Measure.prod_prod]) (ℱ.predictableMeasure_def P T ▸ hH) hD₁
    (fun t ↦ hV₂.restrict _) hHD₁ hHV₂

end MeasureTheory.Filtration
