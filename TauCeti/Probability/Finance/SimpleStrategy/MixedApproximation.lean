/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
public import TauCeti.MeasureTheory.Function.LpSeminorm.WithDensity
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Simultaneous drift and diffusion approximation of holdings

A stock holding must be approximated in two different norms: absolute drift variation
uses L¹, whereas diffusion energy uses L². Approximating the drift and diffusion
coefficients independently does not produce a single sequence of trading holdings.

For two finite measures on the predictable sigma-algebra, every predictable holding
in L¹ of the first and L² of the second has one sequence of bounded finite-grid
approximants converging in both norms. The measures may be mutually singular or vanish;
in particular no lower bound on the volatility or drift is needed. Each trading height
is known at the left endpoint, and every grid starts at zero.

The construction uses Mathlib's `SimpleFunc.approxOn` quantizations in both norms,
followed by the existing predictable L² grid density theorem for the sum measure.
It does not require the original holding to be square integrable for the drift measure.
For stock trading, use absolute drift density for the first measure and squared
diffusion density for the second, on the declared finite horizon. Finiteness of these
measures is an expected-variation/energy hypothesis; almost-sure local integrability
alone requires a separate localization argument.

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
L¹ and L² for two finite measures. These are the distinct drift-variation and diffusion-
energy topologies for stock holdings. No L² hypothesis for the first measure is imposed. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_one_two
    (μ ν : @Measure (ℝ≥0 × Ω) ℱ.predictable) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ₀ : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    (hν₀ : ν ({0} ×ˢ (univ : Set Ω)) = 0)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
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
  -- Use the same finite-valued quantizations for both norms.
  let f (k : ℕ) := SimpleFunc.approxOn (Function.uncurry H) hH.measurable univ 0 (mem_univ _) k
  have happrox {p : ℝ≥0∞} {ρ : Measure (ℝ≥0 × Ω)} (hp : p ≠ ∞)
      (hHp : MemLp (Function.uncurry H) p ρ) :
      Tendsto (fun k ↦ eLpNorm (fun x ↦ f k x - H x.1 x.2) p ρ) atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm hH.measurable (mem_univ _) hp
    · simp
    · simpa only [sub_zero] using hHp.eLpNorm_lt_top
  have hzero : (μ + ν) ({0} ×ˢ (univ : Set Ω)) = 0 := by simp [hμ₀, hν₀]
  -- Bounded quantizations belong to L² of the sum measure and admit trading grids.
  have hex (k : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt (μ + ν)
    (fun _ _ _ _ ↦ measure_ne_top _ _) hzero
    (H := fun t ω ↦ f k (t, ω))
    ((f k).memLp_of_isFiniteMeasure 2 (μ + ν) |>.ae_eq (.of_forall fun p ↦ by
      rcases p with ⟨t, ω⟩
      simp only [Function.uncurry_apply_pair]))
    (ε := (k : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  choose n τ a C hτ₀ hτ ha hb herr using hex
  let E (k : ℕ) (p : ℝ≥0 × Ω) := simpleHolding (τ k) (n k) (a k) p.1 p.2 - f k p
  have hEm (k : ℕ) : StronglyMeasurable (E k) :=
    (isStronglyPredictable_simpleHolding (ha k)).sub (f k).stronglyMeasurable
  -- L² control for the sum measure controls L² diffusion and L¹ drift errors.
  have hsum : Tendsto (fun k ↦ eLpNorm (E k) 2 (μ + ν)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ bot_le) (fun k ↦ (herr k).le)
  have hdiff : Tendsto (fun k ↦ eLpNorm (E k) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ bot_le) (fun k ↦ eLpNorm_le_add_measure_left _ _ _)
  have hdrift : Tendsto (fun k ↦ eLpNorm (E k) 1 μ) atTop (𝓝 0) := by
    have hbound (k : ℕ) : eLpNorm (E k) 1 μ ≤
        eLpNorm (E k) 2 (μ + ν) * μ univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) :=
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (hEm k).aestronglyMeasurable).trans
        (by simpa using mul_le_mul_left (eLpNorm_le_add_measure_right (E k) μ ν (p := 2)) _)
    have hlim := ENNReal.Tendsto.mul_const hsum
      (b := μ univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))) (Or.inr (by finiteness))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hlim) (fun _ ↦ bot_le) hbound
  -- Add the grid-to-quantization errors to the quantization-to-holding errors.
  have htotal (p : ℝ≥0∞) (ρ : Measure (ℝ≥0 × Ω)) (hp : 1 ≤ p) (hpfin : p ≠ ∞)
      (hE : Tendsto (fun k ↦ eLpNorm (E k) p ρ) atTop (𝓝 0))
      (hHp : MemLp (Function.uncurry H) p ρ) :
      Tendsto (fun k ↦ eLpNorm
        (fun x ↦ simpleHolding (τ k) (n k) (a k) x.1 x.2 - H x.1 x.2) p ρ) atTop (𝓝 0) := by
    have hbound (k : ℕ) :
        eLpNorm (fun x ↦ simpleHolding (τ k) (n k) (a k) x.1 x.2 - H x.1 x.2) p ρ ≤
          eLpNorm (E k) p ρ + eLpNorm (fun x ↦ f k x - H x.1 x.2) p ρ := by
      convert eLpNorm_add_le (f := E k) (g := fun x ↦ f k x - H x.1 x.2) (μ := ρ) hp using 1
      congr 1
      ext x
      simp [E]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hE.add (happrox hpfin hHp)) (fun _ ↦ bot_le) hbound
  exact ⟨n, τ, a, C, hτ₀, hτ, ha, hb, htotal 1 μ le_rfl (by simp) hdrift hH₁,
    htotal 2 ν (by norm_num) (by simp) hdiff hH₂⟩

/-- Approximate one stock holding simultaneously in its drift and diffusion gains
coefficients. On finite-horizon predictable time-product measure, take `D = μ S` and
`V = σ S`. The coefficient and gains hypotheses are only L¹ for drift and L² for diffusion;
no nonvanishing, boundedness or continuity assumption on the coefficients is needed.
This is an approximation theorem, not a construction of the stochastic integral. -/
theorem exists_seq_simpleHolding_tendsto_stock_gains
    (ρ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    (hρ₀ : ρ ({0} ×ˢ (univ : Set Ω)) = 0)
    {H D V : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    (hD₁ : MemLp (Function.uncurry D) 1 ρ) (hV₂ : MemLp (Function.uncurry V) 2 ρ)
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
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let μ := ρ.withDensity (fun p ↦ ‖Function.uncurry D p‖ₑ ^ (1 : ℝ≥0∞).toReal)
  let ν := ρ.withDensity (fun p ↦ ‖Function.uncurry V p‖ₑ ^ (2 : ℝ≥0∞).toReal)
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (by simp) hD₁.eLpNorm_lt_top).ne
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp) hV₂.eLpNorm_lt_top).ne
  have hH₁ : MemLp (Function.uncurry H) 1 μ := by
    rw [memLp_iff, ← eLpNorm_mul_eq_withDensity hD₁.aestronglyMeasurable
      hH.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by simp)]
    exact hHD₁.eLpNorm_lt_top
  have hH₂ : MemLp (Function.uncurry H) 2 ν := by
    rw [memLp_iff, ← eLpNorm_mul_eq_withDensity hV₂.aestronglyMeasurable
      hH.aestronglyMeasurable (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)]
    exact hHV₂.eLpNorm_lt_top
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, hlim₁, hlim₂⟩ :=
    ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one_two μ ν
      (withDensity_absolutelyContinuous _ _ hρ₀) (withDensity_absolutelyContinuous _ _ hρ₀)
      hH hH₁ hH₂
  have herr (k : ℕ) : AEStronglyMeasurable
      (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) ρ :=
    ((isStronglyPredictable_simpleHolding (ha k)).sub hH).aestronglyMeasurable
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_, ?_⟩
  · convert hlim₁ using 1
    ext k
    simpa only [μ, Function.uncurry_def, Pi.mul_def] using
      eLpNorm_mul_eq_withDensity hD₁.aestronglyMeasurable (herr k)
        (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by simp)
  · convert hlim₂ using 1
    ext k
    simpa only [ν, Function.uncurry_def, Pi.mul_def] using
      eLpNorm_mul_eq_withDensity hV₂.aestronglyMeasurable (herr k)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)

end MeasureTheory.Filtration
