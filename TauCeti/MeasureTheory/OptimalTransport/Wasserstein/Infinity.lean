/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
-- Proof-only: weak compactness of couplings, closed sublevel sets of `π ↦ ∫⁻ c ∂π`, and the
-- `L^∞` seminorm as the limit of the `Lᵖ` seminorms.
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.OptimalTransport.Compactness

/-!
# The Wasserstein distance at the infinite exponent

At `p = ∞` the Wasserstein distance `TauCeti.wassersteinEDist ∞ μ ν` is the infimum, over the
couplings `π` of `μ` and `ν`, of the `π`-essential supremum of the ground distance
(`TauCeti.wassersteinEDist_top`). This file proves, on a Polish metric space, the two facts that
tie this endpoint to the finite exponents and make it usable:

* the infimum is attained, between any two finite measures that admit a coupling;
* for probability measures, `W_∞ (μ, ν)` is the supremum of the finite-exponent distances
  `W_p (μ, ν)`, and it is their limit as `p → ∞`.

Both are identities in `[0, ∞]`: no bounded support or moment hypothesis is needed, since a
divergent supremum and an infinite `W_∞` are allowed on both sides. Monotonicity in the exponent,
`TauCeti.wassersteinEDist_mono_exponent`, makes the supremum over all finite exponents the same as
the supremum over `1 ≤ p < ∞`.

## Main statements

* `TauCeti.wassersteinEDist_top_eq_iSup` — `W_∞ (μ, ν) = ⨆ p < ∞, W_p (μ, ν)` when `μ` is a
  probability measure;
* `TauCeti.tendsto_wassersteinEDist_atTop` — `W_p (μ, ν) → W_∞ (μ, ν)` as `p → ∞`;
* `TauCeti.exists_isCoupling_eLpNorm_top_eq_wassersteinEDist` — attainment of the infimum defining
  `W_∞`, between finite measures that admit a coupling.

## Implementation notes

Monotonicity gives `⨆ p < ∞, W_p ≤ W_∞`. For the other inequality, write `L` for the supremum.
The couplings `π` with `‖d‖_{Lⁿ(π)} ≤ L` form a decreasing sequence of nonempty weakly closed
subsets of the weakly compact set of couplings: nonempty by attainment at finite exponents, closed
because `π ↦ ∫⁻ dⁿ ∂π` is lower semicontinuous. A coupling in their intersection has all its `Lⁿ`
displacements at most `L`, hence its essential-supremum displacement is at most `L`, because the
`Lⁿ` seminorms of a function converge to its essential supremum
(`TauCeti.tendsto_eLpNorm_atTop`). That coupling attains `W_∞`, which is how attainment and the
supremum formula come out of the same argument.

## References

* C. R. Givens and R. M. Shortt, *A class of Wasserstein metrics for probability distributions*,
  Michigan Math. J. 31 (1984), 231–240, Proposition 1: on a Polish space, `W_∞` is the limit of
  the `W_p` as `p → ∞`, and the infimum defining it is attained.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X]

/-- A coupling of two probability measures whose essential-supremum displacement is bounded by
the supremum of the finite-exponent Wasserstein distances. -/
private theorem exists_isCoupling_eLpNorm_top_le_iSup (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∃ π, IsCoupling π μ ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ π ≤ ⨆ p : ℝ≥0, wassersteinEDist p μ ν := by
  let L := ⨆ p : ℝ≥0, wassersteinEDist p μ ν
  let d : X × X → ℝ≥0∞ := fun z ↦ edist z.1 z.2
  let μ' : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  let ν' : ProbabilityMeasure X := ⟨ν, inferInstance⟩
  -- The exponents `n + 1`, with the `Lⁿ⁺¹` bound read as a bound on the integral of `dⁿ⁺¹`.
  let q : ℕ → ℝ≥0 := fun n ↦ n + 1
  have hq0 (n : ℕ) : (q n : ℝ≥0∞) ≠ 0 := by simp [q]
  have hqpos (n : ℕ) : 0 < (q n : ℝ) := by positivity
  have hiff (n : ℕ) (π : Measure (X × X)) :
      ∫⁻ z, d z ^ (q n : ℝ) ∂π ≤ L ^ (q n : ℝ) ↔ eLpNorm d (q n) π ≤ L := by
    have h := eLpNorm_rpow_eq_lintegral (hq0 n) ENNReal.coe_ne_top d π
    rw [ENNReal.coe_toReal] at h
    rw [← h, ENNReal.rpow_le_rpow_iff (hqpos n)]
  let t : ℕ → Set (ProbabilityMeasure (X × X)) := fun n ↦
    {π | IsCoupling π.toMeasure μ ν} ∩ {π | ∫⁻ z, d z ^ (q n : ℝ) ∂π.toMeasure ≤ L ^ (q n : ℝ)}
  have htcl (n : ℕ) : IsClosed (t n) :=
    (isClosed_setOfPred_isCoupling_of_polishSpace μ' ν').inter
      (isClosed_setOfPred_lintegral_le_probabilityMeasure
        (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous _)
  have ht0 : IsCompact (t 0) :=
    (isCompact_setOfPred_isCoupling_of_polishSpace μ' ν').inter_right
      (isClosed_setOfPred_lintegral_le_probabilityMeasure
        (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous _)
  have htd (n : ℕ) : t (n + 1) ⊆ t n := by
    rintro π ⟨hπ, hle⟩
    refine ⟨hπ, (hiff n π).2 ((eLpNorm_le_eLpNorm_of_exponent_le ?_
      measurable_edist.aestronglyMeasurable).trans ((hiff (n + 1) π).1 hle))⟩
    simp [q]
  have htn (n : ℕ) : (t n).Nonempty := by
    obtain ⟨π, hπ, hval⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist (hq0 n)
      ENNReal.coe_ne_top μ ν ⟨μ.prod ν, isCoupling_prod μ ν⟩
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    exact ⟨⟨π, this⟩, hπ, (hiff n π).2 (hval.trans_le (le_iSup (fun p : ℝ≥0 ↦
      wassersteinEDist p μ ν) (q n)))⟩
  obtain ⟨π, hπ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    ht0 htcl
  rw [mem_iInter] at hπ
  refine ⟨π, (hπ 0).1, ?_⟩
  -- Every `Lⁿ⁺¹` displacement of `π` is at most `L`, so its limit, the `L^∞` one, is too.
  have hq : Tendsto q atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_self_add) tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦ eLpNorm d (q n) π.toMeasure) atTop
      (𝓝 (eLpNorm d ∞ π.toMeasure)) :=
    (tendsto_eLpNorm_atTop measurable_edist.aestronglyMeasurable).comp hq
  exact le_of_tendsto' hlim fun n ↦ (hiff n π).1 (hπ n).2

/-- **`W_∞` is the supremum of the finite-exponent Wasserstein distances.** On a Polish metric
space, if `μ` is a probability measure then `W_∞ (μ, ν) = ⨆ p < ∞, W_p (μ, ν)` in `[0, ∞]`. By
monotonicity in the exponent the supremum may equally be taken over `1 ≤ p < ∞`. -/
theorem wassersteinEDist_top_eq_iSup (μ ν : Measure X) [IsProbabilityMeasure μ] :
    wassersteinEDist ∞ μ ν = ⨆ p : ℝ≥0, wassersteinEDist p μ ν := by
  refine le_antisymm ?_
    (iSup_le fun p ↦ wassersteinEDist_mono_exponent measurable_edist le_top μ ν)
  by_cases hcoup : ∃ π, IsCoupling π μ ν
  · obtain ⟨π₀, hπ₀⟩ := hcoup
    have : IsProbabilityMeasure ν := ⟨by rw [← hπ₀.measure_univ_eq, measure_univ]⟩
    obtain ⟨π, hπ, hle⟩ := exists_isCoupling_eLpNorm_top_le_iSup μ ν
    exact (wassersteinEDist_le hπ ∞).trans hle
  · simp [wassersteinEDist_eq_top_of_not_exists_isCoupling hcoup]

/-- **`W_p` converges to `W_∞`.** On a Polish metric space, if `μ` is a probability measure then
`W_p (μ, ν)` tends to `W_∞ (μ, ν)` in `[0, ∞]` as the exponent `p` tends to infinity. -/
theorem tendsto_wassersteinEDist_atTop (μ ν : Measure X) [IsProbabilityMeasure μ] :
    Tendsto (fun p : ℝ≥0 ↦ wassersteinEDist p μ ν) atTop (𝓝 (wassersteinEDist ∞ μ ν)) := by
  rw [wassersteinEDist_top_eq_iSup]
  exact tendsto_atTop_iSup fun p q hpq ↦
    wassersteinEDist_mono_exponent measurable_edist (ENNReal.coe_le_coe.2 hpq) μ ν

/-- **Attainment at the infinite exponent.** On a Polish metric space, the infimum defining
`W_∞ (μ, ν)` between two finite measures that admit a coupling is a minimum: some coupling has
essential-supremum displacement exactly `W_∞ (μ, ν)`. -/
theorem exists_isCoupling_eLpNorm_top_eq_wassersteinEDist (μ ν : Measure X) [IsFiniteMeasure μ]
    (hcoup : ∃ π, IsCoupling π μ ν) :
    ∃ π, IsCoupling π μ ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ π = wassersteinEDist ∞ μ ν := by
  obtain ⟨π₀, hπ₀⟩ := hcoup
  rcases eq_zero_or_neZero μ with rfl | _
  · -- The only coupling of zero measures is zero, whose objective vanishes.
    have hπ₀0 : π₀ = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← Measure.fst_univ, hπ₀.fst_eq, Measure.coe_zero,
        Pi.zero_apply]
    subst hπ₀0
    exact ⟨0, hπ₀, le_antisymm (by simp) (wassersteinEDist_le hπ₀ ∞)⟩
  -- Normalise the marginals, attain the probability problem, and rescale its plan.
  obtain ⟨m, hm⟩ : ∃ m, μ Set.univ = m := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := hm ▸ by simp [NeZero.ne μ]
  have hmtop : m ≠ ∞ := hm ▸ measure_ne_top μ _
  have : IsProbabilityMeasure (m⁻¹ • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, hm, ENNReal.inv_mul_cancel hm0 hmtop]⟩
  have : IsProbabilityMeasure (m⁻¹ • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, ← hπ₀.measure_univ_eq, hm,
      ENNReal.inv_mul_cancel hm0 hmtop]⟩
  obtain ⟨π, hπ, hle⟩ := exists_isCoupling_eLpNorm_top_le_iSup (m⁻¹ • μ) (m⁻¹ • ν)
  have hscale : wassersteinEDist ∞ (m⁻¹ • μ) (m⁻¹ • ν) = wassersteinEDist ∞ μ ν := by
    simpa using wassersteinEDist_smul (p := ∞) (μ := μ) (ν := ν)
      (ENNReal.inv_ne_zero.mpr hmtop) (ENNReal.inv_ne_top.mpr hm0)
  have hcoup : IsCoupling (m • π) μ ν := by
    simpa [smul_smul, ENNReal.mul_inv_cancel hm0 hmtop] using hπ.smul m
  refine ⟨m • π, hcoup, le_antisymm ?_ (wassersteinEDist_le hcoup ∞)⟩
  rw [eLpNorm_smul_measure_of_ne_zero hm0, ← hscale, wassersteinEDist_top_eq_iSup]
  simpa using hle

end TauCeti
