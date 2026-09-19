/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Integrals of unbounded functions along weakly convergent probability measures

Weak convergence `μᵢ ⇀ μ` of probability measures is defined by convergence of the integrals of
bounded continuous functions. For an *unbounded* continuous function `g : Ω → ℝ≥0` the integrals
`∫⁻ g ∂μᵢ` need not converge to `∫⁻ g ∂μ`: mass escaping to the region where `g` is large can
carry a non-vanishing share of the integral. This file proves that this is the only obstruction.
The integrals converge exactly when the tails of `g` are *uniformly integrable along the family*:
for every `ε > 0` there is a level `R` such that eventually `∫⁻ x in {x | R ≤ g x}, g x ∂μᵢ ≤ ε`.

This is the measure-theoretic core of the characterization of convergence in the `p`-Wasserstein
distance by weak convergence together with convergence of `p`-moments, where `g` is the `p`-th
power of the distance to a basepoint.

Both directions compare `g` with its truncations `min g R`, which are bounded continuous and hence
have converging integrals, and use that `g - R` and the tail `g` on `{x | 2 R ≤ g x}` control
each other. No metric structure on `Ω` and no finiteness of `∫⁻ g ∂μ` is needed for the
sufficiency of the tail condition; the necessity needs `∫⁻ g ∂μ ≠ ∞`.

## Main statements

* `TauCeti.tendsto_lintegral_of_tendsto_probabilityMeasure` — uniformly integrable tails along a
  weakly convergent family give convergence of the integrals;
* `TauCeti.exists_setLIntegral_le_of_tendsto_lintegral` — conversely, convergence of the
  integrals to a finite limit gives uniformly integrable tails;
* `TauCeti.tendsto_lintegral_iff_forall_exists_setLIntegral_le` — the resulting equivalence.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd edition, Wiley 1999, Theorems 3.5
  and 3.6, stated there for real random variables converging in distribution.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 6.8,
  where this tail condition defines weak convergence in `P_p`.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
  {g : Ω → ℝ≥0}

/-- The truncations `min g R` of a continuous function are bounded continuous, so their integrals
converge along a weakly convergent family. -/
private theorem tendsto_lintegral_min (hg : Continuous g) (h : Tendsto μs L (𝓝 μ)) (R : ℝ≥0) :
    Tendsto (fun i ↦ ∫⁻ x, min (g x : ℝ≥0∞) R ∂(μs i : Measure Ω)) L
      (𝓝 (∫⁻ x, min (g x : ℝ≥0∞) R ∂(μ : Measure Ω))) := by
  let f : BoundedContinuousFunction Ω ℝ≥0 := BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ min (g x) R, hg.min continuous_const⟩ R fun x y ↦ by
      rw [NNReal.dist_eq]
      exact abs_sub_le_of_nonneg_of_le (by positivity) (by exact_mod_cast min_le_right _ _)
        (by positivity) (by exact_mod_cast min_le_right _ _)
  simpa [f, ENNReal.coe_min] using ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 h f

/-- The lower half of the convergence holds with no tail condition: along a weakly convergent
family the integral of a continuous function can only drop in the limit. -/
private theorem eventually_lt_lintegral (hg : Continuous g) (h : Tendsto μs L (𝓝 μ))
    {a : ℝ≥0∞} (ha : a < ∫⁻ x, g x ∂(μ : Measure Ω)) :
    ∀ᶠ i in L, a < ∫⁻ x, g x ∂(μs i : Measure Ω) := by
  have hmono : Tendsto (fun n : ℕ ↦ ∫⁻ x, min (g x : ℝ≥0∞) ((n : ℝ≥0) : ℝ≥0∞) ∂(μ : Measure Ω))
      atTop (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n ↦ ?_)
      (.of_forall fun x m n hmn ↦ ?_) (.of_forall fun x ↦ ?_)
    · exact ((measurable_coe_nnreal_ennreal.comp hg.measurable).min
        measurable_const).aemeasurable
    · exact min_le_min_left _ (by exact_mod_cast hmn)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈g x⌉₊] with n hn
      refine (min_eq_left ?_).symm
      exact_mod_cast (Nat.le_ceil (g x)).trans (by exact_mod_cast hn)
  obtain ⟨n, hn⟩ := (hmono.eventually (lt_mem_nhds ha)).exists
  filter_upwards [(tendsto_lintegral_min hg h n).eventually (lt_mem_nhds hn)] with i hi
  exact hi.trans_le (lintegral_mono fun x ↦ min_le_left _ _)

/-- **Uniformly integrable tails give convergence of integrals.** Along a weakly convergent family
of probability measures, the integrals of a continuous function `g : Ω → ℝ≥0` converge as soon as
its tails are uniformly small: for every `ε > 0` there is a level `R` beyond which eventually the
integral of `g` is at most `ε`. -/
theorem tendsto_lintegral_of_tendsto_probabilityMeasure (hg : Continuous g)
    (h : Tendsto μs L (𝓝 μ))
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0,
      ∀ᶠ i in L, ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) ≤ ε) :
    Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))) := by
  refine tendsto_order.2 ⟨fun a ha ↦ eventually_lt_lintegral hg h ha, fun a ha ↦ ?_⟩
  obtain ⟨b, hb, hba⟩ := exists_between ha
  obtain ⟨r, hr, hbr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hba
  obtain ⟨R, hR⟩ := htail r (by exact_mod_cast hr)
  have hmin : ∫⁻ x, min (g x : ℝ≥0∞) R ∂(μ : Measure Ω) < b :=
    (lintegral_mono fun x ↦ min_le_left _ _).trans_lt hb
  have hgm : Measurable fun x ↦ (g x : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hg.measurable
  filter_upwards [(tendsto_lintegral_min hg h R).eventually (gt_mem_nhds hmin), hR] with i hi hRi
  calc ∫⁻ x, g x ∂(μs i : Measure Ω)
      ≤ ∫⁻ x, min (g x : ℝ≥0∞) R + {x | R ≤ g x}.indicator (fun x ↦ (g x : ℝ≥0∞)) x
          ∂(μs i : Measure Ω) := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : R ≤ g x
        · simp [hx]
        · have : (g x : ℝ≥0∞) ≤ R := by exact_mod_cast (not_le.1 hx).le
          simp [hx, this]
    _ = ∫⁻ x, min (g x : ℝ≥0∞) R ∂(μs i : Measure Ω) +
          ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) := by
        rw [lintegral_add_left (hgm.min measurable_const),
          lintegral_indicator (measurableSet_le measurable_const hg.measurable)]
    _ < b + r :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.coe_ne_top hRi) hi hRi
    _ < a := hbr

/-- **Convergence of integrals gives uniformly integrable tails.** If a continuous function
`g : Ω → ℝ≥0` has finite integral against the limit of a weakly convergent family of probability
measures, and its integrals converge along the family, then its tails are uniformly small: for
every `ε > 0` there is a level `R` beyond which eventually the integral of `g` is at most `ε`. -/
theorem exists_setLIntegral_le_of_tendsto_lintegral (hg : Continuous g) (h : Tendsto μs L (𝓝 μ))
    (hμ : ∫⁻ x, g x ∂(μ : Measure Ω) ≠ ∞)
    (hlim : Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) ≤ ε := by
  have hgm : Measurable fun x ↦ (g x : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hg.measurable
  have hexm (R : ℝ≥0) : Measurable fun x ↦ (g x : ℝ≥0∞) - R := hgm.sub measurable_const
  -- The excess `g - n` has vanishing integral against the limit, by dominated convergence.
  have hexc : Tendsto (fun n : ℕ ↦ ∫⁻ x, (g x : ℝ≥0∞) - ((n : ℝ≥0) : ℝ≥0∞) ∂(μ : Measure Ω))
      atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := (μ : Measure Ω))
      (F := fun (n : ℕ) x ↦ (g x : ℝ≥0∞) - ((n : ℝ≥0) : ℝ≥0∞)) (f := 0)
      (fun x ↦ (g x : ℝ≥0∞)) (fun n ↦ hexm n)
      (fun _ ↦ .of_forall fun _ ↦ tsub_le_self) hμ (.of_forall fun x ↦ ?_)
    · simpa using this
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈g x⌉₊] with n hn
    refine (tsub_eq_zero_of_le ?_).symm
    exact_mod_cast (Nat.le_ceil (g x)).trans (by exact_mod_cast hn)
  obtain ⟨n, hn⟩ := (hexc.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))).exists
  set R : ℝ≥0 := (n : ℝ≥0)
  -- The excess integral is the difference of the integral of `g` and of its truncation, and
  -- therefore converges along the family.
  have hmin_ne (ν : ProbabilityMeasure Ω) : ∫⁻ x, min (g x : ℝ≥0∞) R ∂(ν : Measure Ω) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (R : ℝ≥0∞) ∂(ν : Measure Ω)) (by simp)
      (lintegral_mono fun x ↦ min_le_right _ _)
  have hsub (ν : ProbabilityMeasure Ω) :
      ∫⁻ x, g x ∂(ν : Measure Ω) - ∫⁻ x, min (g x : ℝ≥0∞) R ∂(ν : Measure Ω) =
        ∫⁻ x, (g x : ℝ≥0∞) - R ∂(ν : Measure Ω) := by
    rw [← ENNReal.add_sub_cancel_right (a := ∫⁻ x, (g x : ℝ≥0∞) - R ∂(ν : Measure Ω))
      (hmin_ne ν), ← lintegral_add_left (hexm R)]
    simp_rw [tsub_add_min]
  have hexc_i : Tendsto (fun i ↦ ∫⁻ x, (g x : ℝ≥0∞) - R ∂(μs i : Measure Ω)) L
      (𝓝 (∫⁻ x, (g x : ℝ≥0∞) - R ∂(μ : Measure Ω))) := by
    simpa only [hsub] using ENNReal.Tendsto.sub hlim (tendsto_lintegral_min hg h R) (Or.inl hμ)
  refine ⟨2 * R, ?_⟩
  filter_upwards [hexc_i.eventually (gt_mem_nhds hn)] with i hi
  -- Beyond the level `2 R`, the function is at most twice its excess over `R`.
  calc ∫⁻ x in {x | 2 * R ≤ g x}, g x ∂(μs i : Measure Ω)
      = ∫⁻ x, {x | 2 * R ≤ g x}.indicator (fun x ↦ (g x : ℝ≥0∞)) x ∂(μs i : Measure Ω) :=
        (lintegral_indicator (measurableSet_le measurable_const hg.measurable) _).symm
    _ ≤ ∫⁻ x, 2 * ((g x : ℝ≥0∞) - R) ∂(μs i : Measure Ω) := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : 2 * R ≤ g x
        · have h2 : (R : ℝ≥0∞) + R ≤ g x := by exact_mod_cast (two_mul R).symm.trans_le hx
          rw [indicator_of_mem (show x ∈ {x | 2 * R ≤ g x} from hx), two_mul]
          calc (g x : ℝ≥0∞) = (g x - R) + R :=
                (tsub_add_cancel_of_le (le_self_add.trans h2)).symm
            _ ≤ (g x - R) + (g x - R) := by
                gcongr
                exact ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top h2
        · simp [hx]
    _ = 2 * ∫⁻ x, (g x : ℝ≥0∞) - R ∂(μs i : Measure Ω) :=
        lintegral_const_mul _ (hexm R)
    _ ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- **Convergence of integrals of an unbounded function along weak convergence.** Along a weakly
convergent family of probability measures, the integrals of a continuous function `g : Ω → ℝ≥0`
with finite integral against the limit converge to that integral exactly when the tails of `g` are
uniformly small along the family. -/
theorem tendsto_lintegral_iff_forall_exists_setLIntegral_le (hg : Continuous g)
    (h : Tendsto μs L (𝓝 μ)) (hμ : ∫⁻ x, g x ∂(μ : Measure Ω) ≠ ∞) :
    Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0,
        ∀ᶠ i in L, ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) ≤ ε :=
  ⟨fun hlim _ hε ↦ exists_setLIntegral_le_of_tendsto_lintegral hg h hμ hlim hε,
    tendsto_lintegral_of_tendsto_probabilityMeasure hg h⟩

end TauCeti
