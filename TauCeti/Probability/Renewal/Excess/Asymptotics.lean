/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.KeyTheorem
public import TauCeti.Probability.Renewal.InfiniteMean
public import TauCeti.Probability.Renewal.Excess.Escape
public import TauCeti.Probability.Renewal.Excess.Limit

/-!
# Asymptotic behavior of the excess life of a renewal process

Let `T 0, T 1, …` be independent, identically distributed nonnegative interarrival times on `(Ω, P)`
with common law `F = P.map (T 0)` and excess life `E t = renewalExcess T t` at time `t : ℝ≥0`. This
file establishes the two asymptotic regimes of `E t` as `t → ∞`:

1. **Infinite-mean escape (`∫⁻ u, u ∂F = ∞`, lattice or nonlattice).** Since
   `{E t ≤ x} ⊆ {N (t + x) - N t ≥ 1}` on nonexplosive paths and every fixed-window renewal
   increment `(F.renewalFunction (t + x)).toReal - (F.renewalFunction t).toReal` vanishes as
   `t → ∞` (`MeasureTheory.Measure.tendsto_renewalFunction_add_sub_of_mean_eq_top`), the probability
   `P(E t ≤ x)` tends to `0` and `P(x < E t)` tends to `1` for every `x : ℝ≥0`, with no lattice or
   nonlattice assumption on `F`.
2. **Nonlattice equilibrium limit (`¬ F.IsLattice`).** When `F` has finite extended mean `μ`,
   applying Smith's key renewal theorem (`MeasureTheory.Measure.tendsto_renewalConv`) to the
   nonincreasing shifted-tail forcing `u ↦ F.real (Ioi (u + x))` in the excess-tail identity
   `P(x < E t) = (F((· + x, ∞)) ∗ U) t` proves that `P(x < E t)` converges to the equilibrium
   survival probability `F.equilibriumExcessLaw.real (Ioi x)`. Complementing gives sublevel
   convergence

   ```text
   P(E t ≤ x) ⟶ F.equilibriumExcessLaw.real (Iic x)
              = (1 / μ) * ∫ s in (0, x], P(s < T 0) ds,
   ```

   which in fact holds for **every** nonlattice law `F` (finite or infinite mean), since both sides
   vanish when `μ = ∞`. Under finite mean, `F.equilibriumExcessLaw` is a probability measure
   (`MeasureTheory.Measure.isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice`), giving
   pointwise convergence of `ProbabilityTheory.cdf` on all of `ℝ` and convergence in distribution
   (`MeasureTheory.TendstoInDistribution`) of `(E t : ℝ)` as `t → ∞`.

Throughout, neither strict measurability of the increments `T n` nor a separate nondegeneracy
hypothesis `P {T 0 = 0} < 1` is assumed: `IdentDistrib (T n) (T 0) P P` supplies almost-everywhere
measurability, `renewalExcess_congr_ae` upgrades to measurable modifications, and both
`¬ F.IsLattice` and infinite mean automatically imply `F {0} < 1`. Genuine atoms at zero
(`0 < F {0} < 1`) are allowed.

## Main results

* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_mean_eq_top`,
  `TauCeti.Probability.tendsto_measure_renewalExcess_le_of_mean_eq_top`,
  `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess_of_mean_eq_top`: infinite-mean excess
  escape `P(E t ≤ x) → 0` and `P(x < E t) → 1`, lattice or not.
* `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess`: nonlattice finite-mean survival limit
  `P(x < E t) → F.equilibriumExcessLaw.real (Ioi x)` via the key renewal theorem on the tail
  forcing.
* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le`,
  `TauCeti.Probability.tendsto_measure_renewalExcess_le`,
  `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_integral`: nonlattice sublevel limit
  `P(E t ≤ x) → F.equilibriumExcessLaw.real (Iic x) = (1 / μ) ∫_{(0, x]} P(s < T 0) ds`, valid for
  both finite and infinite mean.
* `TauCeti.Probability.tendsto_cdf_renewalExcess`,
  `TauCeti.Probability.tendstoInDistribution_renewalExcess`: pointwise CDF convergence on `ℝ` and
  convergence in distribution to any realization of `F.equilibriumExcessLaw` under finite mean.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, second
  edition, Wiley, 1971, Chapter XI, §4.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-! ### Measurable modification of almost-everywhere measurable increments -/

/-- Measurable modification of the increments `T n` supplied by `IdentDistrib (T n) (T 0) P P`. -/
private noncomputable def mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (n : ℕ) : Ω → ℝ≥0 :=
  ((hid n).aemeasurable_fst).mk (T n)

private lemma measurable_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (n : ℕ) :
    Measurable (mkMeasurable hid n) :=
  ((hid n).aemeasurable_fst).measurable_mk

private lemma ae_eq_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (n : ℕ) :
    T n =ᵐ[P] mkMeasurable hid n :=
  ((hid n).aemeasurable_fst).ae_eq_mk

private lemma iIndepFun_mkMeasurable (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    iIndepFun (mkMeasurable hid) P :=
  hindep.congr (ae_eq_mkMeasurable hid)

private lemma identDistrib_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (n : ℕ) :
    IdentDistrib (mkMeasurable hid n) (mkMeasurable hid 0) P P :=
  (((hid n).aemeasurable_fst).identDistrib_mk.symm.trans (hid n)).trans
    ((hid 0).aemeasurable_fst).identDistrib_mk

private lemma map_mkMeasurable_zero (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    P.map (mkMeasurable hid 0) = P.map (T 0) :=
  Measure.map_congr (ae_eq_mkMeasurable hid 0).symm

private lemma measure_renewalExcess_le_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (t x : ℝ≥0) :
    P {ω | renewalExcess T t ω ≤ x} = P {ω | renewalExcess (mkMeasurable hid) t ω ≤ x} := by
  refine measure_congr ?_
  filter_upwards [renewalExcess_congr_ae (ae_eq_mkMeasurable hid)] with ω hω
  simp [hω t]

private lemma measureReal_renewalExcess_le_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (t x : ℝ≥0) :
    P.real {ω | renewalExcess T t ω ≤ x} =
      P.real {ω | renewalExcess (mkMeasurable hid) t ω ≤ x} := by
  simp only [measureReal_def, measure_renewalExcess_le_mkMeasurable hid t x]

private lemma measureReal_lt_renewalExcess_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (t x : ℝ≥0) :
    P.real {ω | x < renewalExcess T t ω} =
      P.real {ω | x < renewalExcess (mkMeasurable hid) t ω} := by
  simp only [measureReal_def]
  congr 1
  refine measure_congr ?_
  filter_upwards [renewalExcess_congr_ae (ae_eq_mkMeasurable hid)] with ω hω
  simp [hω t]

private lemma map_coe_renewalExcess_mkMeasurable (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (t : ℝ≥0) :
    P.map (fun ω ↦ (renewalExcess T t ω : ℝ)) =
      P.map (fun ω ↦ (renewalExcess (mkMeasurable hid) t ω : ℝ)) := by
  refine Measure.map_congr ?_
  filter_upwards [renewalExcess_congr_ae (ae_eq_mkMeasurable hid)] with ω hω
  simp [hω t]

/-! ### Infinite-mean excess escape -/

/-- **Infinite-mean excess escape.** For independent, identically distributed nonnegative increments
whose common law `P.map (T 0)` has infinite extended mean, lattice or nonlattice, `P(E t ≤ x) → 0`
as `t → ∞` for every finite threshold `x : ℝ≥0`. Zero increments are allowed. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hT' := measurable_mkMeasurable hid
  have hmap := map_mkMeasurable_zero hid
  have hmean' : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (mkMeasurable hid 0)) = ∞ := by rwa [hmap]
  have hF := (P.map (mkMeasurable hid 0)).measure_singleton_lt_one_of_lintegral_pos
    (f := fun u ↦ (u : ℝ≥0∞)) (a := 0) (by simp) (hmean' ▸ ENNReal.zero_lt_top)
  have hzero' : P {ω | mkMeasurable hid 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT' 0) (measurableSet_singleton 0)] at hF
  simp_rw [measureReal_renewalExcess_le_mkMeasurable hid _ x]
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hT' (iIndepFun_mkMeasurable hindep hid) (identDistrib_mkMeasurable hid) hzero' x
    ((P.map (mkMeasurable hid 0)).tendsto_renewalFunction_add_sub_of_mean_eq_top hmean' x)

/-- **Infinite-mean excess escape (`ℝ≥0∞` form).** When the interarrival law has infinite extended
mean, lattice or nonlattice, `P {E t ≤ x} → 0` in `ℝ≥0∞` as `t → ∞` for every `x : ℝ≥0`. -/
theorem tendsto_measure_renewalExcess_le_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have heq (t : ℝ≥0) : P {ω | renewalExcess T t ω ≤ x} =
      ENNReal.ofReal (P.real {ω | renewalExcess T t ω ≤ x}) :=
    (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x)

/-- **Infinite-mean excess tail limit.** When the interarrival law has infinite extended mean,
lattice or nonlattice, `P(x < E t) → 1` as `t → ∞` for every finite threshold `x : ℝ≥0`. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  have hT' := measurable_mkMeasurable hid
  have heq (t : ℝ≥0) : P.real {ω | x < renewalExcess T t ω} =
      1 - P.real {ω | renewalExcess T t ω ≤ x} := by
    rw [measureReal_lt_renewalExcess_mkMeasurable hid,
      measureReal_renewalExcess_le_mkMeasurable hid,
      ← probReal_compl_eq_one_sub (measurableSet_le (measurable_renewalExcess hT' t)
        measurable_const)]
    congr 1
    ext ω
    simp
  simp_rw [heq]
  simpa using tendsto_const_nhds.sub
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x)

/-! ### Nonlattice excess-life convergence -/

/-- **Asymptotic excess survival probability for nonlattice laws.** For i.i.d. nonnegative
increments whose common law `F = P.map (T 0)` is nonlattice and has finite extended mean, applying
Smith's key renewal theorem (`MeasureTheory.Measure.tendsto_renewalConv`) to the nonincreasing
shifted-tail forcing `u ↦ F.real (Ioi (u + x))` shows that `P(x < E t)` converges as `t → ∞` to
`F.equilibriumExcessLaw.real (Ioi x)`. Finiteness of the mean is needed here because
`F.equilibriumExcessLaw = 0` under infinite mean whereas `P(x < E t) → 1`
(`tendsto_measureReal_lt_renewalExcess_of_mean_eq_top`). -/
theorem tendsto_measureReal_lt_renewalExcess
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  have hT' := measurable_mkMeasurable hid
  have hmap := map_mkMeasurable_zero hid
  have hF : (P.map (mkMeasurable hid 0)) {0} < 1 := by
    rw [hmap]
    exact Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  have hzero' : P {ω | mkMeasurable hid 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT' 0) (measurableSet_singleton 0)] at hF
  have htail : Antitone (fun u : ℝ≥0 ↦ (P.map (T 0)).real (Ioi (u + x))) :=
    fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr))
  simp_rw [measureReal_lt_renewalExcess_mkMeasurable hid _ x,
    measureReal_lt_renewalExcess hT' (iIndepFun_mkMeasurable hindep hid)
      (identDistrib_mkMeasurable hid) hzero' _ x, hmap]
  rw [Measure.equilibriumExcessLaw_real_Ioi_eq_integral_tail_add]
  exact (P.map (T 0)).tendsto_renewalConv hNL htail
    ((P.map (T 0)).integrableOn_Ioi_measureReal_tail_add x hmean)

/-- **Asymptotic excess sublevel probability for nonlattice laws.** For i.i.d. nonnegative
increments whose common law `F = P.map (T 0)` is nonlattice, `P(E t ≤ x)` converges as `t → ∞` to
`F.equilibriumExcessLaw.real (Iic x)` at every threshold `x : ℝ≥0`. No finite-mean assumption is
needed: under finite mean the limit is a probability distribution function, while under infinite
mean both the limit (`equilibriumExcessLaw_eq_zero_of_mean_eq_top`) and the excess sublevel
probability vanish. -/
theorem tendsto_measureReal_renewalExcess_le
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simp only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean, measureReal_zero,
      Pi.zero_apply]
    exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x
  · have := hindep.isProbabilityMeasure
    have := ((P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice hNL).2
      hmean
    have hT' := measurable_mkMeasurable hid
    have heq (t : ℝ≥0) : P.real {ω | renewalExcess T t ω ≤ x} =
        1 - P.real {ω | x < renewalExcess T t ω} := by
      rw [measureReal_renewalExcess_le_mkMeasurable hid,
        measureReal_lt_renewalExcess_mkMeasurable hid,
        ← probReal_compl_eq_one_sub (measurableSet_lt measurable_const
          (measurable_renewalExcess hT' t))]
      congr 1
      ext ω
      simp
    have hcomp : (P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)) =
        1 - (P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)) := by
      rw [← probReal_compl_eq_one_sub measurableSet_Ioi, compl_Ioi]
    simp_rw [heq, hcomp]
    exact tendsto_const_nhds.sub (tendsto_measureReal_lt_renewalExcess hindep hid hNL hmean x)

/-- **Asymptotic excess sublevel probability (`ℝ≥0∞` form).** For i.i.d. nonlattice increments,
`P {E t ≤ x} → (P.map (T 0)).equilibriumExcessLaw (Iic x)` in `ℝ≥0∞` as `t → ∞`, for both finite
and infinite interarrival mean. -/
theorem tendsto_measure_renewalExcess_le
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw (Iic (x : ℝ)))) := by
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simp only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean, FunLike.coe_zero,
      Pi.zero_apply]
    exact tendsto_measure_renewalExcess_le_of_mean_eq_top hindep hid hmean x
  · have := hindep.isProbabilityMeasure
    have := ((P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice hNL).2
      hmean
    have heq (t : ℝ≥0) : P {ω | renewalExcess T t ω ≤ x} =
        ENNReal.ofReal (P.real {ω | renewalExcess T t ω ≤ x}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    have hlim : (P.map (T 0)).equilibriumExcessLaw (Iic (x : ℝ)) =
        ENNReal.ofReal ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ))) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    simp_rw [heq]
    rw [hlim]
    simpa only [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_measureReal_renewalExcess_le hindep hid hNL x)

/-- **Integrated-tail formula for the limiting excess distribution.** For i.i.d. nonlattice
increments, `P(E t ≤ x)` converges as `t → ∞` to `(1 / 𝔼[T 0]) * ∫ s in (0, x], P(s < T 0) ds`,
written directly in terms of `T 0` and `P`. Taking the reciprocal in `ℝ≥0∞` before `toReal` covers
both finite and infinite interarrival mean. -/
theorem tendsto_measureReal_renewalExcess_le_integral
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 (((∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), P.real {ω | s < (T 0 ω : ℝ)})) := by
  have := hindep.isProbabilityMeasure
  have hmean_eq : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P :=
    lintegral_map' measurable_coe_nnreal_ennreal.aemeasurable (hid 0).aemeasurable_fst
  have htail_eq (s : ℝ) : (P.map (T 0)).real {u | s < (u : ℝ)} = P.real {ω | s < (T 0 ω : ℝ)} := by
    simp only [measureReal_def, Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst
      (measurableSet_lt measurable_const measurable_coe_nnreal_real)]
    rfl
  have hrhs : (P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)) =
      ((∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), P.real {ω | s < (T 0 ω : ℝ)} := by
    rw [Measure.equilibriumExcessLaw_real_Iic, hmean_eq]
    simp_rw [htail_eq]
  rw [← hrhs]
  exact tendsto_measureReal_renewalExcess_le hindep hid hNL x

/-- **Pointwise CDF convergence of the excess life.** For i.i.d. nonlattice increments of finite
extended mean, the cumulative distribution function of the real-valued excess at time `t` converges
at every `x : ℝ` (including zero and negative thresholds) to
`cdf (P.map (T 0)).equilibriumExcessLaw x`. Finiteness of the mean is required here because
`ProbabilityTheory.cdf` normalizes the zero measure to a unit-mass default via `condCDF`, whereas
`F.equilibriumExcessLaw` is a probability measure precisely when the mean is finite. -/
theorem tendsto_cdf_renewalExcess
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  have hT' := measurable_mkMeasurable hid
  have hmap := map_mkMeasurable_zero hid
  have hF : (P.map (mkMeasurable hid 0)) {0} < 1 := by
    rw [hmap]
    exact Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  have hzero' : P {ω | mkMeasurable hid 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT' 0) (measurableSet_singleton 0)] at hF
  have hmean' : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (mkMeasurable hid 0)) ≠ ∞ := by rwa [hmap]
  have hNL' : ¬ (P.map (mkMeasurable hid 0)).IsLattice := by rwa [hmap]
  simp_rw [map_coe_renewalExcess_mkMeasurable hid, ← hmap]
  exact tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc hT'
    (iIndepFun_mkMeasurable hindep hid) (identDistrib_mkMeasurable hid) hzero' hmean'
    ((P.map (mkMeasurable hid 0)).tendsto_renewalMeasure_real_Ioc hNL') x

/-- **Convergence in distribution of the excess life.** For i.i.d. nonlattice increments of finite
extended mean, the real-valued excess `(renewalExcess T t · : ℝ)` converges in distribution along
`atTop : Filter ℝ≥0` to any random variable `Z` with law `(P.map (T 0)).equilibriumExcessLaw`.
Precomposing with `MeasureTheory.TendstoInDistribution.comp_tendsto` specializes this along any
observation-time family `t : ι → ℝ≥0` tending to `atTop` along an arbitrary filter. -/
theorem tendstoInDistribution_renewalExcess
    [IsProbabilityMeasure P] (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q) :
    TendstoInDistribution (fun t ω ↦ (renewalExcess T t ω : ℝ)) atTop
      Z (fun _ ↦ P) Q := by
  refine TendstoInDistribution.of_tendsto_cdf
    (fun t ↦ measurable_coe_nnreal_real.comp_aemeasurable
      (aemeasurable_renewalExcess (fun n ↦ (hid n).aemeasurable_fst) t))
    hZ.aemeasurable fun x ↦ ?_
  rw [hZ.map_eq]
  exact tendsto_cdf_renewalExcess hindep hid hNL hmean x

end TauCeti.Probability
