/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Count
public import TauCeti.Probability.Renewal.Measure
public import Mathlib.Probability.Independence.Integration

/-!
# Wald's identity and the elementary renewal theorem

Let `T 0, T 1, …` be independent, identically distributed nonnegative increments with common law
`F` and mean `μ = 𝔼[T 0] ∈ [0, ∞]`. Write `S n = arrival T n` for the arrival times,
`N t = renewalCountNat T t` for the number of arrivals in `[0, t]` and `m t = 𝔼[N t]` for the
renewal function of `F`.

The first arrival strictly after time `t` is `S (N t + 1)`. Its expectation is given by **Wald's
identity** `𝔼[S (N t + 1)] = μ · (1 + m t)`. Indeed, on a nonexplosive path, `S (N t + 1)` is the
sum of the increments `T n` over the indices `n` with `S n ≤ t`, and each `T n` is independent of
`S n`, so that the `n`-th summand has mean `μ · F^{∗n} [0, t]`; summing over `n` gives
`μ · U [0, t]`, where `U [0, t] = 1 + m t` is the mass of the renewal measure.

When the increments are not almost surely zero, `μ > 0`, the process does not explode and
`t < S (N t + 1)`, so Wald's identity gives the lower bound `t ≤ μ · (1 + m t)`. For an upper
bound, truncating the increments at a level `c > 0` only increases the count, while the truncated
process satisfies `S (N t + 1) ≤ t + c`; hence `𝔼[min (T 0) c] · (1 + m t) ≤ t + c`. Letting
`t → ∞` and then `c → ∞` (by monotone convergence) yields the **elementary renewal theorem**

```text
m t / t → 1 / μ    as t → ∞,
```

including the case `μ = ∞`, in which the limit is zero. The statement is given in `ℝ≥0∞`, where the
reciprocal of an infinite mean is zero, and in `ℝ`, where the rate is `(μ⁻¹).toReal`. These limit
theorems take the law itself as their argument, a probability measure on `ℝ≥0` other than the point
mass at zero, and write its mean as a lower Lebesgue integral.

## Main results

* `TauCeti.Probability.lintegral_arrival_renewalCountNat_succ` — Wald's identity
  `𝔼[S (N t + 1)] = μ · (1 + m t)`.
* `MeasureTheory.Measure.tendsto_renewalFunction_div` — the elementary renewal theorem
  `m t / t → μ⁻¹` in `ℝ≥0∞`.
* `MeasureTheory.Measure.tendsto_toReal_renewalFunction_div` — the same limit in `ℝ`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

omit [MeasurableSpace Ω] in
/-- On a nonexplosive path, the first arrival strictly after time `t` is the sum of the increments
`T n` over the indices `n` whose arrival time `arrival T n` is at most `t`. -/
private lemma coe_arrival_renewalCountNat_succ_eq_tsum {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    (arrival T (renewalCountNat T t ω + 1) ω : ℝ≥0∞) =
      ∑' n, (arrival T n ⁻¹' Iic t).indicator (fun ω ↦ (T n ω : ℝ≥0∞)) ω := by
  have hmem (n : ℕ) : ω ∈ arrival T n ⁻¹' Iic t ↔ n ∈ Finset.range (renewalCountNat T t ω + 1) := by
    rw [mem_preimage, mem_Iic, Finset.mem_range, Nat.lt_succ_iff, le_renewalCountNat_iff hω]
  rw [tsum_eq_sum fun n hn ↦ indicator_of_notMem (mt (hmem n).1 hn) _, arrival_def,
    ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl fun n hn ↦
    (indicator_of_mem ((hmem n).2 hn) fun ω ↦ (T n ω : ℝ≥0∞)).symm

/-- **Wald's identity for a renewal process.** For independent, identically distributed
increments with mean `μ`, the first arrival strictly after time `t` has expectation
`μ · (1 + m t)`, where `m` is the renewal function of the law of the increments. Both sides may be
infinite. When the increments are almost surely zero, both sides vanish. -/
theorem lintegral_arrival_renewalCountNat_succ (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (t : ℝ≥0) :
    ∫⁻ ω, (arrival T (renewalCountNat T t ω + 1) ω : ℝ≥0∞) ∂P =
      (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P) * (1 + (P.map (T 0)).renewalFunction t) := by
  have := hindep.isProbabilityMeasure
  rcases (prob_le_one (μ := P) (s := {ω | T 0 ω = 0})).lt_or_eq with hzero | hzero
  swap
  · -- Degenerate case: all increments, hence all arrival times, vanish almost surely.
    have h0 : ∀ᵐ ω ∂P, T 0 ω = 0 := by
      rw [ae_iff_measure_eq (p := fun ω ↦ T 0 ω = 0)
        ((hT 0) (measurableSet_singleton 0)).nullMeasurableSet, measure_univ]
      exact hzero
    have hall : ∀ᵐ ω ∂P, ∀ n, T n ω = 0 :=
      ae_all_iff.2 fun n ↦ (hid n).symm.ae_snd (measurableSet_singleton 0) h0
    have hμ : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P = ∫⁻ _, 0 ∂P :=
      lintegral_congr_ae (h0.mono fun ω h ↦ by simp [h])
    have hlhs : ∫⁻ ω, (arrival T (renewalCountNat T t ω + 1) ω : ℝ≥0∞) ∂P = ∫⁻ _, 0 ∂P :=
      lintegral_congr_ae (hall.mono fun ω h ↦ by simp [arrival_def, h])
    simp [hμ, hlhs]
  have hS (n : ℕ) : MeasurableSet (arrival T n ⁻¹' Iic t) :=
    measurable_arrival hT n measurableSet_Iic
  -- The `n`-th summand is the product of the independent variables `1 {S n ≤ t}` and `T n`.
  have hterm (n : ℕ) : ∫⁻ ω, (arrival T n ⁻¹' Iic t).indicator (fun ω ↦ (T n ω : ℝ≥0∞)) ω ∂P =
      (P.map (T 0)).convolutionPower n (Iic t) * ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P := by
    have hsum : arrival T n = ∑ i ∈ Finset.range n, T i := by
      ext ω
      simp [arrival_def]
    have hone : (fun ω ↦ (Iic t).indicator (fun _ ↦ (1 : ℝ≥0∞)) (arrival T n ω)) =
        (arrival T n ⁻¹' Iic t).indicator (1 : Ω → ℝ≥0∞) := by
      ext ω
      by_cases h : arrival T n ω ≤ t <;> simp [h]
    have hind : IndepFun ((arrival T n ⁻¹' Iic t).indicator (1 : Ω → ℝ≥0∞))
        (fun ω ↦ (T n ω : ℝ≥0∞)) P := by
      rw [← hone, hsum]
      exact (hindep.indepFun_sum_range_succ hT n).comp
        (measurable_const.indicator measurableSet_Iic) measurable_coe_nnreal_ennreal
    have hfun : (arrival T n ⁻¹' Iic t).indicator (fun ω ↦ (T n ω : ℝ≥0∞)) =
        fun ω ↦ (arrival T n ⁻¹' Iic t).indicator (1 : Ω → ℝ≥0∞) ω * T n ω := by
      ext ω
      by_cases h : arrival T n ω ≤ t <;> simp [h]
    have hmean : ∫⁻ ω, (T n ω : ℝ≥0∞) ∂P = ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P :=
      ((hid n).comp measurable_coe_nnreal_ennreal).lintegral_eq
    rw [hfun, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        (f := (arrival T n ⁻¹' Iic t).indicator (1 : Ω → ℝ≥0∞))
        (aemeasurable_const.indicator (hS n)) (hT n).coe_nnreal_ennreal.aemeasurable hind,
      hmean, lintegral_indicator_one (hS n),
      ← (hasLaw_arrival hindep hid n).map_eq,
      Measure.map_apply (measurable_arrival hT n) measurableSet_Iic]
  rw [lintegral_congr_ae ((ae_tendsto_arrival_atTop hT hindep hid hzero).mono
      fun ω hω ↦ coe_arrival_renewalCountNat_succ_eq_tsum hω t),
    lintegral_tsum fun n ↦ ((hT n).coe_nnreal_ennreal.indicator (hS n)).aemeasurable]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, ← Measure.renewalMeasure_apply _ measurableSet_Iic,
    Measure.renewalMeasure_Iic, mul_comm]

/-- **Lower Wald bound.** Since the first arrival after `t` is strictly later than `t`, the mean
`μ` of the increments and the renewal function `m` satisfy `t ≤ μ · (1 + m t)`. -/
private lemma coe_le_lintegral_mul_one_add_renewalFunction (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P) * (1 + (P.map (T 0)).renewalFunction t) := by
  have := hindep.isProbabilityMeasure
  rw [← lintegral_arrival_renewalCountNat_succ hT hindep hid t]
  calc (t : ℝ≥0∞) = ∫⁻ _, (t : ℝ≥0∞) ∂P := by simp
    _ ≤ _ := lintegral_mono_ae <| (ae_tendsto_arrival_atTop hT hindep hid hzero).mono
      fun ω hω ↦ ENNReal.coe_le_coe.2 (lt_arrival_renewalCountNat_succ hω t).le

/-- **Upper Wald bound by truncation.** Truncating the increments at a level `c > 0` gives
`𝔼[min (T 0) c] · (1 + m t) ≤ t + c`, where `m` is the renewal function of the law of the
original increments. -/
private lemma lintegral_min_mul_one_add_renewalFunction_le (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) {c : ℝ≥0} (hc : c ≠ 0) (t : ℝ≥0) :
    (∫⁻ ω, (min (T 0 ω) c : ℝ≥0∞) ∂P) * (1 + (P.map (T 0)).renewalFunction t) ≤ t + c := by
  have := hindep.isProbabilityMeasure
  -- The truncated increments are again i.i.d. and not almost surely zero.
  set Tc : ℕ → Ω → ℝ≥0 := fun n ω ↦ min (T n ω) c with hTc
  have hmin : Measurable fun x : ℝ≥0 ↦ min x c := measurable_id.min measurable_const
  have hTc_meas (n : ℕ) : Measurable (Tc n) := hmin.comp (hT n)
  have hTc_indep : iIndepFun Tc P := hindep.comp (fun _ x ↦ min x c) fun _ ↦ hmin
  have hTc_id (n : ℕ) : IdentDistrib (Tc n) (Tc 0) P P := (hid n).comp hmin
  have hTc_zero : P {ω | Tc 0 ω = 0} < 1 := by
    convert hzero using 3 with ω
    simp [hTc, hc]
  -- Truncation only increases the count, hence the renewal function.
  have hm : (P.map (T 0)).renewalFunction t ≤ (P.map (Tc 0)).renewalFunction t := by
    rw [← lintegral_renewalCount hindep hid, ← lintegral_renewalCount hTc_indep hTc_id]
    exact lintegral_mono fun ω ↦ renewalCount_le_renewalCount (T' := Tc) (fun n ↦ min_le_left _ _) t
  calc (∫⁻ ω, (min (T 0 ω) c : ℝ≥0∞) ∂P) * (1 + (P.map (T 0)).renewalFunction t)
      ≤ (∫⁻ ω, (Tc 0 ω : ℝ≥0∞) ∂P) * (1 + (P.map (Tc 0)).renewalFunction t) := by
        simp only [hTc, ENNReal.coe_min]
        gcongr
    _ = ∫⁻ ω, (arrival Tc (renewalCountNat Tc t ω + 1) ω : ℝ≥0∞) ∂P :=
        (lintegral_arrival_renewalCountNat_succ hTc_meas hTc_indep hTc_id t).symm
    _ ≤ ∫⁻ _, ((t + c : ℝ≥0) : ℝ≥0∞) ∂P := by
        refine lintegral_mono_ae <| (ae_tendsto_arrival_atTop hTc_meas hTc_indep hTc_id
          hTc_zero).mono fun ω hω ↦ ENNReal.coe_le_coe.2 ?_
        rw [arrival_succ]
        exact add_le_add (arrival_renewalCountNat_le hω t) (min_le_right _ _)
    _ = t + c := by simp

end TauCeti.Probability

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- **The elementary renewal theorem.** For a probability measure `μ` on `ℝ≥0` other than the
point mass at zero, the renewal function grows asymptotically linearly with rate the reciprocal of
the mean of `μ`: `m t / t → (∫ x dμ)⁻¹` as `t → ∞`. The limit is computed in `ℝ≥0∞`, so it is zero
when the mean is infinite. -/
theorem tendsto_renewalFunction_div (hμ : μ {0} < 1) :
    Tendsto (fun t : ℝ≥0 ↦ μ.renewalFunction t / t) atTop
      (𝓝 (∫⁻ x, (x : ℝ≥0∞) ∂μ)⁻¹) := by
  -- Realize i.i.d. increments with law `μ` as the coordinates of the product measure.
  set P := Measure.infinitePi fun _ : ℕ ↦ μ
  have hT : ∀ n, Measurable fun w : ℕ → ℝ≥0 ↦ w n := measurable_pi_apply
  have hindep : iIndepFun (fun n (w : ℕ → ℝ≥0) ↦ w n) P :=
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ x ↦ x) fun _ ↦ measurable_id
  have hmap : ∀ n, P.map (fun w ↦ w n) = μ := fun n ↦ infinitePi_map_eval _ n
  have hid : ∀ n, IdentDistrib (fun w : ℕ → ℝ≥0 ↦ w n) (fun w ↦ w 0) P P := fun n ↦
    ⟨(hT n).aemeasurable, (hT 0).aemeasurable, by rw [hmap, hmap]⟩
  have hzero : P {w | w 0 = 0} < 1 := by
    rwa [← hmap 0, map_apply (hT 0) (measurableSet_singleton 0)] at hμ
  have hint (f : ℝ≥0 → ℝ≥0∞) (hf : Measurable f) : ∫⁻ w, f (w 0) ∂P = ∫⁻ x, f x ∂μ := by
    rw [← hmap 0, lintegral_map hf (hT 0)]
  set ν := ∫⁻ x, (x : ℝ≥0∞) ∂μ
  -- The two Wald bounds, transferred to `μ`.
  have hlow (t : ℝ≥0) : (t : ℝ≥0∞) ≤ ν * (1 + μ.renewalFunction t) := by
    simpa [hmap, hint _ measurable_coe_nnreal_ennreal] using
      TauCeti.Probability.coe_le_lintegral_mul_one_add_renewalFunction hT hindep hid hzero t
  have hup {c : ℝ≥0} (hc : c ≠ 0) (t : ℝ≥0) :
      (∫⁻ x, (min x c : ℝ≥0∞) ∂μ) * (1 + μ.renewalFunction t) ≤ t + c := by
    have hmin : Measurable fun x : ℝ≥0 ↦ (min x c : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.min measurable_const
    simpa [hmap, hint _ hmin] using
      TauCeti.Probability.lintegral_min_mul_one_add_renewalFunction_le hT hindep hid hzero hc t
  -- `1 / t → 0` as `t → ∞`.
  have hinv : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.inv_top ▸ tendsto_inv_iff.2 (ENNReal.tendsto_coe_nhds_top.2 tendsto_id)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · -- Lower bound: `ν⁻¹ - 1 / t ≤ m t / t`.
    have hlim : Tendsto (fun t : ℝ≥0 ↦ ν⁻¹ - (t : ℝ≥0∞)⁻¹) atTop (𝓝 ν⁻¹) := by
      simpa using ENNReal.Tendsto.sub tendsto_const_nhds hinv (Or.inr ENNReal.zero_ne_top)
    filter_upwards [hlim.eventually (lt_mem_nhds ha), eventually_gt_atTop 0] with t hat ht
    refine hat.trans_le (tsub_le_iff_left.2 ?_)
    rw [← one_div (t : ℝ≥0∞), ← ENNReal.add_div,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht.ne')) (Or.inl ENNReal.coe_ne_top),
      mul_comm, ← div_eq_mul_inv]
    exact ENNReal.div_le_of_le_mul (mul_comm ν _ ▸ hlow t)
  · -- Upper bound: `m t / t ≤ ν_c⁻¹ · (1 + c / t)` for the mean `ν_c` of `min x c`.
    have hmono : Tendsto (fun k : ℕ ↦ ∫⁻ x, (min x (k + 1 : ℝ≥0) : ℝ≥0∞) ∂μ) atTop (𝓝 ν) := by
      refine lintegral_tendsto_of_tendsto_of_monotone
        (fun k ↦ (measurable_coe_nnreal_ennreal.min measurable_const).aemeasurable)
        (Eventually.of_forall fun x k l hkl ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
      · exact min_le_min_left _ (by exact_mod_cast Nat.succ_le_succ hkl)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈x⌉₊] with k hk
        rw [min_eq_left (ENNReal.coe_le_coe.2 ((Nat.le_ceil x).trans ?_))]
        exact_mod_cast hk.trans (Nat.le_succ k)
    obtain ⟨k, hk⟩ := ((tendsto_inv_iff.2 hmono).eventually (gt_mem_nhds ha)).exists
    set c : ℝ≥0 := k + 1
    set νc := ∫⁻ x, (min x c : ℝ≥0∞) ∂μ
    have hνc : νc ≠ 0 := ENNReal.inv_ne_top.1 (hk.trans_le le_top).ne
    have hlim : Tendsto (fun t : ℝ≥0 ↦ νc⁻¹ * (1 + c * (t : ℝ≥0∞)⁻¹)) atTop (𝓝 νc⁻¹) := by
      simpa using ENNReal.Tendsto.const_mul ((tendsto_const_nhds (x := (1 : ℝ≥0∞))).add
        (ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) hinv (Or.inr ENNReal.coe_ne_top)))
        (Or.inr (ENNReal.inv_ne_top.2 hνc))
    filter_upwards [hlim.eventually (gt_mem_nhds hk), eventually_gt_atTop 0] with t hat ht
    refine lt_of_le_of_lt ?_ hat
    have ht0 : (t : ℝ≥0∞) ≠ 0 := by simpa using ht.ne'
    have hm : μ.renewalFunction t ≤ (t + c) * νc⁻¹ := by
      rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hνc) (Or.inr (by simp))]
      exact (mul_le_mul_left (le_add_self) _).trans (mul_comm νc _ ▸ hup (by simp [c]) t)
    calc μ.renewalFunction t / t ≤ (t + c) * νc⁻¹ / t := ENNReal.div_le_div_right hm _
      _ = νc⁻¹ * (1 + c * (t : ℝ≥0∞)⁻¹) := by
        rw [mul_comm, mul_div_assoc, ENNReal.add_div, ENNReal.div_self ht0 ENNReal.coe_ne_top,
          div_eq_mul_inv]

/-- **The elementary renewal theorem, real form.** For a probability measure `μ` on `ℝ≥0` other
than the point mass at zero, `m t / t → r` as `t → ∞`, where the rate `r` is the reciprocal of the
mean of `μ`, taken in `ℝ≥0∞` before conversion to a real number; thus `r = 0` when the mean is
infinite. -/
theorem tendsto_toReal_renewalFunction_div (hμ : μ {0} < 1) :
    Tendsto (fun t : ℝ≥0 ↦ (μ.renewalFunction t).toReal / t) atTop
      (𝓝 (∫⁻ x, (x : ℝ≥0∞) ∂μ)⁻¹.toReal) := by
  -- The mean is positive because `μ` is not the point mass at zero.
  have hν : (∫⁻ x, (x : ℝ≥0∞) ∂μ)⁻¹ ≠ ∞ := by
    refine ENNReal.inv_ne_top.2 fun h ↦ hμ.ne ?_
    rw [lintegral_eq_zero_iff measurable_coe_nnreal_ennreal, EventuallyEq, ae_iff] at h
    rw [← prob_compl_eq_zero_iff (measurableSet_singleton 0)]
    simpa [compl_def] using h
  refine ((ENNReal.tendsto_toReal hν).comp (tendsto_renewalFunction_div μ hμ)).congr fun t ↦ ?_
  simp [ENNReal.toReal_div]

end MeasureTheory.Measure
