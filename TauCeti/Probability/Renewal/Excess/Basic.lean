/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Eval
public import TauCeti.Probability.Renewal.Count
public import TauCeti.Probability.Renewal.Equation

/-!
# The excess of a renewal process

The excess (or residual waiting time) of a renewal process at time `t` is the time from `t` until
the next arrival,

```text
E t = arrival T (N t + 1) - t,
```

where `N t = renewalCountNat T t` is the number of positive-index arrivals in `[0, t]`. On a
nonexplosive path the arrival `arrival T (N t + 1)` is the first one strictly after `t`, so the
excess is strictly positive; on explosive paths the formula uses the exceptional value `N t = 0`.

For independent increments with common law `F` that are not almost surely zero, this file computes
the law of the excess at each fixed time in terms of the renewal measure `U = ∑ n, F^{∗n}`. Writing
`F> u = F((u, ∞))` for the tail of `F` and `F≤ u = F([0, u])` for its distribution function,

```text
P(x < E t) = ∫_{[0, t]} F> (t - s + x) U(ds),
P(E t ≤ x) = ∫_{[0, t]} (F≤ (t - s + x) - F≤ (t - s)) U(ds).
```

The first identity splits the event `x < E t` according to the value `n` of `N t`. Almost surely
it is the disjoint union over `n` of the events `{arrival T n ≤ t, t + x < arrival T n + T n}`, and
`arrival T n`, which has law `F^{∗n}`, is independent of `T n`. The second identity follows from the
tail identity `∫_{[0, t]} F> (t - s) U(ds) = 1`
(`TauCeti.Probability.renewalConv_measureReal_Ioi_renewalMeasure`). In the notation of
`TauCeti.Probability.renewalConv`, both probabilities are of the form `h ∗ U`, so they solve the
renewal equation `g = h + g ∗ F` with forcing terms `F> (t + x)` and `F≤ (t + x) - F≤ t`
respectively. These representations are the input of the limit theorem for the excess.

## Main definitions

* `TauCeti.Probability.renewalExcess`: the excess `arrival T (N t + 1) - t` at time `t`.

## Main results

* `TauCeti.Probability.lt_renewalExcess_iff`: on a nonexplosive path, `x < E t` exactly when some
  arrival `arrival T n` is at most `t` while the next one is after `t + x`.
* `TauCeti.Probability.measurable_renewalExcess`: measurability of the excess.
* `TauCeti.Probability.measure_lt_renewalExcess`,
  `TauCeti.Probability.measureReal_lt_renewalExcess`: the excess-tail representation
  `P(x < E t) = (F> (· + x) ∗ U) t`.
* `TauCeti.Probability.measureReal_renewalExcess_le`: the distribution function of the excess is
  `P(E t ≤ x) = ((F≤ (· + x) - F≤) ∗ U) t`.
* `TauCeti.Probability.measureReal_lt_renewalExcess_eq_add`,
  `TauCeti.Probability.measureReal_renewalExcess_le_eq_add`: the renewal equations satisfied by
  `t ↦ P(x < E t)` and `t ↦ P(E t ≤ x)`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} (T : ℕ → Ω → ℝ≥0)

/-- The excess (residual waiting time) of a renewal process at time `t`: the time from `t` until
the arrival with index one more than the natural-valued count `renewalCountNat T t`. On a
nonexplosive path this is the first arrival strictly after `t`. -/
def renewalExcess (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  arrival T (renewalCountNat T t ω + 1) ω - t

lemma renewalExcess_def (t : ℝ≥0) (ω : Ω) :
    renewalExcess T t ω = arrival T (renewalCountNat T t ω + 1) ω - t := (rfl)

variable {T}

/-- On a nonexplosive path, the excess at `t` reaches from `t` exactly to the next arrival. -/
lemma add_renewalExcess {ω : Ω} (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    t + renewalExcess T t ω = arrival T (renewalCountNat T t ω + 1) ω :=
  add_tsub_cancel_of_le (lt_arrival_renewalCountNat_succ hω t).le

/-- On a nonexplosive path, the excess is strictly positive. -/
lemma renewalExcess_pos {ω : Ω} (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    0 < renewalExcess T t ω :=
  tsub_pos_of_lt (lt_arrival_renewalCountNat_succ hω t)

/-- On a nonexplosive path, specifying the count and a lower bound for the excess is
equivalent to locating two consecutive arrivals around the corresponding time window. -/
lemma renewalCountNat_eq_and_lt_renewalExcess_iff {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) {n : ℕ} {t x : ℝ≥0} :
    (renewalCountNat T t ω = n ∧ x < renewalExcess T t ω) ↔
      arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω := by
  constructor
  · rintro ⟨hN, hx⟩
    refine ⟨by simpa [hN] using arrival_renewalCountNat_le hω t, ?_⟩
    rw [← hN, ← add_renewalExcess hω t]
    gcongr
  · rintro ⟨hs, hx⟩
    have hN := (renewalCountNat_eq_iff hω).2 ⟨hs, le_self_add.trans_lt hx⟩
    refine ⟨hN, ?_⟩
    rw [renewalExcess_def, hN]
    exact lt_tsub_iff_left.2 hx

/-- On a nonexplosive path, the excess at `t` exceeds `x` exactly when some arrival
`arrival T n` is at most `t` while the next one is after `t + x`. That index `n` is then the
count at `t`. -/
lemma lt_renewalExcess_iff {ω : Ω} (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    {t x : ℝ≥0} :
    x < renewalExcess T t ω ↔ ∃ n, arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω := by
  constructor
  · intro hx
    exact ⟨renewalCountNat T t ω, (renewalCountNat_eq_and_lt_renewalExcess_iff hω).1 ⟨rfl, hx⟩⟩
  · rintro ⟨n, hn⟩
    exact ((renewalCountNat_eq_and_lt_renewalExcess_iff hω).2 hn).2

variable (T) in
/-- The events `{arrival T n ≤ t, t + x < arrival T (n + 1)}` are pairwise disjoint, on every
path: if the event for `m` holds, then every arrival with index greater than `m` is after `t`. -/
private lemma pairwise_disjoint_setOf_arrival (t x : ℝ≥0) :
    Pairwise (Disjoint on fun n ↦ {ω | arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω}) := by
  refine (pairwise_disjoint_on _).2 fun m n hmn ↦ disjoint_left.2 fun ω hm hn ↦ ?_
  have hle := monotone_arrival T ω (Nat.succ_le_of_lt hmn)
  exact (hm.2.trans_le (hle.trans hn.1)).not_ge le_self_add

variable [MeasurableSpace Ω]

/-- The excess at a fixed time is measurable. -/
@[fun_prop]
lemma measurable_renewalExcess (hT : ∀ n, Measurable (T n)) (t : ℝ≥0) :
    Measurable (renewalExcess T t) := by
  have harr : Measurable fun ω n ↦ arrival T n ω :=
    measurable_pi_iff.2 fun n ↦ measurable_arrival hT n
  exact (harr.eval_index ((measurable_renewalCountNat hT t).add_const 1)).sub_const t

variable {P : Measure Ω}

/-- For i.i.d. increments with law `F`, the `n`-th arrival is at most `t` and the next one is
after `t + x` with probability `∫_{[0, t]} F((t - s + x, ∞)) F^{∗n}(ds)`, because `arrival T n`
is independent of `T n`. -/
private lemma measure_arrival_le_lt_arrival_succ (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (n : ℕ) (t x : ℝ≥0) :
    P {ω | arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω} =
      ∫⁻ s in Iic t, P.map (T 0) (Ioi (t - s + x)) ∂(P.map (T 0)).convolutionPower n := by
  have := hindep.isProbabilityMeasure
  have hS : arrival T n = ∑ j ∈ Finset.range n, T j := by
    ext ω
    simp [arrival_def]
  have hind : IndepFun (arrival T n) (T n) P := hS ▸ hindep.indepFun_sum_range_succ hT n
  have hpair : Measurable fun ω ↦ (arrival T n ω, T n ω) := (measurable_arrival hT n).prodMk (hT n)
  have hmap : P.map (fun ω ↦ (arrival T n ω, T n ω)) =
      ((P.map (T 0)).convolutionPower n).prod (P.map (T 0)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_arrival hT n).aemeasurable
      (hT n).aemeasurable).1 hind, (hasLaw_arrival hindep hid n).map_eq, (hid n).map_eq]
  set B : Set (ℝ≥0 × ℝ≥0) := {p | p.1 ≤ t ∧ t + x < p.1 + p.2}
  have hB : MeasurableSet B := (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
  have hset : {ω | arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω} =
      (fun ω ↦ (arrival T n ω, T n ω)) ⁻¹' B := by
    ext ω
    simp [B, arrival_succ]
  rw [hset, ← Measure.map_apply hpair hB, hmap, Measure.prod_apply hB,
    ← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun s ↦ ?_
  by_cases hs : s ≤ t
  · rw [indicator_of_mem (mem_Iic.2 hs)]
    congr 1
    ext u
    simp [B, hs, tsub_add_eq_add_tsub hs, tsub_lt_iff_left (hs.trans le_self_add)]
  · rw [indicator_of_notMem (by simpa using hs)]
    simp [B, hs]

/-- **The excess-tail representation**, in `ℝ≥0∞`. For i.i.d. increments with law `F` that are not
almost surely zero, the excess at time `t` exceeds `x` with probability
`∫_{[0, t]} F((t - s + x, ∞)) U(ds)`, where `U` is the renewal measure of `F`. -/
theorem measure_lt_renewalExcess (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P {ω | x < renewalExcess T t ω} =
      ∫⁻ s in Iic t, P.map (T 0) (Ioi (t - s + x)) ∂(P.map (T 0)).renewalMeasure := by
  have hA (n : ℕ) : MeasurableSet {ω | arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω} :=
    (measurableSet_le (measurable_arrival hT n) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_arrival hT _))
  -- On nonexplosive paths, `{x < E t}` is the disjoint union over the value `n` of the count.
  have hae : {ω | x < renewalExcess T t ω} =ᵐ[P]
      ⋃ n, {ω | arrival T n ω ≤ t ∧ t + x < arrival T (n + 1) ω} := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_tendsto_arrival_atTop hindep hid hzero] with ω hω
    simpa using lt_renewalExcess_iff hω
  rw [measure_congr hae, measure_iUnion (pairwise_disjoint_setOf_arrival T t x) hA,
    Measure.renewalMeasure_def, Measure.restrict_sum _ measurableSet_Iic, lintegral_sum_measure]
  exact tsum_congr fun n ↦ measure_arrival_le_lt_arrival_succ hT hindep hid n t x

/-- **The excess-tail representation.** For i.i.d. increments with law `F` that are not almost
surely zero, `P(x < E t) = (h ∗ U) t` for the forcing term `h u = F((u + x, ∞))`, where `U` is the
renewal measure of `F`. -/
theorem measureReal_lt_renewalExcess (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P.real {ω | x < renewalExcess T t ω} =
      renewalConv (fun u ↦ (P.map (T 0)).real (Ioi (u + x))) (P.map (T 0)).renewalMeasure t := by
  have := hindep.isProbabilityMeasure
  have hmeas : Measurable fun s ↦ (P.map (T 0)).real (Ioi (t - s + x)) :=
    Monotone.measurable fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr))
  rw [measureReal_def, measure_lt_renewalExcess hT hindep hid hzero, renewalConv_def,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ measureReal_nonneg)
      hmeas.aestronglyMeasurable]
  congr 1
  exact setLIntegral_congr_fun measurableSet_Iic fun s _ ↦ (ofReal_measureReal).symm

/-- **The distribution function of the excess.** For i.i.d. increments with law `F` that are not
almost surely zero, `P(E t ≤ x) = (h ∗ U) t` for the forcing term `h u = F([0, u + x]) - F([0, u])`,
where `U` is the renewal measure of `F`. -/
theorem measureReal_renewalExcess_le (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P.real {ω | renewalExcess T t ω ≤ x} =
      renewalConv (fun u ↦ (P.map (T 0)).real (Iic (u + x)) - (P.map (T 0)).real (Iic u))
        (P.map (T 0)).renewalMeasure t := by
  have := hindep.isProbabilityMeasure
  set F := P.map (T 0)
  have hF : F {0} < 1 := by rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)]
  have hU := (Measure.renewalMeasure_Iic_lt_top F hF t).ne
  have hint (y : ℝ≥0) := integrableOn_Iic_sub (h := fun u ↦ F.real (Ioi (u + y))) (C := 1)
    (Antitone.measurable fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr)))
    (fun u _ ↦ by simp [abs_of_nonneg measureReal_nonneg]) hU
  -- `P(E t ≤ x) = 1 - P(x < E t)`, and `1 = (F> ∗ U) t` by the tail identity.
  have hcompl : {ω | renewalExcess T t ω ≤ x} = {ω | x < renewalExcess T t ω}ᶜ := by
    ext
    simp
  rw [hcompl, probReal_compl_eq_one_sub (measurableSet_lt measurable_const
      (measurable_renewalExcess hT t)), measureReal_lt_renewalExcess hT hindep hid hzero,
    ← renewalConv_measureReal_Ioi_renewalMeasure hF t]
  have hfun : (fun u ↦ F.real (Iic (u + x)) - F.real (Iic u)) =
      (fun u ↦ F.real (Ioi (u + 0))) - fun u ↦ F.real (Ioi (u + x)) := by
    funext u
    simp only [Pi.sub_apply, add_zero, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    ring
  rw [hfun, renewalConv_sub (hint 0) (hint x)]
  simp only [add_zero, F]

/-- **The renewal equation for the excess tail.** For i.i.d. increments with law `F` that are not
almost surely zero, `g t = P(x < E t)` solves the renewal equation `g = h + g ∗ F` with forcing
term `h t = F((t + x, ∞))`. -/
theorem measureReal_lt_renewalExcess_eq_add (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P.real {ω | x < renewalExcess T t ω} = (P.map (T 0)).real (Ioi (t + x)) +
      renewalConv (fun s ↦ P.real {ω | x < renewalExcess T s ω}) (P.map (T 0)) t := by
  have := hindep.isProbabilityMeasure
  have := Measure.isLocallyFiniteMeasure_renewalMeasure _
    (by rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)])
  simp_rw [measureReal_lt_renewalExcess hT hindep hid hzero]
  exact renewalConv_renewalMeasure_eq_add (C := 1)
    (Antitone.measurable fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr)))
    fun u _ ↦ by simp [abs_of_nonneg measureReal_nonneg]

/-- **The renewal equation for the distribution function of the excess.** For i.i.d. increments
with law `F` that are not almost surely zero, `g t = P(E t ≤ x)` solves the renewal equation
`g = h + g ∗ F` with forcing term `h t = F([0, t + x]) - F([0, t])`. -/
theorem measureReal_renewalExcess_le_eq_add (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P.real {ω | renewalExcess T t ω ≤ x} =
      ((P.map (T 0)).real (Iic (t + x)) - (P.map (T 0)).real (Iic t)) +
        renewalConv (fun s ↦ P.real {ω | renewalExcess T s ω ≤ x}) (P.map (T 0)) t := by
  have := hindep.isProbabilityMeasure
  have := Measure.isLocallyFiniteMeasure_renewalMeasure _
    (by rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)])
  have hcdf : Measurable fun u : ℝ≥0 ↦ (P.map (T 0)).real (Iic u) :=
    Monotone.measurable fun _ _ h ↦ measureReal_mono (Iic_subset_Iic.2 h)
  simp_rw [measureReal_renewalExcess_le hT hindep hid hzero]
  refine renewalConv_renewalMeasure_eq_add (C := 1) ((hcdf.comp (measurable_add_const x)).sub hcdf)
    fun u _ ↦ abs_sub_le_iff.2 ⟨?_, ?_⟩ <;>
  linarith [measureReal_nonneg (μ := P.map (T 0)) (s := Iic u),
    measureReal_nonneg (μ := P.map (T 0)) (s := Iic (u + x)),
    measureReal_le_one (μ := P.map (T 0)) (s := Iic u),
    measureReal_le_one (μ := P.map (T 0)) (s := Iic (u + x))]

end TauCeti.Probability
