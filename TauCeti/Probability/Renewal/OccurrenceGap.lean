/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.ArrivalMeasure
public import TauCeti.Probability.PointProcess.Poisson.Interarrival

import TauCeti.Probability.PointProcess.Poisson.IntegerValued

/-!
# Renewal arrival measures and point-process interarrival gaps

Extracting interarrival gaps from `renewalArrivalMeasure T ω` recovers the increment sequence
`T`, including zero increments and explosive paths. Conversely, any locally finite integer-valued
measure on `ℝ≥0` whose occurrence times are all finite equals the renewal arrival measure of its
`ℝ≥0` interarrival-gap representatives, and its cumulative mass on `[0, t]` agrees with both the
extended and the natural-valued renewal counts. Atoms at zero and multiple simultaneous
occurrences are retained.

Specializing to a homogeneous temporal Poisson random measure `N` of positive rate `r`, whose
interarrival gaps are mutually independent exponential random variables of rate `r`, realizes
almost every path of `N` as `renewalArrivalMeasure` of those gaps and identifies the `(0, t]`
counts simultaneously at all times `t` with `renewalCount` and `renewalCountNat`.

## Main results

* `TauCeti.Probability.occurrenceGap_renewalArrivalMeasure` — extracting `occurrenceGap` from
  `renewalArrivalMeasure T ω` recovers `(T n ω : ℝ≥0∞)`.
* `TauCeti.Probability.eq_renewalArrivalMeasure_toNNReal_occurrenceGap` — any locally finite
  counting measure with infinitely many finite occurrences is reconstructed as the renewal
  arrival measure of its `ℝ≥0` interarrival gaps.
* `TauCeti.Probability.IsPoissonRandomMeasure.ae_eq_renewalArrivalMeasure_occurrenceGap` — a
  positive-rate homogeneous Poisson random measure almost surely equals the renewal arrival
  measure of its interarrival gaps.
* `TauCeti.Probability.IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCountNat_occurrenceGap` —
  almost surely, for every `t : ℝ≥0`, `N ω (Ioc 0 t)` equals the natural-valued renewal count of
  the interarrival gaps.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

section Deterministic

variable {Ω : Type*}

/-- Extracting interarrival gaps from `renewalArrivalMeasure T ω` recovers every increment,
including zero increments and explosive paths. -/
@[simp]
theorem occurrenceGap_renewalArrivalMeasure (T : ℕ → Ω → ℝ≥0) (ω : Ω) (n : ℕ) :
    (renewalArrivalMeasure T ω).occurrenceGap n = (T n ω : ℝ≥0∞) := by
  simp [renewalArrivalMeasure_eq_occurrenceTimeMeasure, arrival_def]

/-- Extracting `ℝ≥0` interarrival-gap representatives from `renewalArrivalMeasure T ω` recovers
the increment sequence `T`. -/
theorem toNNReal_occurrenceGap_renewalArrivalMeasure (T : ℕ → Ω → ℝ≥0) (ω : Ω) (n : ℕ) :
    ((renewalArrivalMeasure T ω).occurrenceGap n).toNNReal = T n ω := by
  simp

/-- Extracting real-valued interarrival-gap representatives from `renewalArrivalMeasure T ω`
recovers the real-coerced increment sequence. -/
theorem toReal_occurrenceGap_renewalArrivalMeasure (T : ℕ → Ω → ℝ≥0) (ω : Ω) (n : ℕ) :
    ((renewalArrivalMeasure T ω).occurrenceGap n).toReal = (T n ω : ℝ) := by
  simp

/-- When the `n`-th occurrence time of `N ω` is finite, the `(n + 1)`-st renewal arrival time of
its `ℝ≥0` interarrival-gap representatives equals that occurrence time. -/
theorem arrival_toNNReal_occurrenceGap {N : Ω → Measure ℝ≥0} {ω : Ω} {n : ℕ}
    (hn : (N ω).occurrenceTime n ≠ ∞) :
    arrival (fun i ω' => ((N ω').occurrenceGap i).toNNReal) (n + 1) ω =
      ((N ω).occurrenceTime n).toNNReal := by
  rw [arrival_def, (N ω).sum_toNNReal_occurrenceGap_range hn]

/-- Any locally finite integer-valued measure on `ℝ≥0` whose occurrence times are all finite
equals the renewal arrival measure of its `ℝ≥0` interarrival-gap representatives. Atoms at zero
and coincident occurrences are allowed. -/
theorem eq_renewalArrivalMeasure_toNNReal_occurrenceGap {N : Ω → Measure ℝ≥0} {ω : Ω}
    [IsLocallyFiniteMeasure (N ω)] (hN : (N ω).IsIntegerValued)
    (hfin : ∀ n, (N ω).occurrenceTime n ≠ ∞) :
    N ω = renewalArrivalMeasure (fun n ω' => ((N ω').occurrenceGap n).toNNReal) ω := by
  rw [renewalArrivalMeasure_eq_occurrenceTimeMeasure]
  have hseq : (fun n =>
      (arrival (fun i ω' => ((N ω').occurrenceGap i).toNNReal) (n + 1) ω : ℝ≥0∞)) =
      (N ω).occurrenceTime := by
    funext n
    rw [arrival_toNNReal_occurrenceGap (hfin n), ENNReal.coe_toNNReal (hfin n)]
  rw [hseq]
  exact hN.eq_occurrenceTimeMeasure

/-- For a locally finite counting measure on `ℝ≥0` whose occurrence times are all finite, the
mass of `[0, t]` equals the extended renewal count of its `ℝ≥0` interarrival-gap
representatives. -/
theorem apply_Iic_eq_renewalCount_toNNReal_occurrenceGap {N : Ω → Measure ℝ≥0} {ω : Ω}
    [IsLocallyFiniteMeasure (N ω)] (hN : (N ω).IsIntegerValued)
    (hfin : ∀ n, (N ω).occurrenceTime n ≠ ∞) (t : ℝ≥0) :
    N ω (Iic t) = renewalCount (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω := by
  rw [eq_renewalArrivalMeasure_toNNReal_occurrenceGap hN hfin, renewalArrivalMeasure_Iic]

/-- For a locally finite counting measure on `ℝ≥0` whose occurrence times are all finite, the
mass of `[0, t]` equals the natural-valued renewal count of its `ℝ≥0` interarrival-gap
representatives. -/
theorem apply_Iic_eq_renewalCountNat_toNNReal_occurrenceGap {N : Ω → Measure ℝ≥0} {ω : Ω}
    [IsLocallyFiniteMeasure (N ω)] (hN : (N ω).IsIntegerValued)
    (hfin : ∀ n, (N ω).occurrenceTime n ≠ ∞) (t : ℝ≥0) :
    N ω (Iic t) =
      (renewalCountNat (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω : ℝ≥0∞) := by
  have heq := eq_renewalArrivalMeasure_toNNReal_occurrenceGap hN hfin
  have hlf : IsLocallyFiniteMeasure
      (renewalArrivalMeasure (fun n ω' => ((N ω').occurrenceGap n).toNNReal) ω) :=
    heq ▸ inferInstance
  have htend : Tendsto
      (fun n => arrival (fun i ω' => ((N ω').occurrenceGap i).toNNReal) n ω) atTop atTop :=
    (isLocallyFiniteMeasure_renewalArrivalMeasure_iff _ ω).mp hlf
  rw [apply_Iic_eq_renewalCount_toNNReal_occurrenceGap hN hfin t, ← natCast_renewalCountNat htend]

end Deterministic

section Poisson

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

/-- Almost every path of a positive-rate homogeneous Poisson random measure on `ℝ≥0` equals the
renewal arrival measure of its `ℝ≥0` interarrival-gap representatives. -/
theorem IsPoissonRandomMeasure.ae_eq_renewalArrivalMeasure_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, N ω = renewalArrivalMeasure (fun n ω' => ((N ω').occurrenceGap n).toNNReal) ω := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hlf hint hposfin
  exact eq_renewalArrivalMeasure_toNNReal_occurrenceGap hint fun n => (hposfin n).2.ne

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the count on `(0, t]` equals the extended renewal count of its
interarrival gaps. -/
theorem IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCount_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t,
      N ω (Ioc 0 t) = renewalCount (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω := by
  filter_upwards [h.ae_eq_renewalArrivalMeasure_occurrenceGap hr,
    h.ae_forall_occurrenceTime_pos_lt_top hr] with ω heq hposfin t
  have hpos0 : 0 < ((N ω).occurrenceGap 0).toNNReal := by
    rw [Measure.occurrenceGap_zero]
    exact ENNReal.toNNReal_pos (hposfin 0).1.ne' (hposfin 0).2.ne
  rw [heq, renewalArrivalMeasure_Ioc _ hpos0]

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the count on `(0, t]` equals the natural-valued renewal count
of its interarrival gaps. -/
theorem IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCountNat_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t, N ω (Ioc 0 t) =
      (renewalCountNat (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω : ℝ≥0∞) := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_eq_renewalArrivalMeasure_occurrenceGap hr,
    h.ae_forall_Ioc_eq_renewalCount_occurrenceGap hr] with ω hlf heq hIoc t
  have hlf' : IsLocallyFiniteMeasure
      (renewalArrivalMeasure (fun n ω' => ((N ω').occurrenceGap n).toNNReal) ω) :=
    heq ▸ hlf
  have htend : Tendsto
      (fun n => arrival (fun i ω' => ((N ω').occurrenceGap i).toNNReal) n ω) atTop atTop :=
    (isLocallyFiniteMeasure_renewalArrivalMeasure_iff _ ω).mp hlf'
  rw [hIoc t, ← natCast_renewalCountNat htend]

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the natural floor of the real count on `(0, t]` equals the
natural-valued renewal count of its interarrival gaps. -/
theorem IsPoissonRandomMeasure.ae_forall_natFloor_Ioc_eq_renewalCountNat_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t, ⌊(N ω (Ioc 0 t)).toReal⌋₊ =
      renewalCountNat (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω := by
  filter_upwards [h.ae_forall_Ioc_eq_renewalCountNat_occurrenceGap hr] with ω hIoc t
  simp [hIoc t]

end Poisson

end TauCeti.Probability
