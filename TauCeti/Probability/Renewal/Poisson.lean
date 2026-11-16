/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.ArrivalMeasure
public import TauCeti.Probability.PointProcess.Poisson.OccurrenceTime

import TauCeti.Probability.PointProcess.Poisson.IntegerValued

/-!
# Renewal realization of a homogeneous Poisson random measure

Almost every path of a positive-rate homogeneous temporal Poisson random measure `N` on `ℝ≥0`
equals `renewalArrivalMeasure` of its `ℝ≥0` interarrival-gap representatives, and its `(0, t]`
counts agree simultaneously at all times `t` with both `renewalCount` and `renewalCountNat`.

## Main results

* `TauCeti.Probability.IsPoissonRandomMeasure.ae_eq_renewalArrivalMeasure_toNNReal_occurrenceGap` —
  a positive-rate homogeneous Poisson random measure almost surely equals the renewal arrival
  measure of its `ℝ≥0` interarrival-gap representatives.
* `IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCount_toNNReal_occurrenceGap` (in
  `TauCeti.Probability`) — almost surely, for every `t : ℝ≥0`, `N ω (Ioc 0 t)` equals the
  extended renewal count of the `ℝ≥0` interarrival-gap representatives.
* `IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap` (in
  `TauCeti.Probability`) — almost surely, for every `t : ℝ≥0`, `N ω (Ioc 0 t)` equals the
  natural-valued renewal count of the `ℝ≥0` interarrival-gap representatives.
* `IsPoissonRandomMeasure.ae_forall_natFloor_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap` (in
  `TauCeti.Probability`) — almost surely, for every `t : ℝ≥0`, the natural floor of the real count
  on `(0, t]` equals the natural-valued renewal count.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

/-- Almost every path of a positive-rate homogeneous Poisson random measure on `ℝ≥0` equals the
renewal arrival measure of its `ℝ≥0` interarrival-gap representatives. -/
theorem IsPoissonRandomMeasure.ae_eq_renewalArrivalMeasure_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, N ω = renewalArrivalMeasure (fun n ω' => ((N ω').occurrenceGap n).toNNReal) ω := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hlf hint hposfin
  rw [renewalArrivalMeasure_comp (fun n (ν : Measure ℝ≥0) => (ν.occurrenceGap n).toNNReal) N ω]
  exact eq_renewalArrivalMeasure_toNNReal_occurrenceGap hint fun n => (hposfin n).2.ne

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the count on `(0, t]` equals the extended renewal count of its
`ℝ≥0` interarrival-gap representatives. -/
theorem IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCount_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t,
      N ω (Ioc 0 t) = renewalCount (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω := by
  filter_upwards [h.ae_eq_renewalArrivalMeasure_toNNReal_occurrenceGap hr,
    h.ae_forall_occurrenceTime_pos_lt_top hr] with ω heq hposfin t
  have hpos0 : 0 < ((N ω).occurrenceGap 0).toNNReal := by
    rw [Measure.occurrenceGap_zero]
    exact ENNReal.toNNReal_pos (hposfin 0).1.ne' (hposfin 0).2.ne
  rw [heq, renewalArrivalMeasure_Ioc _ hpos0]

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the count on `(0, t]` equals the natural-valued renewal count
of its `ℝ≥0` interarrival-gap representatives. -/
theorem IsPoissonRandomMeasure.ae_forall_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t, N ω (Ioc 0 t) =
      (renewalCountNat (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω : ℝ≥0∞) := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure,
    h.ae_eq_renewalArrivalMeasure_toNNReal_occurrenceGap hr,
    h.ae_forall_Ioc_eq_renewalCount_toNNReal_occurrenceGap hr] with ω hlf heq hcount t
  have hlf' : IsLocallyFiniteMeasure
      (renewalArrivalMeasure (fun n ω' => ((N ω').occurrenceGap n).toNNReal) ω) :=
    heq ▸ hlf
  have htend := (isLocallyFiniteMeasure_renewalArrivalMeasure_iff _ ω).mp hlf'
  rw [hcount t, ← natCast_renewalCountNat htend]

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the natural floor of the real count on `(0, t]` equals the
natural-valued renewal count of its `ℝ≥0` interarrival-gap representatives. -/
theorem IsPoissonRandomMeasure.ae_forall_natFloor_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t, ⌊(N ω (Ioc 0 t)).toReal⌋₊ =
      renewalCountNat (fun n ω' => ((N ω').occurrenceGap n).toNNReal) t ω := by
  filter_upwards [h.ae_forall_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap hr] with ω hIoc t
  simp [hIoc t]

end TauCeti.Probability
