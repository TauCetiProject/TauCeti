/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Basic
public import TauCeti.Probability.Renewal.Measure
public import TauCeti.Probability.PointProcess.OccurrenceTime.Gap
public import Mathlib.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite

/-!
# The random measure of renewal arrivals

`renewalArrivalMeasure T ω` places one Dirac mass at each positive-index arrival of the
renewal process with increments `T`. It omits the artificial arrival at index zero, but
retains genuine arrivals at zero and repeated arrivals. Its evaluation on `[0,t]` is the
extended renewal count, and local finiteness is equivalent to nonexplosion. Extracting
interarrival gaps from `renewalArrivalMeasure T ω` recovers `T`, and conversely every
locally finite integer-valued measure on `ℝ≥0` whose occurrence times are all finite equals
the renewal arrival measure of its `ℝ≥0` interarrival-gap representatives on the canonical
space `Measure ℝ≥0`.

The construction is measurable into Mathlib's space of measures with its evaluation
σ-algebra. Its entire law transfers to the canonical product realization of i.i.d.
increments. Its intensity, expressed using `Measure.bind`, is `F ∗ F.renewalMeasure`, not
the renewal measure itself: the latter also includes the artificial initial arrival.

Pointwise positivity lemmas rule out mass at zero and bound singleton masses by one.
For exponential increments, counts on `(0,t]` almost surely agree with the existing
natural-valued renewal counts; the corresponding natural-valued counts have Poisson laws.
No independent increment or Poisson random-measure characterization is asserted here.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter XI, §1, for renewal arrivals and the renewal measure.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2017, Chapters 2 and 7, for occurrence measures and exponential arrival times.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} (T : ℕ → Ω → ℝ≥0)

/-- The measure of positive-index renewal arrivals, with multiplicity. The artificial arrival
at index zero is omitted, but genuine arrivals at zero are retained. -/
def renewalArrivalMeasure (ω : Ω) : Measure ℝ≥0 :=
  Measure.sum fun n => Measure.dirac (arrival T (n + 1) ω)

/-- The arrival measure is the sum of the Dirac masses at the positive-index arrivals. -/
theorem renewalArrivalMeasure_def (ω : Ω) :
    renewalArrivalMeasure T ω = Measure.sum fun n => Measure.dirac (arrival T (n + 1) ω) :=
  (rfl)

/-- Renewal arrivals are the finite-time specialization of the occurrence-sequence measure. -/
theorem renewalArrivalMeasure_eq_occurrenceTimeMeasure (ω : Ω) :
    renewalArrivalMeasure T ω =
      occurrenceTimeMeasure (fun n => (arrival T (n + 1) ω : ℝ≥0∞)) := by
  simp [renewalArrivalMeasure_def, occurrenceTimeMeasure_def]

/-- Renewal arrival measures are integer-valued, including when arrivals accumulate. -/
@[simp]
theorem isIntegerValued_renewalArrivalMeasure (ω : Ω) :
    (renewalArrivalMeasure T ω).IsIntegerValued := by
  rw [renewalArrivalMeasure_eq_occurrenceTimeMeasure]
  exact isIntegerValued_occurrenceTimeMeasure _

/-- Evaluation counts occurrences, rather than distinct arrival locations. -/
theorem renewalArrivalMeasure_apply (ω : Ω) (s : Set ℝ≥0) :
    renewalArrivalMeasure T ω s = ∑' n, s.indicator (fun _ => (1 : ℝ≥0∞))
      (arrival T (n + 1) ω) := by
  simp [renewalArrivalMeasure_def, Measure.sum_apply_of_countable, Measure.dirac_apply,
    Pi.one_def]

/-- Counting arrivals on `[0,t]` recovers the extended renewal count, including at zero. -/
@[simp]
theorem renewalArrivalMeasure_Iic (ω : Ω) (t : ℝ≥0) :
    renewalArrivalMeasure T ω (Iic t) = renewalCount T t ω := by
  simp [renewalArrivalMeasure_apply, renewalCount_def,
    Set.indicator_apply]

/-- Extracting occurrences from the arrival measure recovers every positive-index
arrival, even with zero increments or explosion. The artificial index-zero arrival
is not inserted by occurrence extraction. -/
@[simp]
theorem occurrenceTime_renewalArrivalMeasure (ω : Ω) (n : ℕ) :
    (renewalArrivalMeasure T ω).occurrenceTime n = (arrival T (n + 1) ω : ℝ≥0∞) := by
  rw [renewalArrivalMeasure_eq_occurrenceTimeMeasure,
    occurrenceTime_occurrenceTimeMeasure (fun _ _ h => by
      exact_mod_cast monotone_arrival T ω (Nat.succ_le_succ h))]

/-- Extracting interarrival gaps from the arrival measure recovers every renewal increment,
including zero increments and explosive paths. -/
@[simp]
theorem occurrenceGap_renewalArrivalMeasure (ω : Ω) (n : ℕ) :
    (renewalArrivalMeasure T ω).occurrenceGap n = (T n ω : ℝ≥0∞) := by
  cases n with
  | zero => simp [arrival_succ]
  | succ n =>
    rw [Measure.occurrenceGap_succ_of_ne_top (by simp),
      occurrenceTime_renewalArrivalMeasure, occurrenceTime_renewalArrivalMeasure,
      arrival_succ, ENNReal.coe_add, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]

/-- Integration against the arrival measure sums the test function over all arrivals. -/
@[simp]
theorem lintegral_renewalArrivalMeasure (ω : Ω) (f : ℝ≥0 → ℝ≥0∞) :
    ∫⁻ x, f x ∂renewalArrivalMeasure T ω = ∑' n, f (arrival T (n + 1) ω) := by
  simp [renewalArrivalMeasure_def, lintegral_sum_measure]

/-- Forming the arrival measure commutes with changing the sample space. -/
@[simp]
theorem renewalArrivalMeasure_comp {Ω' : Type*} (g : Ω' → Ω) (ω : Ω') :
    renewalArrivalMeasure (fun n ω => T n (g ω)) ω = renewalArrivalMeasure T (g ω) := by
  simp only [renewalArrivalMeasure_def, arrival_def]

/-- A renewal arrival measure is locally finite exactly when its arrival times diverge. -/
theorem isLocallyFiniteMeasure_renewalArrivalMeasure_iff (ω : Ω) :
    IsLocallyFiniteMeasure (renewalArrivalMeasure T ω) ↔
      Tendsto (fun n => arrival T n ω) atTop atTop := by
  rw [renewalArrivalMeasure_eq_occurrenceTimeMeasure,
    isLocallyFiniteMeasure_occurrenceTimeMeasure_iff, ENNReal.tendsto_coe_nhds_top]
  exact Filter.tendsto_add_atTop_iff_nat (f := fun n => arrival T n ω) 1

/-- On a nonexplosive path, counting arrivals on `[0, t]` recovers the cast natural renewal
count, including at zero. -/
theorem renewalArrivalMeasure_Iic_eq_renewalCountNat {ω : Ω}
    (hω : Tendsto (fun n => arrival T n ω) atTop atTop) (t : ℝ≥0) :
    renewalArrivalMeasure T ω (Iic t) = (renewalCountNat T t ω : ℝ≥0∞) := by
  rw [renewalArrivalMeasure_Iic, natCast_renewalCountNat hω]

/-- A positive first increment rules out any arrival at zero; later increments may vanish. -/
theorem renewalArrivalMeasure_singleton_zero {ω : Ω} (hT : 0 < T 0 ω) :
    renewalArrivalMeasure T ω {0} = 0 := by
  rw [renewalArrivalMeasure_def, Measure.sum_apply _ (measurableSet_singleton 0)]
  refine tsum_eq_zero_iff.mpr fun n => ?_
  rw [Measure.dirac_apply]
  apply Set.indicator_of_notMem
  have hfirst : arrival T 1 ω = T 0 ω := by simp [arrival_succ]
  have hle : T 0 ω ≤ arrival T (n + 1) ω := by
    simpa only [hfirst] using monotone_arrival T ω (Nat.succ_le_succ (Nat.zero_le n))
  simpa only [mem_singleton_iff] using ne_of_gt (hT.trans_le hle)

/-- If the first increment is positive, counting on `(0,t]` agrees with counting on `[0,t]`.
No nonexplosion assumption is needed, and the count may be infinite. -/
theorem renewalArrivalMeasure_Ioc {ω : Ω} (hT : 0 < T 0 ω) (t : ℝ≥0) :
    renewalArrivalMeasure T ω (Ioc 0 t) = renewalCount T t ω := by
  rw [← bot_eq_zero,
    measure_Ioc_bot_eq_measure_Iic (renewalArrivalMeasure_singleton_zero T hT),
    renewalArrivalMeasure_Iic]

/-- On a nonexplosive path with a positive first increment, counting arrivals on `(0, t]`
recovers the cast natural renewal count. -/
theorem renewalArrivalMeasure_Ioc_eq_renewalCountNat {ω : Ω}
    (hω : Tendsto (fun n => arrival T n ω) atTop atTop) (hT : 0 < T 0 ω) (t : ℝ≥0) :
    renewalArrivalMeasure T ω (Ioc 0 t) = (renewalCountNat T t ω : ℝ≥0∞) := by
  rw [renewalArrivalMeasure_Ioc T hT, natCast_renewalCountNat hω]

/-- Positive increments after the first give singleton masses at most one: there are no
coincident arrivals. The first increment may vanish, and no nonexplosion assumption is needed. -/
theorem renewalArrivalMeasure_singleton_le_one {ω : Ω} (hT : ∀ n, 0 < T (n + 1) ω)
    (x : ℝ≥0) : renewalArrivalMeasure T ω {x} ≤ 1 := by
  rw [renewalArrivalMeasure_def, Measure.sum_apply _ (measurableSet_singleton x)]
  by_cases hx : ∃ n, arrival T (n + 1) ω = x
  · obtain ⟨n, rfl⟩ := hx
    rw [tsum_eq_single n]
    · simp
    · intro m hmn
      rw [Measure.dirac_apply]
      exact Set.indicator_of_notMem (by
        simpa using fun h => hmn ((strictMono_arrival_succ T hT).injective h)) _
  · have hn : ∀ n, arrival T (n + 1) ω ≠ x := by simpa using hx
    simp [hn]

variable {T} [MeasurableSpace Ω]

private lemma measurable_dirac_arrival_apply (hT : ∀ n, Measurable (T n))
    {s : Set ℝ≥0} (hs : MeasurableSet s) (n : ℕ) :
    Measurable fun ω => Measure.dirac (arrival T (n + 1) ω) s :=
  (Measure.measurable_coe hs).comp
    (Measure.measurable_dirac.comp (measurable_arrival hT (n + 1)))

/-- Measurable increments give a random measure for the evaluation σ-algebra on measures. -/
@[fun_prop]
theorem measurable_renewalArrivalMeasure (hT : ∀ n, Measurable (T n)) :
    Measurable (renewalArrivalMeasure T) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [renewalArrivalMeasure_def, Measure.sum_apply _ hs]
  exact Measurable.tsum (measurable_dirac_arrival_apply hT hs)

variable {P : Measure Ω}

/-- Nondegenerate i.i.d. increments give almost surely locally finite arrival measures. -/
theorem ae_isLocallyFiniteMeasure_renewalArrivalMeasure
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (renewalArrivalMeasure T ω) := by
  filter_upwards [ae_tendsto_arrival_atTop hindep hid hzero] with ω hω
  exact (isLocallyFiniteMeasure_renewalArrivalMeasure_iff T ω).2 hω

/-- The whole random arrival measure, not merely each separate count, has the same law in
any i.i.d. realization as on the canonical product space. -/
theorem map_renewalArrivalMeasure_eq_infinitePi_map (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    P.map (renewalArrivalMeasure T) =
      (Measure.infinitePi fun _ : ℕ => P.map (T 0)).map
        (renewalArrivalMeasure (fun n (w : ℕ → ℝ≥0) => w n)) := by
  have hcomp : renewalArrivalMeasure T =
      renewalArrivalMeasure (fun n (w : ℕ → ℝ≥0) => w n) ∘ (fun ω n => T n ω) := by
    funext ω
    exact (renewalArrivalMeasure_comp (fun n (w : ℕ → ℝ≥0) => w n)
      (fun ω n => T n ω) ω)
  rw [hcomp, ← Measure.map_map
    (measurable_renewalArrivalMeasure (fun n => measurable_pi_apply n))
    (measurable_pi_iff.2 hT), hindep.map_fun_eq_infinitePi_map hT]
  simp_rw [fun n => (hid n).map_eq]

/-- The intensity of the arrival measure is the renewal measure with the artificial initial
arrival removed, expressed without subtraction as `F ∗ U`. This includes explosive laws. -/
theorem bind_renewalArrivalMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    P.bind (renewalArrivalMeasure T) = (P.map (T 0)) ∗ (P.map (T 0)).renewalMeasure := by
  have := hindep.isProbabilityMeasure
  ext s hs
  rw [Measure.bind_apply hs (measurable_renewalArrivalMeasure hT).aemeasurable,
    Measure.conv_renewalMeasure, Measure.sum_apply _ hs]
  simp only [renewalArrivalMeasure_def, Measure.sum_apply _ hs]
  rw [lintegral_tsum (f := fun n ω => (Measure.dirac (arrival T (n + 1) ω)) s)
    fun n => (measurable_dirac_arrival_apply hT hs n).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [← Measure.bind_apply (f := fun ω => Measure.dirac (arrival T (n + 1) ω)) hs
    (Measure.measurable_dirac.comp (measurable_arrival hT (n + 1))).aemeasurable,
    Measure.bind_dirac_eq_map P (measurable_arrival hT (n + 1)),
    (hasLaw_arrival hindep hid (n + 1)).map_eq]

/-- For exponential increments the arrival-measure counts on `(0,t]` agree with the natural
renewal counts, on one event for every time. -/
theorem ae_renewalArrivalMeasure_Ioc_eq_of_expMeasure {r : ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω => (T n ω : ℝ)) (expMeasure r) P) :
    ∀ᵐ ω ∂P, ∀ t, renewalArrivalMeasure T ω (Ioc 0 t) = (renewalCountNat T t ω : ℝ≥0∞) := by
  filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw,
    ae_pos_of_hasLaw_expMeasure (hlaw 0)] with ω hω hpos t
  exact renewalArrivalMeasure_Ioc_eq_renewalCountNat T hω (by exact_mod_cast hpos) t

/-- The natural counts of exponential renewal arrivals on `(0,t]` have the Poisson law.
Taking the natural floor of the real mass only changes the count on a null set. -/
theorem hasLaw_renewalArrivalMeasure_Ioc_poissonMeasure {r : ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω => (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    HasLaw (fun ω => ⌊(renewalArrivalMeasure T ω (Ioc 0 t)).toReal⌋₊)
      (poissonMeasure (r * t)) P := by
  apply (hasLaw_renewalCountNat_poissonMeasure hindep hlaw t).congr
  filter_upwards [ae_renewalArrivalMeasure_Ioc_eq_of_expMeasure hindep hlaw] with ω hω
  simp [hω t]

section OccurrenceGap

/-- When the `n`-th occurrence time of `μ` is finite, the `(n + 1)`-st renewal arrival time of
its `ℝ≥0` interarrival-gap representatives on the canonical space `Measure ℝ≥0` equals that
occurrence time. -/
theorem arrival_toNNReal_occurrenceGap {μ : Measure ℝ≥0} {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) :
    arrival (fun i (ν : Measure ℝ≥0) => (ν.occurrenceGap i).toNNReal) (n + 1) μ =
      (μ.occurrenceTime n).toNNReal := by
  rw [arrival_def, μ.sum_range_toNNReal_occurrenceGap hn]

/-- Any locally finite integer-valued measure on `ℝ≥0` whose occurrence times are all finite
equals the renewal arrival measure of its `ℝ≥0` interarrival-gap representatives on the canonical
space `Measure ℝ≥0`. Atoms at zero and coincident occurrences are allowed. -/
theorem eq_renewalArrivalMeasure_toNNReal_occurrenceGap {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued)
    (hfin : ∀ n, μ.occurrenceTime n ≠ ∞) :
    μ = renewalArrivalMeasure (fun n (ν : Measure ℝ≥0) => (ν.occurrenceGap n).toNNReal) μ := by
  rw [renewalArrivalMeasure_eq_occurrenceTimeMeasure]
  have hseq : (fun n =>
      (arrival (fun i (ν : Measure ℝ≥0) => (ν.occurrenceGap i).toNNReal) (n + 1) μ : ℝ≥0∞)) =
      μ.occurrenceTime := by
    funext n
    rw [arrival_toNNReal_occurrenceGap (hfin n), ENNReal.coe_toNNReal (hfin n)]
  rw [hseq]
  exact hμ.eq_occurrenceTimeMeasure

/-- For a locally finite counting measure on `ℝ≥0` having at least one finite occurrence strictly
after `t`, the mass of `[0, t]` equals the extended renewal count of its `ℝ≥0` interarrival-gap
representatives on the canonical space `Measure ℝ≥0`. -/
theorem apply_Iic_eq_renewalCount_toNNReal_occurrenceGap {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued)
    {t : ℝ≥0} (hfin : ∃ n, t < (μ.occurrenceTime n).toNNReal) :
    μ (Iic t) =
      renewalCount (fun n (ν : Measure ℝ≥0) => (ν.occurrenceGap n).toNNReal) t μ := by
  obtain ⟨n, hn⟩ := hfin
  have hn_ne : μ.occurrenceTime n ≠ ∞ := fun h => by simp [h] at hn
  let T : ℕ → Measure ℝ≥0 → ℝ≥0 := fun i ν => (ν.occurrenceGap i).toNNReal
  calc
    μ (Iic t) = occurrenceTimeMeasure μ.occurrenceTime (Iic t) := by
      conv_lhs => rw [hμ.eq_occurrenceTimeMeasure]
    _ = ∑' k, if μ.occurrenceTime k ≤ t then (1 : ℝ≥0∞) else 0 := occurrenceTimeMeasure_Iic _ t
    _ = ∑' k, if arrival T (k + 1) μ ≤ t then (1 : ℝ≥0∞) else 0 := by
      refine tsum_congr fun k => ?_
      have hiff : μ.occurrenceTime k ≤ (t : ℝ≥0∞) ↔ arrival T (k + 1) μ ≤ t := by
        rcases le_or_gt k n with hkn | hnk
        · have hk_ne : μ.occurrenceTime k ≠ ∞ :=
            ne_top_of_le_ne_top hn_ne (μ.monotone_occurrenceTime hkn)
          rw [arrival_toNNReal_occurrenceGap hk_ne, ← ENNReal.coe_le_coe,
            ENNReal.coe_toNNReal hk_ne]
        · have hlt_time : (t : ℝ≥0∞) < μ.occurrenceTime k := by
            have hnt : (t : ℝ≥0∞) < μ.occurrenceTime n := by
              rw [← ENNReal.coe_toNNReal hn_ne, ENNReal.coe_lt_coe]
              exact hn
            exact hnt.trans_le (μ.monotone_occurrenceTime hnk.le)
          have hlt_arr : t < arrival T (k + 1) μ := by
            have hna : t < arrival T (n + 1) μ := by
              rwa [arrival_toNNReal_occurrenceGap hn_ne]
            exact hna.trans_le (monotone_arrival T μ (Nat.succ_le_succ hnk.le))
          simp [hlt_time.not_ge, hlt_arr.not_ge]
      simp [hiff]
    _ = renewalCount T t μ := (renewalCount_def T t μ).symm

/-- For a locally finite counting measure on `ℝ≥0` whose occurrence times are all finite, the
mass of `[0, t]` equals the natural-valued renewal count of its `ℝ≥0` interarrival-gap
representatives on the canonical space `Measure ℝ≥0`. -/
theorem apply_Iic_eq_renewalCountNat_toNNReal_occurrenceGap {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued)
    (hfin : ∀ n, μ.occurrenceTime n ≠ ∞) (t : ℝ≥0) :
    μ (Iic t) =
      (renewalCountNat (fun n (ν : Measure ℝ≥0) => (ν.occurrenceGap n).toNNReal) t μ : ℝ≥0∞) := by
  have heq := eq_renewalArrivalMeasure_toNNReal_occurrenceGap hμ hfin
  have htend : Tendsto
      (fun n => arrival (fun i (ν : Measure ℝ≥0) => (ν.occurrenceGap i).toNNReal) n μ)
      atTop atTop :=
    (isLocallyFiniteMeasure_renewalArrivalMeasure_iff _ μ).mp (heq ▸ inferInstance)
  conv_lhs => rw [heq]
  exact renewalArrivalMeasure_Iic_eq_renewalCountNat _ htend t

end OccurrenceGap

end TauCeti.Probability
