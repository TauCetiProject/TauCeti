/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Count

/-!
# Interarrival gaps from ordered occurrence times

`Measure.occurrenceGap μ` extracts the sequence of nonnegative waiting times between successive
ordered occurrences of a measure `μ` on the half-line: index zero is the first occurrence time,
and index `n + 1` is the increment from occurrence `n` to occurrence `n + 1`. Infinite
occurrence times convert via `ENNReal.toNNReal` to zero, so the map is total and measurable
into `ℕ → ℝ≥0` without restricting the domain to locally finite or infinite-mass measures.

Whenever occurrence `n` is finite, the partial sum of the first `n + 1` gaps recovers
`μ.occurrenceTime n`. Conversely, a strictly positive gap forces the corresponding occurrence
time to be finite, and strictly positive gaps at all indices force infinite total mass. For a
locally finite integer-valued measure of infinite total mass, the partial sums of its gaps
reconstruct the measure as a countable sum of Dirac masses, and equality in law of the full gap
sequence determines equality in law of the random measures.

The zero measure and the Dirac mass at zero both have identically zero gaps, so infinite total
mass is necessary for reconstruction from gaps alone. No simplicity hypothesis or assumption on
the atom at zero is needed for measurability, reconstruction, or law transfer; positivity of
the gaps separately records absence of mass at zero and simplicity at each occurrence.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- The interarrival gaps of a measure on `ℝ≥0`: index `0` is the first occurrence time, and
index `n + 1` is the increment from occurrence `n` to occurrence `n + 1`. Infinite occurrence
times map via `ENNReal.toNNReal` to `0`, so the map is defined on all measures. -/
noncomputable def occurrenceGap (μ : Measure ℝ≥0) : ℕ → ℝ≥0
  | 0 => (μ.occurrenceTime 0).toNNReal
  | n + 1 => (μ.occurrenceTime (n + 1)).toNNReal - (μ.occurrenceTime n).toNNReal

/-- The initial gap is the finite part of the first occurrence time. -/
theorem occurrenceGap_zero (μ : Measure ℝ≥0) :
    μ.occurrenceGap 0 = (μ.occurrenceTime 0).toNNReal := (rfl)

/-- Each subsequent gap is the truncated difference of consecutive finite occurrence times. -/
theorem occurrenceGap_succ (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap (n + 1) =
      (μ.occurrenceTime (n + 1)).toNNReal - (μ.occurrenceTime n).toNNReal := (rfl)

/-- Each interarrival gap is measurable for the evaluation σ-algebra on measures, without
imposing local finiteness or infinite total mass on the domain. -/
@[fun_prop]
theorem measurable_occurrenceGap_apply (n : ℕ) :
    Measurable fun μ : Measure ℝ≥0 => μ.occurrenceGap n := by
  cases n with
  | zero => exact (measurable_occurrenceTime 0).ennreal_toNNReal
  | succ n =>
    exact (measurable_occurrenceTime (n + 1)).ennreal_toNNReal.sub
      (measurable_occurrenceTime n).ennreal_toNNReal

/-- Extracting the entire sequence of interarrival gaps is measurable. -/
@[fun_prop]
theorem measurable_occurrenceGap :
    Measurable fun μ : Measure ℝ≥0 => μ.occurrenceGap :=
  measurable_pi_iff.mpr measurable_occurrenceGap_apply

/-- The zero measure has identically zero interarrival gaps. -/
@[simp]
theorem occurrenceGap_zero_measure (n : ℕ) : (0 : Measure ℝ≥0).occurrenceGap n = 0 := by
  cases n <;> simp [occurrenceGap_zero, occurrenceGap_succ]

/-- A single location with positive multiplicity `k` gives a single gap at index zero and zero
gaps thereafter; multiplicity zero yields all zeros. -/
@[simp]
theorem occurrenceGap_nsmul_dirac (k : ℕ) (t : ℝ≥0) (n : ℕ) :
    (k • dirac t).occurrenceGap n = if n = 0 ∧ 0 < k then t else 0 := by
  cases n with
  | zero =>
    by_cases hk : 0 < k <;> simp [occurrenceGap_zero, hk]
  | succ m =>
    simp only [occurrenceGap_succ, occurrenceTime_nsmul_dirac, Nat.succ_ne_zero, false_and,
      ↓reduceIte]
    by_cases hm : m + 1 < k
    · have hm' : m < k := Nat.lt_of_succ_lt hm
      simp [hm, hm']
    · simp [hm]

/-- A single Dirac mass at `t` has initial gap `t` and zero gaps thereafter. -/
@[simp]
theorem occurrenceGap_dirac (t : ℝ≥0) (n : ℕ) :
    (dirac t).occurrenceGap n = if n = 0 then t else 0 := by
  simpa using occurrenceGap_nsmul_dirac 1 t n

/-- A strictly positive `n`-th gap rules out an infinite `n`-th occurrence time, without any
local finiteness or integrality hypothesis. -/
theorem occurrenceTime_ne_top_of_occurrenceGap_pos {μ : Measure ℝ≥0} {n : ℕ}
    (h : 0 < μ.occurrenceGap n) : μ.occurrenceTime n ≠ ∞ := by
  intro htop
  cases n with
  | zero => simp [occurrenceGap_zero, htop] at h
  | succ m => simp [occurrenceGap_succ, htop] at h

/-- Strictly positive interarrival gaps at every index force infinite total mass. -/
theorem apply_univ_eq_top_of_forall_occurrenceGap_pos {μ : Measure ℝ≥0}
    (h : ∀ n, 0 < μ.occurrenceGap n) : μ univ = ∞ :=
  (forall_occurrenceTime_ne_top_iff μ).mp fun n =>
    occurrenceTime_ne_top_of_occurrenceGap_pos (h n)

/-- Whenever occurrence `n` is finite, summing the first `n + 1` interarrival gaps recovers
its finite value. No local finiteness or integrality assumption is needed. -/
theorem sum_range_occurrenceGap_eq_toNNReal_occurrenceTime (μ : Measure ℝ≥0) {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) :
    ∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i = (μ.occurrenceTime n).toNNReal := by
  induction n with
  | zero => simp [occurrenceGap_zero]
  | succ n ih =>
    have hle : μ.occurrenceTime n ≤ μ.occurrenceTime (n + 1) :=
      μ.monotone_occurrenceTime (Nat.le_succ n)
    have hn' : μ.occurrenceTime n ≠ ∞ := ne_top_of_le_ne_top hn hle
    rw [Finset.sum_range_succ, ih hn', occurrenceGap_succ]
    exact add_tsub_cancel_of_le (ENNReal.toNNReal_mono hn hle)

/-- Extended-valued form of `sum_range_occurrenceGap_eq_toNNReal_occurrenceTime`: partial sums
of gaps recover finite occurrence times in `ℝ≥0∞`. -/
theorem coe_sum_range_occurrenceGap_eq_occurrenceTime (μ : Measure ℝ≥0) {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) :
    ((∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i : ℝ≥0) : ℝ≥0∞) = μ.occurrenceTime n := by
  rw [sum_range_occurrenceGap_eq_toNNReal_occurrenceTime μ hn, ENNReal.coe_toNNReal hn]

/-- Absence of mass at the origin makes a finite first occurrence gap strictly positive for a
locally finite measure. Integrality is not needed; local finiteness rules out accumulation of
mass approaching zero. -/
theorem occurrenceGap_zero_pos {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]
    (h0 : μ {0} = 0) (hfin : μ.occurrenceTime 0 ≠ ∞) : 0 < μ.occurrenceGap 0 := by
  rw [occurrenceGap_zero, pos_iff_ne_zero]
  intro hzero
  have hle : μ.occurrenceTime 0 ≤ (0 : ℝ≥0) := by
    rw [← ENNReal.coe_toNNReal hfin, hzero]
  have hmass := (μ.occurrenceTime_le_iff 0 0).1 hle
  have hIic : Iic (0 : ℝ≥0) = {0} := by ext x; simp
  rw [hIic, h0] at hmass
  simp at hmass

/-- Simplicity at a finite occurrence makes the next finite interarrival gap strictly positive.
Other locations need not be simple. -/
theorem IsIntegerValued.occurrenceGap_succ_pos {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) {n : ℕ} (hnext : μ.occurrenceTime (n + 1) ≠ ∞)
    (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) : 0 < μ.occurrenceGap (n + 1) := by
  have hn : μ.occurrenceTime n ≠ ∞ :=
    ne_top_of_le_ne_top hnext (μ.monotone_occurrenceTime (Nat.le_succ n))
  have hlt : (μ.occurrenceTime n).toNNReal < (μ.occurrenceTime (n + 1)).toNNReal := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hn, ENNReal.coe_toNNReal hnext]
    exact hμ.occurrenceTime_lt_succ hn hs
  rw [occurrenceGap_succ]
  exact tsub_pos_of_lt hlt

/-- For two finite consecutive occurrences, the gap exceeds `s` exactly when there is no
occurrence in the closed-right window of duration `s` after the first. Simplicity is needed
only at the first occurrence. -/
theorem IsIntegerValued.lt_occurrenceGap_succ_iff {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) {n : ℕ} (hn : μ.occurrenceTime n ≠ ∞)
    (hnext : μ.occurrenceTime (n + 1) ≠ ∞) (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1)
    (s : ℝ≥0) :
    s < μ.occurrenceGap (n + 1) ↔
      μ (Ioc (μ.occurrenceTime n).toNNReal ((μ.occurrenceTime n).toNNReal + s)) = 0 :=
  hμ.lt_toNNReal_occurrenceTime_sub_iff hn hnext hs s

/-- A locally finite integer-valued measure of infinite total mass is reconstructed as the sum
of Dirac masses at the partial sums of its interarrival gaps. Atoms at zero and multiple
occurrences are allowed. -/
theorem IsIntegerValued.eq_sum_dirac_sum_occurrenceGap {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued) (huniv : μ univ = ∞) :
    μ = Measure.sum fun n => Measure.dirac (∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i) := by
  have hfin : ∀ n, μ.occurrenceTime n ≠ ∞ := (forall_occurrenceTime_ne_top_iff μ).2 huniv
  calc
    μ = TauCeti.Probability.occurrenceTimeMeasure μ.occurrenceTime := hμ.eq_occurrenceTimeMeasure
    _ = Measure.sum fun n => Measure.dirac (∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i) := by
      rw [TauCeti.Probability.occurrenceTimeMeasure_def]
      congr 1
      funext n
      rw [ite_eq_right (hfin n), sum_range_occurrenceGap_eq_toNNReal_occurrenceTime μ (hfin n)]

/-- On locally finite counting measures of infinite total mass, equality of interarrival gap
sequences is equivalent to equality of measures. Both integrality and infinite total mass are
essential: `0` and `dirac 0` share the zero gap sequence. -/
@[simp]
theorem IsIntegerValued.occurrenceGap_inj {μ ν : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hμ : μ.IsIntegerValued) (hν : ν.IsIntegerValued)
    (hμu : μ univ = ∞) (hνu : ν univ = ∞) :
    μ.occurrenceGap = ν.occurrenceGap ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [hμ.eq_sum_dirac_sum_occurrenceGap hμu, hν.eq_sum_dirac_sum_occurrenceGap hνu, h]

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- Reading interarrival gaps from the occurrence measure of partial sums recovers the input
gaps, without positivity or nonaccumulation hypotheses. -/
@[simp]
theorem occurrenceGap_occurrenceTimeMeasure_sum (g : ℕ → ℝ≥0) (n : ℕ) :
    (occurrenceTimeMeasure
      (fun k => ∑ i ∈ Finset.range (k + 1), (g i : ℝ≥0∞))).occurrenceGap n = g n := by
  have hmono : Monotone fun k => ∑ i ∈ Finset.range (k + 1), (g i : ℝ≥0∞) :=
    fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right h 1))
  have hocc := occurrenceTime_occurrenceTimeMeasure hmono
  cases n with
  | zero =>
    rw [Measure.occurrenceGap_zero, hocc]
    simp
  | succ n =>
    rw [Measure.occurrenceGap_succ, hocc, ENNReal.toNNReal_sum fun _ _ => ENNReal.coe_ne_top,
      ENNReal.toNNReal_sum fun _ _ => ENNReal.coe_ne_top]
    simp [Finset.sum_range_succ]

end TauCeti.Probability

namespace ProbabilityTheory.IdentDistrib

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure ℝ≥0} {N' : Ω' → Measure ℝ≥0}

/-- Equality in law of the full interarrival gap sequence implies equality in law of the
temporal counting measures, assuming local finiteness, integrality, and infinite total mass
almost surely. Neither simplicity nor absence of an atom at zero is required. -/
theorem of_occurrenceGap
    (h : IdentDistrib (fun ω => (N ω).occurrenceGap)
      (fun ω => (N' ω).occurrenceGap) P P')
    (hN : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) ∧ (N ω).IsIntegerValued ∧ N ω univ = ∞)
    (hN' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (N' ω) ∧ (N' ω).IsIntegerValued ∧ N' ω univ = ∞) :
    IdentDistrib N N' P P' := by
  let F : (ℕ → ℝ≥0) → ℕ → ℝ≥0∞ :=
    fun g n => ((∑ i ∈ Finset.range (n + 1), g i : ℝ≥0) : ℝ≥0∞)
  have hF : Measurable F :=
    measurable_pi_iff.mpr fun n =>
      (Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i).coe_nnreal_ennreal
  have hFcomp := h.comp hF
  have haeN : F ∘ (fun ω => (N ω).occurrenceGap) =ᵐ[P] fun ω => (N ω).occurrenceTime := by
    filter_upwards [hN] with ω hω
    funext n
    exact (N ω).coe_sum_range_occurrenceGap_eq_occurrenceTime
      ((Measure.forall_occurrenceTime_ne_top_iff (N ω)).2 hω.2.2 n)
  have haeN' : F ∘ (fun ω => (N' ω).occurrenceGap) =ᵐ[P'] fun ω => (N' ω).occurrenceTime := by
    filter_upwards [hN'] with ω hω
    funext n
    exact (N' ω).coe_sum_range_occurrenceGap_eq_occurrenceTime
      ((Measure.forall_occurrenceTime_ne_top_iff (N' ω)).2 hω.2.2 n)
  have hocc : IdentDistrib (fun ω => (N ω).occurrenceTime)
      (fun ω => (N' ω).occurrenceTime) P P' :=
    (IdentDistrib.of_ae_eq hFcomp.aemeasurable_fst haeN).symm.trans
      (hFcomp.trans (IdentDistrib.of_ae_eq hFcomp.aemeasurable_snd haeN'))
  exact hocc.of_occurrenceTime (hN.mono fun _ h => ⟨h.1, h.2.1⟩)
    (hN'.mono fun _ h => ⟨h.1, h.2.1⟩)

end ProbabilityTheory.IdentDistrib
