/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Path
public import TauCeti.Probability.PointProcess.Poisson.Temporal
public import TauCeti.Probability.Process.Poisson.Microscopic
import TauCeti.MeasureTheory.Measure.Interval

/-!
# The microscopic characterization of temporal Poisson point processes

For a measurable random measure `M : Ω → Measure ℝ≥0` represented almost surely by a
natural-valued cumulative count process `N` (`∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = N t ω`), combining the
count-increment recognition theorems in `TauCeti.Probability.PointProcess.Poisson.Temporal` with
the scalar small-time Poisson limit theorem yields the microscopic characterization of homogeneous
temporal Poisson point processes:

`M` is a rate-`r` homogeneous Poisson random measure on `ℝ≥0` if and only if `N 0 = 0` almost
surely, `N` has stationary independent increments, and as `h ↓ 0`,

```text
P(N h = 1) = r * h + o(h),       P(N h ≥ 2) = o(h).
```

Both the Landau `=o[𝓝[>] 0]` formulation and the quotient `Tendsto` formulation are provided,
together with their specializations to `countPathMeasure (N · ω)` for a natural-valued process `N`
measurable at nonnegative rational times whose sample paths are monotone and right-continuous on
one event of full measure. Rate `r = 0` is included alongside `r > 0`. Path monotonicity and
right-continuity are required only on one common event of full measure, without assuming
measurability of that event; natural values automatically exclude explosion at finite times.

Independently of independent increments and measurability, stationary increment laws together with
`P(N h - N 0 ≥ 2) = o(h)` already imply almost-sure simplicity (`∀ t > 0, M ω {t} ≤ 1`, and at all
`t : ℝ≥0` when `N 0 ≤ 1` almost surely) via the equal-mesh subdivision bound for multiple jumps.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, §9.5, microscopic
  characterization of the Poisson process.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 3 and 7.
-/

public section

open Asymptotics Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal NNRat

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

private theorem ae_le_of_ae_measure_Iic_eq {M : Ω → Measure ℝ≥0}
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞))
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, N s ω ≤ N t ω :=
  (ae_monotone_of_ae_measure_Iic_eq hcount).mono fun _ h ↦ h hst

/-! ### Simplicity from microscopic multiple-jump bounds -/

/-- Stationary increment laws and `P(N h - N 0 ≥ 2) = o(h)` imply that any random measure `M`
represented almost surely by cumulative counts `N` has singleton mass at most one simultaneously
at all positive times. Neither independent increments nor measurability of `M` or `N` is
assumed. -/
theorem ae_forall_pos_measure_singleton_le_one_of_small_time [IsFiniteMeasure P]
    {M : Ω → Measure ℝ≥0}
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞))
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h : ℝ≥0 ↦ (h : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ≥0), M ω {t} ≤ 1 := by
  have hjump := ae_count_le_add_one_of_small_time (ae_monotone_of_ae_measure_Iic_eq hcount)
    hstat hsmall
  filter_upwards [hcount, hjump] with ω hω hj t ht
  obtain ⟨s, hst, hle⟩ := hj t ht
  have hIoc : M ω (Ioc s t) ≤ 1 := by
    rw [Measure.measure_Ioc_eq_natCast_sub (hω s) (hω t)]
    have hsub : N t ω - N s ω ≤ 1 := by omega
    exact_mod_cast hsub
  have hsubset : {t} ⊆ Ioc s t := singleton_subset_iff.mpr ⟨hst, le_rfl⟩
  exact (measure_mono hsubset).trans hIoc

/-- Stationary increment laws and `P(N h - N 0 ≥ 2) = o(h)` imply that
`countPathMeasure (N · ω)` has singleton mass at most one simultaneously at all positive times,
whenever sample paths are monotone and right-continuous on one event of full measure. Neither
independent increments nor coordinate measurability is assumed. -/
theorem ae_forall_pos_countPathMeasure_singleton_le_one_of_small_time [IsFiniteMeasure P]
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω))
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h : ℝ≥0 ↦ (h : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ≥0), countPathMeasure (N · ω) {t} ≤ 1 :=
  ae_forall_pos_measure_singleton_le_one_of_small_time (ae_countPathMeasure_Iic_eq hreg) hstat
    hsmall

/-- If in addition `N 0 ≤ 1` almost surely, stationary increment laws and
`P(N h - N 0 ≥ 2) = o(h)` make any random measure `M` represented almost surely by cumulative
counts `N` simple at every time in `ℝ≥0`, including the origin. -/
theorem ae_forall_measure_singleton_le_one_of_small_time [IsFiniteMeasure P]
    {M : Ω → Measure ℝ≥0}
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞))
    (h0 : ∀ᵐ ω ∂P, N 0 ω ≤ 1)
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h : ℝ≥0 ↦ (h : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t, M ω {t} ≤ 1 := by
  filter_upwards [hcount, h0,
    ae_forall_pos_measure_singleton_le_one_of_small_time hcount hstat hsmall] with ω hω h0ω hpos t
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · have hIic : Iic (0 : ℝ≥0) = {0} := by ext; simp
    rw [← hIic, hω 0]
    exact_mod_cast h0ω
  · exact hpos t ht

/-- If in addition `N 0 ≤ 1` almost surely, stationary increment laws and
`P(N h - N 0 ≥ 2) = o(h)` make `countPathMeasure (N · ω)` simple at every time in `ℝ≥0`,
including the origin. -/
theorem ae_forall_countPathMeasure_singleton_le_one_of_small_time [IsFiniteMeasure P]
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω))
    (h0 : ∀ᵐ ω ∂P, N 0 ω ≤ 1)
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h : ℝ≥0 ↦ (h : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t, countPathMeasure (N · ω) {t} ≤ 1 :=
  ae_forall_measure_singleton_le_one_of_small_time
    (ae_countPathMeasure_Iic_eq hreg) h0 hstat hsmall

/-! ### Microscopic characterizations of homogeneous temporal Poisson point processes -/

/-- **Microscopic characterization of homogeneous temporal Poisson point processes (quotient
form).** For a measurable random measure `M` on `ℝ≥0` represented almost surely by cumulative
counts `N`, `M` is a rate-`r` Poisson random measure on `ℝ≥0` if and only if `N 0 = 0` almost
surely, `N` has stationary independent increments, and `P(N h = 1) / h → r` and
`P(N h ≥ 2) / h → 0` as `h ↓ 0`. Both `r > 0` and `r = 0` are included. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_stationary_small_time
    {M : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0) := by
  rw [isPoissonRandomMeasure_smul_nnvolume_iff_count_increments hM hcount]
  exact and_congr_right fun h0 ↦ and_congr_right fun hind ↦
    hind.hasLaw_sub_poissonMeasure_iff_stationary_small_time h0
      (ae_le_of_ae_measure_Iic_eq hcount) r

/-- **Microscopic characterization of `countPathMeasure` (quotient form).** For a natural-valued
process measurable at nonnegative rational times whose paths are monotone and right-continuous on
one event of full measure, `countPathMeasure (N · ω)` is a rate-`r` Poisson random measure on `ℝ≥0`
if and only if `N 0 = 0` almost surely, `N` has stationary independent increments, and
`P(N h = 1) / h → r` and `P(N h ≥ 2) / h → 0` as `h ↓ 0`. Both `r > 0` and `r = 0` are
included. -/
theorem isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_stationary_small_time {r : ℝ≥0}
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0) :=
  isPoissonRandomMeasure_smul_nnvolume_iff_stationary_small_time
    (measurable_countPathMeasure_of_nnrat hN) (ae_countPathMeasure_Iic_eq hreg)

/-- **Microscopic characterization of homogeneous temporal Poisson point processes (`o(h)`
form).** For a measurable random measure `M` on `ℝ≥0` represented almost surely by cumulative
counts `N`, `M` is a rate-`r` Poisson random measure on `ℝ≥0` if and only if `N 0 = 0` almost
surely, `N` has stationary independent increments, `P(N h = 1) - r * h = o(h)`, and
`P(N h ≥ 2) = o(h)` as `h ↓ 0`. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_stationary_isLittleO
    {M : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) := by
  rw [isPoissonRandomMeasure_smul_nnvolume_iff_count_increments hM hcount]
  exact and_congr_right fun h0 ↦ and_congr_right fun hind ↦
    hind.hasLaw_sub_poissonMeasure_iff_stationary_isLittleO h0
      (ae_le_of_ae_measure_Iic_eq hcount) r

/-- **Microscopic characterization of `countPathMeasure` (`o(h)` form).** For a natural-valued
process measurable at nonnegative rational times whose paths are monotone and right-continuous on
one event of full measure, `countPathMeasure (N · ω)` is a rate-`r` Poisson random measure on `ℝ≥0`
if and only if `N 0 = 0` almost surely, `N` has stationary independent increments,
`P(N h = 1) - r * h = o(h)`, and `P(N h ≥ 2) = o(h)` as `h ↓ 0`. -/
theorem isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_stationary_isLittleO {r : ℝ≥0}
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) :=
  isPoissonRandomMeasure_smul_nnvolume_iff_stationary_isLittleO
    (measurable_countPathMeasure_of_nnrat hN) (ae_countPathMeasure_Iic_eq hreg)

end TauCeti.Probability
