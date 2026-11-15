/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Path
public import TauCeti.Probability.PointProcess.Poisson.Temporal
public import TauCeti.Probability.Process.Poisson.Microscopic

/-!
# The microscopic characterization of temporal Poisson point processes

For a natural-valued process `N` measurable at nonnegative rational times whose sample paths are
nondecreasing and right-continuous on one event of probability one, `countPathMeasure (N · ω)` is
a measurable random counting measure on `ℝ≥0`. Combining the path-to-measure conversion in
`TauCeti.Probability.PointProcess.OccurrenceTime.Path` with the scalar small-time Poisson limit
theorem and the equal-mesh subdivision bound for multiple jumps yields the microscopic
characterization of homogeneous temporal Poisson point processes:

`countPathMeasure (N · ω)` is a rate-`r` homogeneous Poisson random measure on `ℝ≥0` (and in
particular is almost surely locally finite, has no atom at zero, and is simple) if and only if
`N 0 = 0` almost surely, `N` has stationary independent increments, and as `h ↓ 0`,

```text
P(N h = 1) = r * h + o(h),       P(N h ≥ 2) = o(h).
```

Both the Landau `=o[𝓝[>] 0]` formulation and the quotient `Tendsto` formulation are provided, and
rate `r = 0` is included alongside `r > 0`. Path monotonicity and right-continuity are required
only on one common event of full measure, without assuming measurability of that event; natural
values automatically exclude explosion at finite times. When all coordinates `N t` are measurable,
this is also equivalent to `(N t ω : ℝ)` being a rate-`r` `IsFilteredPoissonProcess` relative to
its natural filtration.

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

/-! ### Simplicity of `countPathMeasure` from microscopic multiple-jump bounds -/

/-- Stationary increment laws and `P(N h - N 0 ≥ 2) = o(h)` imply via equal-mesh subdivisions that
`countPathMeasure (N · ω)` has singleton mass at most one simultaneously at all positive times,
whenever sample paths are monotone and right-continuous on one event of full measure. Neither
independent increments nor coordinate measurability is assumed. -/
theorem ae_countPathMeasure_singleton_le_one_of_small_time [IsFiniteMeasure P]
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω))
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h : ℝ≥0 ↦ (h : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ≥0), countPathMeasure (N · ω) {t} ≤ 1 := by
  have hjump := ae_count_le_add_one_of_small_time (hreg.mono fun _ h ↦ h.1) hstat hsmall
  filter_upwards [hreg, hjump] with ω ⟨hf, hrc⟩ hj t ht
  exact (countPathMeasure_singleton_le_one_iff hf hrc ht).2 (hj t ht)

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
    ∀ᵐ ω ∂P, ∀ t, countPathMeasure (N · ω) {t} ≤ 1 := by
  have hjump := ae_count_le_add_one_of_small_time (hreg.mono fun _ h ↦ h.1) hstat hsmall
  filter_upwards [hreg, h0, hjump] with ω ⟨hf, hrc⟩ h0ω hj
  exact (forall_countPathMeasure_singleton_le_one_iff hf hrc).2 ⟨h0ω, hj⟩

/-! ### Recognizing temporal Poisson random measures reconstructed from count paths -/

/-- For a count process measurable at nonnegative rational times whose paths are monotone and
right-continuous on one event of full measure, `countPathMeasure (N · ω)` is a Poisson random
measure with locally finite intensity `Λ` (`Λ {0} = 0`) if and only if `N 0 = 0` almost surely and
`N` has independent Poisson increments with parameters `(Λ (Ioc s t)).toNNReal`. -/
theorem isPoissonRandomMeasure_countPathMeasure_iff_count_increments {Λ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure Λ] (hΛ : Λ {0} = 0)
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) Λ ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
        (poissonMeasure (Λ (Ioc s t)).toNNReal) P := by
  refine isPoissonRandomMeasure_iff_count_increments hΛ
    (measurable_countPathMeasure_of_nnrat hN) ?_
  filter_upwards [hreg] with ω ⟨hf, hrc⟩ t
  exact countPathMeasure_Iic hf hrc t

/-- Homogeneous specialization: for a count process measurable at nonnegative rational times whose
paths are monotone and right-continuous on one event of full measure, `countPathMeasure (N · ω)` is
a rate-`r` homogeneous Poisson random measure if and only if `N 0 = 0` almost surely and `N` has
independent rate-`r` Poisson increments. -/
theorem isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_count_increments {r : ℝ≥0}
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
        (poissonMeasure (r * (t - s))) P := by
  refine isPoissonRandomMeasure_smul_nnvolume_iff_count_increments
    (measurable_countPathMeasure_of_nnrat hN) ?_
  filter_upwards [hreg] with ω ⟨hf, hrc⟩ t
  exact countPathMeasure_Iic hf hrc t

/-- **Microscopic characterization of homogeneous temporal Poisson point processes (quotient
form).** For a natural-valued process measurable at nonnegative rational times whose paths are
monotone and right-continuous on one event of full measure, `countPathMeasure (N · ω)` is a
rate-`r` Poisson random measure on `ℝ≥0` if and only if `N 0 = 0` almost surely, `N` has
stationary independent increments, and `P(N h = 1) / h → r` and `P(N h ≥ 2) / h → 0` as `h ↓ 0`.
Both `r > 0` and `r = 0` are included. -/
theorem isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_stationary_small_time {r : ℝ≥0}
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0) := by
  rw [isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_count_increments hN hreg]
  have hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω := fun s t hst ↦
    hreg.mono fun _ h ↦ h.1 hst
  exact and_congr_right fun h0 ↦ and_congr_right fun hind ↦
    hind.hasLaw_sub_poissonMeasure_iff_stationary_small_time h0 hmono r

/-- **Microscopic characterization of homogeneous temporal Poisson point processes (`o(h)`
form).** For a natural-valued process measurable at nonnegative rational times whose paths are
monotone and right-continuous on one event of full measure, `countPathMeasure (N · ω)` is a
rate-`r` Poisson random measure on `ℝ≥0` if and only if `N 0 = 0` almost surely, `N` has
stationary independent increments, `P(N h = 1) - r * h = o(h)`, and `P(N h ≥ 2) = o(h)` as
`h ↓ 0`. -/
theorem isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_stationary_isLittleO {r : ℝ≥0}
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) := by
  rw [isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_count_increments hN hreg]
  have hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω := fun s t hst ↦
    hreg.mono fun _ h ↦ h.1 hst
  exact and_congr_right fun h0 ↦ and_congr_right fun hind ↦
    hind.hasLaw_sub_poissonMeasure_iff_stationary_isLittleO h0 hmono r

/-- **Microscopic characterization including almost-sure simplicity and local finiteness.**
For a natural-valued process measurable at nonnegative rational times whose paths are monotone and
right-continuous on one event of full measure, the microscopic conditions characterize when
`countPathMeasure (N · ω)` is a rate-`r` Poisson random measure whose realizations on one event of
probability one are locally finite, put zero mass at the origin, and are simple
(`∀ t, countPathMeasure (N · ω) {t} ≤ 1`). Simplicity in the sufficiency direction is obtained
directly from the equal-mesh subdivision bound
`ae_forall_countPathMeasure_singleton_le_one_of_small_time`. -/
theorem isPoissonRandomMeasure_and_ae_simple_countPathMeasure_iff_stationary_isLittleO {r : ℝ≥0}
    (hN : ∀ q : ℚ≥0, Measurable (N q))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    (IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ∧
      ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (countPathMeasure (N · ω)) ∧
        countPathMeasure (N · ω) {0} = 0 ∧
        ∀ t, countPathMeasure (N · ω) {t} ≤ 1) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) := by
  refine ⟨fun h ↦ (isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_stationary_isLittleO
    hN hreg).1 h.1, fun h ↦ ?_⟩
  have hprm :=
    (isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_stationary_isLittleO hN hreg).2 h
  refine ⟨hprm, ?_⟩
  let := hprm.isProbabilityMeasure
  rcases h with ⟨h0, _, hstat, _, h2⟩
  have hstat0 (s h : ℝ≥0) : IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P := by
    refine (hstat s h).trans (IdentDistrib.of_ae_eq (hstat s h).aemeasurable_snd ?_)
    filter_upwards [h0] with ω h0ω
    simp [h0ω]
  have h2' : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h : ℝ≥0 ↦ (h : ℝ)) := by
    refine h2.congr' (Eventually.of_forall fun h ↦ ?_) EventuallyEq.rfl
    refine measureReal_congr ?_
    filter_upwards [h0] with ω h0ω
    simp [h0ω]
  have hsimple := ae_forall_countPathMeasure_singleton_le_one_of_small_time hreg
    (h0.mono fun _ h0ω ↦ by omega) hstat0 h2'
  filter_upwards [hreg, h0, hsimple] with ω ⟨hf, hrc⟩ h0ω hs
  exact ⟨isLocallyFiniteMeasure_countPathMeasure hf,
    (countPathMeasure_singleton_zero_eq_zero_iff hf hrc).2 h0ω, hs⟩

/-- For a natural-valued process with measurable coordinates whose paths are monotone and
right-continuous on one event of full measure, `countPathMeasure (N · ω)` is a rate-`r`
homogeneous Poisson random measure on `ℝ≥0` if and only if `(N t ω : ℝ)` is a rate-`r` Poisson
process relative to its natural filtration. -/
theorem isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_isFilteredPoissonProcess_natural
    {r : ℝ≥0} (hN : ∀ t, Measurable (N t))
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IsPoissonRandomMeasure P (fun ω ↦ countPathMeasure (N · ω)) ((r : ℝ≥0∞) • nnvolume) ↔
      IsFilteredPoissonProcess
        (Filtration.natural (fun t ω ↦ (N t ω : ℝ))
          (fun t ↦ (Measurable.of_discrete.comp (hN t)).stronglyMeasurable))
        r (fun t ω ↦ (N t ω : ℝ)) P := by
  have hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω := fun s t hst ↦
    hreg.mono fun _ h ↦ h.1 hst
  rw [isPoissonRandomMeasure_countPathMeasure_smul_nnvolume_iff_count_increments
    (fun q ↦ hN q) hreg, isFilteredPoissonProcess_natural_cast_iff hN hmono]

end TauCeti.Probability
