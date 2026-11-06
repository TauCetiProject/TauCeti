/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Characterization
public import TauCeti.Probability.Process.Poisson.Simplicity
public import TauCeti.Probability.Distributions.Poisson.SmallRate
public import TauCeti.Probability.Independence.Process.HasIndepIncrements

/-!
# The microscopic characterization of Poisson counts

For a measurable, almost surely nondecreasing natural-valued process starting at zero,
independent increments have the rate-`r` Poisson laws exactly when the increments are
stationary and the one- and multiple-occurrence probabilities satisfy

```text
P(N h = 1) / h → r,       P(N h ≥ 2) / h → 0       as h ↓ 0.
```

This connects the scalar convolution-semigroup characterization with Mathlib's
`HasIndepIncrements`, rather than assuming independence from the current count separately.
It also proves simplicity simultaneously at every positive time: almost surely, for each
`t > 0` there is an `s < t` with `N t ≤ N s + 1`. For nondecreasing paths this excludes a
jump from the left of size two or more.

The assertions apply in particular to right-continuous count processes, but the increment-law
characterization and the no-multiple-jumps conclusion do not themselves require right
continuity. Monotonicity is imposed on one common event of full measure, not just separately
for each pair of times. Natural-valued paths are bounded on every bounded time interval.
Rate zero is included, without invoking an exponential waiting-time law at zero rate.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025,
  §9.5, microscopic characterization of the Poisson process.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Topology Asymptotics
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- The converse microscopic estimates, obtained from the scalar small-rate asymptotics.
This helper is used to prove both the characterization and its simplicity consequence. -/
private theorem small_time_of_hasLaw_poissonMeasure (r : ℝ≥0)
    (hlaw : ∀ t, HasLaw (N t) (poissonMeasure (r * t)) P) :
    Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0) := by
  have hrate : Tendsto (fun h : ℝ≥0 ↦ r * h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ≥0)))).const_mul r
  have hO : (fun h : ℝ≥0 ↦ ((r * h : ℝ≥0) : ℝ)) =O[𝓝[>] 0] (fun h ↦ (h : ℝ)) := by
    simpa using isBigO_const_mul_self (r : ℝ) (fun h : ℝ≥0 ↦ (h : ℝ)) (𝓝[>] 0)
  have h1 := ((isLittleO_poissonMeasure_real_singleton_one_sub.comp_tendsto hrate).trans_isBigO
    hO).tendsto_div_nhds_zero
  have h2 := ((isLittleO_poissonMeasure_real_Ici_two.comp_tendsto hrate).trans_isBigO
    hO).tendsto_div_nhds_zero
  constructor
  · have hlim := h1.add_const (r : ℝ)
    simp only [zero_add] at hlim
    apply hlim.congr' _
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < (h : ℝ) := hh
    rw [(hlaw h).measureReal_eq (p := fun n ↦ n = 1) (.of_discrete)]
    simp only [Function.comp_apply, NNReal.coe_mul, ofPred_eq_eq_singleton]
    field_simp
    ring
  · simpa only [Function.comp_apply,
      (hlaw _).measureReal_eq (p := fun n ↦ 2 ≤ n) (.of_discrete), Ici_def] using h2

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- Stationary independent increments with the microscopic one- and multiple-occurrence
limits have rate-`r` Poisson laws on every interval. Path monotonicity is assumed on a common
full-measure event; no right continuity or moment hypothesis is needed. -/
theorem HasIndepIncrements.hasLaw_sub_poissonMeasure_of_small_time
    (hN : HasIndepIncrements N P)
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω))
    (hstat : ∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P)
    (r : ℝ≥0)
    (h1 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)))
    (h2 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0))
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P := by
  have := hN.isProbabilityMeasure
  have hind (s t : ℝ≥0) : IndepFun (N s) (fun ω ↦ N (s + t) ω - N s ω) P := by
    refine (hN.indepFun_sub_sub (r := 0) zero_le le_self_add).congr ?_ .rfl
    filter_upwards [h0] with ω hω using by simp [hω]
  have hlaw := hasLaw_poissonMeasure_of_small_time h0
    (fun s t hst ↦ hmono.mono fun _ hω ↦ hω hst) hind hstat r h1 h2 (t - s)
  have hd := hstat s (t - s)
  rw [add_tsub_cancel_of_le hst] at hd
  exact ⟨hd.aemeasurable_fst, hd.map_eq.trans hlaw.map_eq⟩

/-- **The microscopic characterization of Poisson counts.** For a measurable nondecreasing
count process starting at zero with independent increments, all increments have the rate-`r`
Poisson laws if and only if they are stationary and satisfy the one- and multiple-occurrence
limits at zero. The rate may be zero. -/
theorem HasIndepIncrements.hasLaw_sub_poissonMeasure_iff_stationary_small_time
    (hN : HasIndepIncrements N P)
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω)) (r : ℝ≥0) :
    (∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P) ↔
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)) ∧
      Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · intro hlaw
    have hmarg (t : ℝ≥0) : HasLaw (N t) (poissonMeasure (r * t)) P := by
      have h := hlaw 0 t zero_le
      simp only [tsub_zero] at h
      exact h.congr (h0.mono fun ω hω ↦ by simp [hω])
    refine ⟨?_, small_time_of_hasLaw_poissonMeasure r hmarg⟩
    intro s t
    have h := hlaw s (s + t) le_self_add
    rw [add_tsub_cancel_left] at h
    exact ⟨h.aemeasurable, (hmarg t).aemeasurable, h.map_eq.trans (hmarg t).map_eq.symm⟩
  · rintro ⟨hstat, h1, h2⟩ s t hst
    exact hN.hasLaw_sub_poissonMeasure_of_small_time h0 hmono hstat r h1 h2 hst

end ProbabilityTheory

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- Poisson increment laws exclude multiple jumps simultaneously at every positive time.
For a nondecreasing path, the displayed inequality bounds its jump from the left by one.
Independence and right continuity are not required, and the initial count is unrestricted. -/
theorem ae_count_le_add_one_of_hasLaw_sub_poissonMeasure
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω)) (r : ℝ≥0)
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (r * (t - s))) P) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ≥0), ∃ s < t, N t ω ≤ N s ω + 1 := by
  have := (hlaw 0 0 le_rfl).isProbabilityMeasure
  have hmarg (t : ℝ≥0) : HasLaw (fun ω ↦ N t ω - N 0 ω) (poissonMeasure (r * t)) P := by
    simpa only [tsub_zero] using hlaw 0 t zero_le
  have hsmall := (small_time_of_hasLaw_poissonMeasure (N := fun t ω ↦ N t ω - N 0 ω)
    r hmarg).2
  apply ae_count_le_add_one_of_small_time hmono
  · intro s t
    have h := hlaw s (s + t) le_self_add
    rw [add_tsub_cancel_left] at h
    exact ⟨h.aemeasurable, (hmarg t).aemeasurable, h.map_eq.trans (hmarg t).map_eq.symm⟩
  · exact (isLittleO_iff_tendsto' (Eventually.of_forall fun h hz ↦ by
      have : h = 0 := NNReal.coe_eq_zero.mp hz
      simp [this])).2 hsmall

end TauCeti.Probability
