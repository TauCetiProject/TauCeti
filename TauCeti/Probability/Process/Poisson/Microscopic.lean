/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Characterization
public import TauCeti.Probability.Process.Poisson.Simplicity
public import TauCeti.Probability.Independence.Process.HasIndepIncrements

/-!
# The microscopic characterization of Poisson counts

For a natural-valued process starting at zero and almost surely nondecreasing at each fixed
pair of times,
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
continuity. The increment-law characterization needs only pairwise almost-sure monotonicity;
the simplicity conclusion assumes monotonicity on one common event of full measure.
Natural-valued nondecreasing paths are bounded on every bounded time interval.
Rate zero is included, without invoking an exponential waiting-time law at zero rate.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025,
  §9.5, microscopic characterization of the Poisson process.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Topology Asymptotics
open scoped NNReal

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- Stationary independent increments with the microscopic one- and multiple-occurrence
limits have rate-`r` Poisson laws on every interval. Only pairwise almost-sure monotonicity
is assumed; no right continuity or moment hypothesis is needed. -/
theorem HasIndepIncrements.hasLaw_sub_poissonMeasure_of_small_time
    (hN : HasIndepIncrements N P)
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω)
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
  have hlaw := hasLaw_poissonMeasure_of_small_time h0 hmono hind hstat r h1 h2 (t - s)
  have hd := hstat s (t - s)
  rw [add_tsub_cancel_of_le hst] at hd
  exact hd.symm.hasLaw hlaw

/-- **The microscopic characterization of Poisson counts.** For a count process starting at
zero with independent increments and pairwise almost-sure monotonicity, all increments have
rate-`r` Poisson laws if and only if they are stationary and satisfy the one- and
multiple-occurrence limits at zero. The rate may be zero. -/
theorem HasIndepIncrements.hasLaw_sub_poissonMeasure_iff_stationary_small_time
    (hN : HasIndepIncrements N P)
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω) (r : ℝ≥0) :
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
    exact ⟨identDistrib_sub_of_hasLaw_poissonMeasure hlaw hmarg,
      tendsto_small_time_of_hasLaw_poissonMeasure r hmarg⟩
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
  have hsmall := (tendsto_small_time_of_hasLaw_poissonMeasure (N := fun t ω ↦ N t ω - N 0 ω)
    r hmarg).2
  apply ae_count_le_add_one_of_small_time hmono
  · exact identDistrib_sub_of_hasLaw_poissonMeasure hlaw hmarg
  · exact (isLittleO_iff_tendsto' (Eventually.of_forall fun h hz ↦ by
      have : h = 0 := NNReal.coe_eq_zero.mp hz
      simp [this])).2 hsmall

end TauCeti.Probability
