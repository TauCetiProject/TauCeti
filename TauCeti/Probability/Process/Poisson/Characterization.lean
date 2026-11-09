/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Characterization
public import TauCeti.Probability.Distributions.Poisson.SmallRate
public import Mathlib.Probability.Independence.Integration

/-!
# Poisson marginals from microscopic increment probabilities

For a process almost surely nondecreasing at each fixed pair of times, stationary increments
independent of the current count give a convolution semigroup of probability laws on `ℕ`. Applying
`eq_poissonMeasure_of_small_time`, the microscopic conditions determine every marginal law,
without a canonical sample space, moment assumptions, or sample-path continuity. This result
does not by itself assert independence of arbitrary collections of increments or simplicity
of paths; those need the corresponding process hypotheses.

Conversely, Poisson marginals give the microscopic limits, and Poisson increment laws give
stationarity when compared with the corresponding marginal laws.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, Chapter 6,
  microscopic characterization of the Poisson process.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- A natural-valued process starting at zero and almost surely nondecreasing at each fixed
pair of times has Poisson marginals if its increments are stationary and independent of the
current count and satisfy the microscopic one- and multiple-occurrence limits. Full independence
of all increments and a common full-measure event of monotonicity are not needed for this marginal
conclusion. -/
theorem hasLaw_poissonMeasure_of_small_time {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℝ≥0 → Ω → ℕ}
    (h0 : N 0 =ᵐ[P] fun _ ↦ 0)
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω)
    (hind : ∀ s t, IndepFun (N s) (fun ω ↦ N (s + t) ω - N s ω) P)
    (hstat : ∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P)
    (r : ℝ≥0)
    (h1 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h)
      (𝓝[>] 0) (𝓝 (r : ℝ)))
    (h2 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h)
      (𝓝[>] 0) (𝓝 0)) (t : ℝ≥0) :
    HasLaw (N t) (poissonMeasure (r * t)) P := by
  have hN (s : ℝ≥0) : AEMeasurable (N s) P := (hstat 0 s).aemeasurable_snd
  have (s : ℝ≥0) : IsProbabilityMeasure (P.map (N s)) :=
    (Measure.isProbabilityMeasure_map_iff (hN s)).mpr inferInstance
  have hzero : P.map (N 0) = Measure.dirac 0 := by
    rw [Measure.map_congr h0]
    simp
  have hadd (s u : ℝ≥0) : P.map (N (s + u)) = P.map (N s) ∗ P.map (N u) := by
    have hae : N s + (fun ω ↦ N (s + u) ω - N s ω) =ᵐ[P] N (s + u) := by
      filter_upwards [hmono s (s + u) (le_add_right le_rfl)] with ω hω
      exact Nat.add_sub_of_le hω
    calc
      P.map (N (s + u)) = P.map (N s + (fun ω ↦ N (s + u) ω - N s ω)) :=
        Measure.map_congr hae.symm
      _ = P.map (N s) ∗ P.map (fun ω ↦ N (s + u) ω - N s ω) :=
        (hind s u).map_add_eq_map_conv_map₀ (hN s) (hstat s u).aemeasurable_fst
      _ = P.map (N s) ∗ P.map (N u) := by rw [(hstat s u).map_eq]
  have hlaw := eq_poissonMeasure_of_small_time (fun s ↦ P.map (N s)) r hzero hadd
    (by simpa only [map_measureReal_apply_of_aemeasurable (hN _) (measurableSet_singleton 1),
      Set.preimage, Set.mem_singleton_iff] using h1)
    (by simpa only [map_measureReal_apply_of_aemeasurable (hN _) measurableSet_Ici,
      Set.preimage, Set.mem_Ici] using h2) t
  exact ⟨hN t, hlaw⟩

/-- Poisson marginals imply the microscopic one- and multiple-occurrence limits at zero,
including at rate zero. No independence or path regularity is required. -/
theorem tendsto_small_time_of_hasLaw_poissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} (r : ℝ≥0)
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
    have hh' : 0 < (h : ℝ) := NNReal.coe_pos.mpr hh
    rw [(hlaw h).measureReal_eq (p := fun n ↦ n = 1) (.of_discrete)]
    simp only [Function.comp_apply, NNReal.coe_mul, Set.ofPred_eq_eq_singleton]
    field_simp
    ring
  · simpa only [Function.comp_apply,
      (hlaw _).measureReal_eq (p := fun n ↦ 2 ≤ n) (.of_discrete), Set.Ici_def] using h2

/-- Poisson increment laws identify each shifted increment with any marginal having the
corresponding Poisson law. In particular, this gives stationarity without independence. -/
theorem identDistrib_sub_of_hasLaw_poissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N M : ℝ≥0 → Ω → ℕ} {r : ℝ≥0}
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (r * (t - s))) P)
    (hmarg : ∀ t, HasLaw (M t) (poissonMeasure (r * t)) P) (s t : ℝ≥0) :
    IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (M t) P P := by
  have h := hlaw s (s + t) le_self_add
  rw [add_tsub_cancel_left] at h
  exact h.identDistrib (hmarg t)

end TauCeti.Probability
