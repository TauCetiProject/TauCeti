/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Characterization
public import TauCeti.Probability.Process.Poisson.Simplicity
public import TauCeti.Probability.Process.Poisson.Filtered
public import TauCeti.Probability.Independence.Process.HasIndepIncrements
import TauCeti.Probability.Independence.Filtration

/-!
# The microscopic characterization of Poisson counts

For a natural-valued process starting at zero and almost surely nondecreasing at each fixed
pair of times,
independent increments have the rate-`r` Poisson laws exactly when the increments are
stationary and the one- and multiple-occurrence probabilities satisfy

```text
P(N h = 1) / h → r,       P(N h ≥ 2) / h → 0       as h ↓ 0,
```

or equivalently `P(N h = 1) - r * h = o(h)` and `P(N h ≥ 2) = o(h)` on `𝓝[>] 0`.

This connects the scalar convolution-semigroup characterization with Mathlib's
`HasIndepIncrements`, rather than assuming independence from the current count separately, and
characterizes when the real cast of `N` is an `IsFilteredPoissonProcess` relative to a
filtration `ℱ` or relative to its natural filtration.
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

/-- Landau `=o[𝓝[>] 0]` form of the microscopic characterization of Poisson counts. -/
theorem HasIndepIncrements.hasLaw_sub_poissonMeasure_iff_stationary_isLittleO
    (hN : HasIndepIncrements N P)
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω) (r : ℝ≥0) :
    (∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P) ↔
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) := by
  have h1_iff :
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
          (fun h : ℝ≥0 ↦ (h : ℝ)) ↔
        Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)) := by
    have hz : ∀ᶠ h : ℝ≥0 in 𝓝[>] 0,
        (h : ℝ) = 0 → P.real {ω | N h ω = 1} - (r : ℝ) * h = 0 := by
      filter_upwards [self_mem_nhdsWithin] with h hh hzero
      exact absurd hzero (NNReal.coe_pos.mpr hh).ne'
    rw [isLittleO_iff_tendsto' hz]
    have hcongr : (fun h : ℝ≥0 ↦ (P.real {ω | N h ω = 1} - (r : ℝ) * h) / (h : ℝ)) =ᶠ[𝓝[>] 0]
        fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h - r := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have : (h : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hh).ne'
      field_simp
    rw [tendsto_congr' hcongr]
    exact ⟨fun h ↦ by simpa using h.add_const (r : ℝ),
      fun h ↦ by simpa using h.sub_const (r : ℝ)⟩
  have h2_iff :
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) ↔
        Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h) (𝓝[>] 0) (𝓝 0) := by
    refine isLittleO_iff_tendsto' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh hzero
    exact absurd hzero (NNReal.coe_pos.mpr hh).ne'
  rw [hN.hasLaw_sub_poissonMeasure_iff_stationary_small_time h0 hmono r, h1_iff, h2_iff]

end ProbabilityTheory

namespace TauCeti.Probability

section Simplicity

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

end Simplicity

section Filtered

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- For a pairwise almost surely nondecreasing natural-valued process `N`, its real cast is a
rate-`r` Poisson process relative to `ℱ` if and only if `N` is adapted to `ℱ`, starts at zero
almost surely, and has `ℱ`-independent `poissonMeasure (r * (t - s))` increments. -/
theorem isFilteredPoissonProcess_cast_iff
    (ℱ : Filtration ℝ≥0 mΩ) {r : ℝ≥0}
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω) :
    IsFilteredPoissonProcess ℱ r (fun t ω ↦ (N t ω : ℝ)) P ↔
      Adapted ℱ N ∧ (∀ᵐ ω ∂P, N 0 ω = 0) ∧
      (∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P) ∧
      ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
        Indep (.comap (fun ω ↦ N t ω - N s ω) inferInstance) (ℱ s) P := by
  have hemb : MeasurableEmbedding (Nat.cast : ℕ → ℝ) := .natCast
  have hcomap (X : Ω → ℕ) :
      MeasurableSpace.comap (fun ω ↦ (X ω : ℝ)) inferInstance =
        MeasurableSpace.comap X inferInstance := by
    change MeasurableSpace.comap ((Nat.cast : ℕ → ℝ) ∘ X) inferInstance = _
    rw [← MeasurableSpace.comap_comp, hemb.comap_eq]
  have hlaw_iff {X : Ω → ℕ} {c : ℝ≥0} :
      HasLaw (fun ω ↦ (X ω : ℝ)) Po(ℝ, c) P ↔ HasLaw X (poissonMeasure c) P := by
    refine ⟨fun h ↦ ?_, fun h ↦ (hasLaw_map Measurable.of_discrete.aemeasurable).fun_comp h⟩
    have hx : AEMeasurable X P := hemb.aemeasurable_comp_iff.mp h.aemeasurable
    refine ⟨hx, hemb.map_injective ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable Measurable.of_discrete.aemeasurable hx]
    exact h.map_eq
  have hind_iff {s t : ℝ≥0} (hst : s ≤ t) :
      Indep (.comap ((fun ω ↦ (N t ω : ℝ)) - fun ω ↦ (N s ω : ℝ)) inferInstance) (ℱ s) P ↔
        Indep (.comap (fun ω ↦ N t ω - N s ω) inferInstance) (ℱ s) P := by
    have hae : ((fun ω ↦ (N t ω : ℝ)) - fun ω ↦ (N s ω : ℝ)) =ᵐ[P]
        fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ) := by
      filter_upwards [hmono s t hst] with ω hω
      simp [Nat.cast_sub hω]
    rw [← hcomap (fun ω ↦ N t ω - N s ω)]
    constructor
    · intro h
      have hi : @IndepFun Ω ℝ Ω mΩ inferInstance (ℱ s)
          ((fun ω ↦ (N t ω : ℝ)) - fun ω ↦ (N s ω : ℝ)) id P := by
        simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using h
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using
        hi.congr hae EventuallyEq.rfl
    · intro h
      have hi : @IndepFun Ω ℝ Ω mΩ inferInstance (ℱ s)
          (fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ)) id P := by
        simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using h
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using
        hi.congr hae.symm EventuallyEq.rfl
  constructor
  · intro h
    refine ⟨fun t ↦ hemb.measurable_comp_iff.mp (h.adapted t),
      h.eval_zero_ae_eq_zero.mono fun _ hω ↦ Nat.cast_eq_zero.1 hω, fun s t hst ↦ ?_,
      fun s t hst ↦ (hind_iff hst).1 (h.indep_sub hst)⟩
    have hae : (fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ)) =ᵐ[P]
        ((fun ω ↦ (N t ω : ℝ)) - fun ω ↦ (N s ω : ℝ)) := by
      filter_upwards [hmono s t hst] with ω hω
      simp [Nat.cast_sub hω]
    exact hlaw_iff.1 ((h.hasLaw_sub hst).congr hae)
  · rintro ⟨hadapt, h0, hlaw, hind⟩
    refine ⟨fun t ↦ (Measurable.of_discrete.comp (hadapt t)).stronglyMeasurable,
      h0.mono fun _ hω ↦ by simp [hω], fun s t hst ↦ ?_,
      fun s t hst ↦ (hind_iff hst).2 (hind hst)⟩
    have hae : ((fun ω ↦ (N t ω : ℝ)) - fun ω ↦ (N s ω : ℝ)) =ᵐ[P]
        fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ) := by
      filter_upwards [hmono s t hst] with ω hω
      simp [Nat.cast_sub hω]
    exact (hlaw_iff.2 (hlaw s t hst)).congr hae

/-- **Microscopic characterization of a filtered Poisson count process.** On a probability space,
a pairwise almost surely nondecreasing natural-valued process `N` is a rate-`r` Poisson process
relative to `ℱ` (after casting to `ℝ`) if and only if it is adapted to `ℱ`, starts at zero
almost surely, has `ℱ`-independent stationary increments, and satisfies
`P(N h = 1) - r * h = o(h)` and `P(N h ≥ 2) = o(h)` as `h ↓ 0`. -/
theorem isFilteredPoissonProcess_cast_iff_stationary_isLittleO [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) {r : ℝ≥0}
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω) :
    IsFilteredPoissonProcess ℱ r (fun t ω ↦ (N t ω : ℝ)) P ↔
      Adapted ℱ N ∧ (∀ᵐ ω ∂P, N 0 ω = 0) ∧
      (∀ ⦃s t : ℝ≥0⦄, s ≤ t →
        Indep (.comap (fun ω ↦ N t ω - N s ω) inferInstance) (ℱ s) P) ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) := by
  rw [isFilteredPoissonProcess_cast_iff ℱ hmono]
  constructor
  · rintro ⟨hadapt, h0, hlaw, hind_sub⟩
    have hind : HasIndepIncrements N P := hadapt.hasIndepIncrements hind_sub
    obtain ⟨hstat, h1, h2⟩ :=
      (hind.hasLaw_sub_poissonMeasure_iff_stationary_isLittleO h0 hmono r).1 hlaw
    exact ⟨hadapt, h0, hind_sub, hstat, h1, h2⟩
  · rintro ⟨hadapt, h0, hind_sub, hstat, h1, h2⟩
    have hind : HasIndepIncrements N P := hadapt.hasIndepIncrements hind_sub
    exact ⟨hadapt, h0,
      (hind.hasLaw_sub_poissonMeasure_iff_stationary_isLittleO h0 hmono r).2 ⟨hstat, h1, h2⟩,
      hind_sub⟩

/-- For a coordinatewise measurable, pairwise almost surely nondecreasing natural-valued process
`N`, its real cast is a rate-`r` Poisson process relative to its natural filtration if and only if
`N 0 = 0` almost surely and `N` has independent `poissonMeasure (r * (t - s))` increments. -/
theorem isFilteredPoissonProcess_natural_cast_iff {r : ℝ≥0}
    (hN : ∀ t, Measurable (N t))
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω) :
    IsFilteredPoissonProcess
        (Filtration.natural (fun t ω ↦ (N t ω : ℝ))
          (fun t ↦ (Measurable.of_discrete.comp (hN t)).stronglyMeasurable))
        r (fun t ω ↦ (N t ω : ℝ)) P ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P := by
  let hmeas : ∀ t, StronglyMeasurable (fun ω ↦ (N t ω : ℝ)) :=
    fun t ↦ (Measurable.of_discrete.comp (hN t)).stronglyMeasurable
  constructor
  · intro h
    let := h.isProbabilityMeasure
    obtain ⟨hadapt, h0, hlaw, hind_sub⟩ :=
      (isFilteredPoissonProcess_cast_iff (Filtration.natural _ hmeas) hmono).1 h
    exact ⟨h0, hadapt.hasIndepIncrements hind_sub, hlaw⟩
  · rintro ⟨h0, hind, hlaw⟩
    let := hind.isProbabilityMeasure
    have hind_real : HasIndepIncrements (fun t ω ↦ (N t ω : ℝ)) P := by
      intro n t ht
      have hcast := (hind n t ht).comp (fun _ ↦ (Nat.cast : ℕ → ℝ))
        (fun _ ↦ Measurable.of_discrete)
      refine hcast.congr fun i ↦ ?_
      filter_upwards [hmono (t i.castSucc) (t i.succ) (ht i.castSucc_le_succ)] with ω hω
      simp [Nat.cast_sub hω]
    refine hind_real.isFilteredPoissonProcess_natural hmeas
      (h0.mono fun _ hω ↦ by simp [hω]) fun s t hst ↦ ?_
    have hae : ((fun ω ↦ (N t ω : ℝ)) - fun ω ↦ (N s ω : ℝ)) =ᵐ[P]
        fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ) := by
      filter_upwards [hmono s t hst] with ω hω
      simp [Nat.cast_sub hω]
    exact ((hasLaw_map Measurable.of_discrete.aemeasurable).fun_comp (hlaw s t hst)).congr hae

/-- **Microscopic characterization relative to the natural filtration.** For a coordinatewise
measurable, pairwise almost surely nondecreasing natural-valued process `N`, its real cast is a
rate-`r` Poisson process relative to its natural filtration if and only if `N 0 = 0` almost
surely, `N` has stationary independent increments, and the `o(h)` microscopic limits hold. -/
theorem isFilteredPoissonProcess_natural_cast_iff_stationary_isLittleO {r : ℝ≥0}
    (hN : ∀ t, Measurable (N t))
    (hmono : ∀ s t, s ≤ t → ∀ᵐ ω ∂P, N s ω ≤ N t ω) :
    IsFilteredPoissonProcess
        (Filtration.natural (fun t ω ↦ (N t ω : ℝ))
          (fun t ↦ (Measurable.of_discrete.comp (hN t)).stronglyMeasurable))
        r (fun t ω ↦ (N t ω : ℝ)) P ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      (∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} - (r : ℝ) * h) =o[𝓝[>] 0]
        (fun h : ℝ≥0 ↦ (h : ℝ)) ∧
      (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω}) =o[𝓝[>] 0] (fun h : ℝ≥0 ↦ (h : ℝ)) := by
  rw [isFilteredPoissonProcess_natural_cast_iff hN hmono]
  exact and_congr_right fun h0 ↦ and_congr_right fun hind ↦
    hind.hasLaw_sub_poissonMeasure_iff_stationary_isLittleO h0 hmono r

end Filtered

end TauCeti.Probability
