/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Process.Adapted
public import TauCeti.Probability.Process.Filtration.AmbientNullAugmentation
import TauCeti.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Independence.Completion
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Independence.Process.HasIndepIncrements
import TauCeti.Probability.Process.Filtration.Natural

/-!
# Homogeneous Poisson processes relative to a filtration

`TauCeti.Probability.IsFilteredPoissonProcess ℱ α N P` says that the real process `N` is a
homogeneous Poisson process of rate `α` relative to the filtration `ℱ`: it starts at `0` almost
surely, it is adapted to `ℱ`, and for `s ≤ t` the increment `N t - N s` has the Poisson law of
parameter `α * (t - s)` and is independent of `ℱ s`. A Poisson marginal law alone says nothing
about the filtration; the independence clause is what makes stopping and martingale arguments
relative to `ℱ` possible. No path regularity is part of the definition: an arbitrary version of a
Poisson process need not have càdlàg paths.

The rate may be zero, in which case the process vanishes almost surely at every time
(`IsFilteredPoissonProcess.eval_ae_eq_zero`).

## Main declarations

* `TauCeti.Probability.IsFilteredPoissonProcess`: a Poisson process of rate `α` relative to a
  filtration.
* `IsFilteredPoissonProcess.hasLaw_eval`, `integral_eval`, `variance_eval`, `memLp_eval`: `N t`
  has the Poisson law of parameter `α * t`, hence every finite moment, mean `α * t` and variance
  `α * t`.
* `IsFilteredPoissonProcess.indepFun_sub_sub`, `hasIndepIncrements`: increments over disjoint
  intervals are independent.
* `IsFilteredPoissonProcess.of_le`, `natural`, `ambientNullAugmentation`: the property passes to
  every smaller filtration to which `N` is adapted, in particular to the natural filtration, and
  to the augmentation by ambient-measurable null sets.
* `IsFilteredPoissonProcess.indep_comap_shift`, `shift`: the future increment process
  `(N (s + u) - N s)_u` is independent of `ℱ s` and is a Poisson process of the same rate for
  its own natural filtration.
* `ProbabilityTheory.HasIndepIncrements.isFilteredPoissonProcess_natural`: conversely, a process
  with independent Poisson increments starting at `0` is a Poisson process relative to its
  natural filtration.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `N` is a **homogeneous Poisson process of rate `α` relative to the filtration `ℱ`** under
`P`: it starts at `0` almost surely, it is adapted to `ℱ`, and for `s ≤ t` the increment
`N t - N s` has the law of a Poisson variable of parameter `α * (t - s)` and is independent of
`ℱ s`. -/
structure IsFilteredPoissonProcess (ℱ : Filtration ℝ≥0 mΩ) (α : ℝ≥0) (N : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop where
  /-- `N t` is `ℱ t`-measurable. -/
  stronglyAdapted : StronglyAdapted ℱ N
  /-- The process starts at `0` almost surely. -/
  eval_zero_ae_eq_zero : ∀ᵐ ω ∂P, N 0 ω = 0
  /-- The increment `N t - N s` has the Poisson law of parameter `α * (t - s)`. -/
  hasLaw_sub ⦃s t : ℝ≥0⦄ : s ≤ t → HasLaw (N t - N s) Po(ℝ, α * (t - s)) P
  /-- The increment `N t - N s` is independent of `ℱ s`. -/
  indep_sub ⦃s t : ℝ≥0⦄ : s ≤ t → Indep (.comap (N t - N s) inferInstance) (ℱ s) P

namespace IsFilteredPoissonProcess

variable {ℱ : Filtration ℝ≥0 mΩ} {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- A Poisson process relative to `ℱ` is adapted to `ℱ`. -/
theorem adapted (h : IsFilteredPoissonProcess ℱ α N P) : Adapted ℱ N :=
  h.stronglyAdapted.adapted

/-- Each value of a Poisson process is measurable. -/
theorem measurable (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) : Measurable (N t) :=
  (h.adapted t).mono (ℱ.le t) le_rfl

/-- A Poisson process is defined on a probability space. -/
theorem isProbabilityMeasure (h : IsFilteredPoissonProcess ℱ α N P) : IsProbabilityMeasure P :=
  (h.hasLaw_sub (le_refl 0)).isProbabilityMeasure

/-- The value `N t` has the Poisson law of parameter `α * t`. -/
theorem hasLaw_eval (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    HasLaw (N t) Po(ℝ, α * t) P := by
  refine (tsub_zero t ▸ h.hasLaw_sub (zero_le : 0 ≤ t)).congr ?_
  filter_upwards [h.eval_zero_ae_eq_zero] with ω hω
  simp [hω]

/-- A Poisson process has finite moments of every finite order. -/
theorem memLp_eval (h : IsFilteredPoissonProcess ℱ α N P) (t p : ℝ≥0) :
    MemLp (N t) p P :=
  (h.hasLaw_eval t).memLp (memLp_id_map_cast_poissonMeasure _ p)

/-- The mean of `N t` is `α * t`. -/
theorem integral_eval (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    ∫ ω, N t ω ∂P = α * t := by
  rw [integral_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_eval t), NNReal.coe_mul]

/-- The variance of `N t` is `α * t`. -/
theorem variance_eval (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    variance (N t) P = α * t := by
  rw [variance_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_eval t), NNReal.coe_mul]

/-- The probability that no event has occurred by time `t` is `exp (-(α * t))`. -/
theorem measureReal_eval_eq_zero (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    P.real {ω | N t ω = 0} = exp (-(α * t)) := by
  rw [(h.hasLaw_eval t).measureReal_eq (measurableSet_singleton (0 : ℝ)),
    Set.ofPred_eq_eq_singleton, map_measureReal_apply (by fun_prop) (measurableSet_singleton 0)]
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' {0} = {0} := by
    ext n
    simp
  rw [hpre, poissonMeasure_real_singleton_zero, NNReal.coe_mul]

/-- A Poisson process of rate zero vanishes almost surely at every time. -/
theorem eval_ae_eq_zero (h : IsFilteredPoissonProcess ℱ 0 N P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, N t ω = 0 := by
  have hlaw := h.hasLaw_eval t
  rw [zero_mul, poissonMeasure_zero, Measure.map_dirac, Nat.cast_zero] at hlaw
  exact hlaw.ae_eq_of_dirac

/-- Increments of a Poisson process over intervals `(s, t]` and `(u, v]` with `t ≤ u` are
independent. Only `s ≤ u` and `t ≤ u` are used, so the first interval may also be reversed or
empty. -/
theorem indepFun_sub_sub (h : IsFilteredPoissonProcess ℱ α N P) {s t u v : ℝ≥0}
    (hsu : s ≤ u) (htu : t ≤ u) (huv : u ≤ v) :
    IndepFun (N t - N s) (N v - N u) P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left (h.indep_sub huv).symm
    ((h.adapted.measurable_le htu).sub (h.adapted.measurable_le hsu)).comap_le

/-- A Poisson process has independent increments. -/
theorem hasIndepIncrements (h : IsFilteredPoissonProcess ℱ α N P) : HasIndepIncrements N P :=
  have := h.isProbabilityMeasure
  h.adapted.hasIndepIncrements h.indep_sub

/-- A Poisson process relative to `ℱ` is a Poisson process relative to every smaller filtration
to which it is adapted. -/
theorem of_le (h : IsFilteredPoissonProcess ℱ α N P) {𝒢 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ ℱ)
    (hN : StronglyAdapted 𝒢 N) : IsFilteredPoissonProcess 𝒢 α N P where
  stronglyAdapted := hN
  eval_zero_ae_eq_zero := h.eval_zero_ae_eq_zero
  hasLaw_sub _ _ hst := h.hasLaw_sub hst
  indep_sub s _ hst := indep_of_indep_of_le_right (h.indep_sub hst) (h𝒢 s)

/-- A Poisson process relative to some filtration is a Poisson process relative to its natural
filtration. -/
theorem natural (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    IsFilteredPoissonProcess (Filtration.natural N hmeas) α N P :=
  h.of_le ((Filtration.natural_le_iff N hmeas ℱ).mpr h.adapted)
    (Filtration.stronglyAdapted_natural hmeas)

/-- Adjoining ambient-measurable null events to the filtration preserves the Poisson property,
without completing the ambient measurable space. -/
theorem ambientNullAugmentation (h : IsFilteredPoissonProcess ℱ α N P) :
    IsFilteredPoissonProcess (ℱ.ambientNullAugmentation P) α N P where
  stronglyAdapted t := (h.stronglyAdapted t).mono (ℱ.le_ambientNullAugmentation P t)
  eval_zero_ae_eq_zero := h.eval_zero_ae_eq_zero
  hasLaw_sub _ _ hst := h.hasLaw_sub hst
  indep_sub s t hst := by
    apply indep_of_indep_of_le_right (h.indep_sub hst).eventuallyMeasurableSpace_right
    rw [Filtration.ambientNullAugmentation_apply, Filtration.nullAugment_apply]
    exact inf_le_right

/-- Fixed-time almost-sure equality preserves the Poisson property, provided the replacement is
adapted to the same filtration. Adaptedness is not inferred from almost-sure equality on a raw
filtration. -/
theorem congr (h : IsFilteredPoissonProcess ℱ α N P) {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted ℱ M) (hNM : ∀ t, N t =ᵐ[P] M t) :
    IsFilteredPoissonProcess ℱ α M P where
  stronglyAdapted := hM
  eval_zero_ae_eq_zero := by
    filter_upwards [h.eval_zero_ae_eq_zero, hNM 0] with ω hω hω' using hω' ▸ hω
  hasLaw_sub s t hst := (h.hasLaw_sub hst).congr ((hNM t).sub (hNM s)).symm
  indep_sub s t hst := by
    have hi : @IndepFun Ω ℝ Ω mΩ inferInstance (ℱ s) (N t - N s) id P := by
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using h.indep_sub hst
    have hj := hi.congr ((hNM t).sub (hNM s)) (Filter.EventuallyEq.refl ..)
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hj

/-- The future increment process `(N (s + u) - N s)_u` of a Poisson process is independent of
`ℱ s`. -/
theorem indep_comap_shift (h : IsFilteredPoissonProcess ℱ α N P) (s : ℝ≥0) :
    Indep (.comap (fun ω u ↦ N (s + u) ω - N s ω) inferInstance) (ℱ s) P := by
  have := h.isProbabilityMeasure
  refine indep_of_indep_of_le_left (h.adapted.indep_comap_sub_Ici h.indep_sub s) ?_
  have hg : Measurable fun (z : Set.Ici s → ℝ) (u : ℝ≥0) ↦
      z ⟨s + u, Set.mem_Ici.mpr le_self_add⟩ := by
    fun_prop
  have hcomp : (fun ω u ↦ N (s + u) ω - N s ω) =
      (fun (z : Set.Ici s → ℝ) (u : ℝ≥0) ↦ z ⟨s + u, Set.mem_Ici.mpr le_self_add⟩) ∘
        fun ω (t : Set.Ici s) ↦ N t ω - N s ω :=
    rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

/-- The future increment process `(N (s + u) - N s)_u` of a Poisson process relative to `ℱ` is a
Poisson process of the same rate relative to its own natural filtration. -/
theorem shift (h : IsFilteredPoissonProcess ℱ α N P) (s : ℝ≥0)
    (hmeas : ∀ u, StronglyMeasurable fun ω ↦ N (s + u) ω - N s ω) :
    IsFilteredPoissonProcess (Filtration.natural (fun u ω ↦ N (s + u) ω - N s ω) hmeas) α
      (fun u ω ↦ N (s + u) ω - N s ω) P := by
  have hsub (u v : ℝ≥0) : ((fun ω ↦ N (s + v) ω - N s ω) - fun ω ↦ N (s + u) ω - N s ω) =
      N (s + v) - N (s + u) := by
    ext ω
    simp
  refine ⟨Filtration.stronglyAdapted_natural hmeas, ae_of_all _ fun ω ↦ by simp,
    fun u v huv ↦ ?_, fun u v huv ↦ ?_⟩
  · rw [hsub, ← add_tsub_add_eq_tsub_left s v u]
    exact h.hasLaw_sub (by gcongr)
  · rw [hsub]
    refine indep_of_indep_of_le_right (h.indep_sub (by gcongr : s + u ≤ s + v)) ?_
    -- The shifted history up to time `u` is known at time `s + u`.
    exact iSup₂_le fun w hwu ↦
      ((h.adapted.measurable_le (by gcongr : s + w ≤ s + u)).sub
        (h.adapted.measurable_le (le_self_add : s ≤ s + u))).comap_le

end IsFilteredPoissonProcess

end TauCeti.Probability

namespace ProbabilityTheory.HasIndepIncrements

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ}

/-- A measurable process with independent increments, starting at `0` almost surely, whose
increments `N t - N s` have the Poisson law of parameter `α * (t - s)` is a Poisson process of
rate `α` relative to its natural filtration. -/
theorem isFilteredPoissonProcess_natural (hN : HasIndepIncrements N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) (h0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hlaw : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → HasLaw (N t - N s) Po(ℝ, α * (t - s)) P) :
    IsFilteredPoissonProcess (Filtration.natural N hmeas) α N P where
  stronglyAdapted := Filtration.stronglyAdapted_natural hmeas
  eval_zero_ae_eq_zero := h0
  hasLaw_sub := hlaw
  indep_sub s t hst := by
    rw [Filtration.natural_eq_comap]
    -- The history theorem is stated at `⊥`, which is `0` in `ℝ≥0` by definition.
    exact ((IndepFun_iff_Indep _ _ _).mp
      (hN.indepFun_past_sub (fun t ↦ (hmeas t).measurable) h0 hst)).symm

end ProbabilityTheory.HasIndepIncrements
