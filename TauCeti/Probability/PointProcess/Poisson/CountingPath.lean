/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.CountingPath
public import TauCeti.Probability.PointProcess.Poisson.Temporal
public import TauCeti.Probability.PointProcess.Poisson.Thinning

/-!
# Poisson count processes as Poisson random measures

A natural-valued process `N` with measurable coordinates whose paths are almost surely
nondecreasing and right-continuous determines the measurable random measure
`ω ↦ countingPathMeasure (N · ω)`. This random measure is Poisson with a locally finite intensity
`Λ` without an atom at zero exactly when `N` starts at zero almost surely and has independent
increments with Poisson laws of parameters `Λ (s,t]`. For intensity `r` times Lebesgue measure,
the increment over `(s,t]` has parameter `r * (t - s)`: `N` is a rate-`r` Poisson process.

Through this identification the point-process operations apply to count processes:

* **Thinning.** Deleting each occurrence of a rate-`r` Poisson count process independently with
  probability `1 - p` (`HasIndepIncrements.exists_bernoulli_thinning_of_hasLaw_poissonMeasure`)
  gives two independent homogeneous Poisson random measures of rates `p * r` and `(1 - p) * r`,
  whose cumulative counts on `(0,t]` add up to `N t` simultaneously at all times almost surely.
  The randomization depends only on the path of `N`.
* **Superposition.** The sum of two independent Poisson count processes of rates `r₁` and `r₂`
  has independent increments with the Poisson laws of rate `r₁ + r₂`
  (`hasIndepIncrements_add_and_hasLaw_sub_poissonMeasure`).

Rate zero and the probabilities `p = 0, 1` are included. A rate-zero Poisson count process is
identically zero almost surely, by `isPoissonRandomMeasure_zero_iff_ae_count_eq_zero`; no
exponential waiting-time law is used.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.3 (superposition), Corollary 5.9 (thinning) and Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- Almost surely counting paths are recovered by the cumulative counts of their counting
measures, simultaneously at all times. -/
private theorem ae_forall_countingPathMeasure_Iic
    (hmono : ∀ᵐ ω ∂P, Monotone fun t ↦ N t ω)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous fun t ↦ N t ω) :
    ∀ᵐ ω ∂P, ∀ t, countingPathMeasure (fun t ↦ N t ω) (Iic t) = N t ω := by
  filter_upwards [hmono, hrc] with ω h₁ h₂ t using countingPathMeasure_Iic h₁ h₂ t

/-- A natural-valued process with measurable coordinates and almost surely nondecreasing
right-continuous paths is a Poisson count process with locally finite intensity `Λ`, without
mass at zero, exactly when the counting measures of its paths form a Poisson random measure of
intensity `Λ`. Atoms of `Λ` at positive times are allowed. -/
theorem isPoissonRandomMeasure_countingPathMeasure_iff {Λ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure Λ] (hΛ : Λ {0} = 0) (hm : ∀ t, Measurable (N t))
    (hmono : ∀ᵐ ω ∂P, Monotone fun t ↦ N t ω)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous fun t ↦ N t ω) :
    IsPoissonRandomMeasure P (fun ω ↦ countingPathMeasure fun t ↦ N t ω) Λ ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
        ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
          (poissonMeasure (Λ (Ioc s t)).toNNReal) P :=
  isPoissonRandomMeasure_iff_count_increments hΛ
    (measurable_countingPathMeasure.comp (measurable_pi_iff.2 hm))
    (ae_forall_countingPathMeasure_Iic hmono hrc)

/-- A natural-valued process with measurable coordinates and almost surely nondecreasing
right-continuous paths is a rate-`r` Poisson process exactly when the counting measures of its
paths form a homogeneous Poisson random measure of rate `r`. Rate zero is included. -/
theorem isPoissonRandomMeasure_countingPathMeasure_smul_nnvolume_iff
    (hm : ∀ t, Measurable (N t)) (hmono : ∀ᵐ ω ∂P, Monotone fun t ↦ N t ω)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous fun t ↦ N t ω) {r : ℝ≥0} :
    IsPoissonRandomMeasure P (fun ω ↦ countingPathMeasure fun t ↦ N t ω)
        ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
        ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P :=
  isPoissonRandomMeasure_smul_nnvolume_iff_count_increments
    (measurable_countingPathMeasure.comp (measurable_pi_iff.2 hm))
    (ae_forall_countingPathMeasure_Iic hmono hrc)

/-- **Superposition of Poisson count processes.** The sum of two independent Poisson processes
of rates `r₁` and `r₂`, each with measurable coordinates and almost surely nondecreasing
right-continuous paths, has independent increments with the Poisson laws of rate `r₁ + r₂`.
Independence is required of the entire paths. Zero rates are included. -/
theorem hasIndepIncrements_add_and_hasLaw_sub_poissonMeasure {N₁ N₂ : ℝ≥0 → Ω → ℕ}
    {r₁ r₂ : ℝ≥0} (hN₁ : HasIndepIncrements N₁ P) (hm₁ : ∀ t, Measurable (N₁ t))
    (h0₁ : ∀ᵐ ω ∂P, N₁ 0 ω = 0) (hmono₁ : ∀ᵐ ω ∂P, Monotone fun t ↦ N₁ t ω)
    (hrc₁ : ∀ᵐ ω ∂P, IsRightContinuous fun t ↦ N₁ t ω)
    (hlaw₁ : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N₁ t ω - N₁ s ω) (poissonMeasure (r₁ * (t - s))) P)
    (hN₂ : HasIndepIncrements N₂ P) (hm₂ : ∀ t, Measurable (N₂ t))
    (h0₂ : ∀ᵐ ω ∂P, N₂ 0 ω = 0) (hmono₂ : ∀ᵐ ω ∂P, Monotone fun t ↦ N₂ t ω)
    (hrc₂ : ∀ᵐ ω ∂P, IsRightContinuous fun t ↦ N₂ t ω)
    (hlaw₂ : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N₂ t ω - N₂ s ω) (poissonMeasure (r₂ * (t - s))) P)
    (hind : IndepFun (fun ω t ↦ N₁ t ω) (fun ω t ↦ N₂ t ω) P) :
    HasIndepIncrements (fun t ω ↦ N₁ t ω + N₂ t ω) P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ (N₁ t ω + N₂ t ω) - (N₁ s ω + N₂ s ω))
        (poissonMeasure ((r₁ + r₂) * (t - s))) P := by
  have hM₁ := (isPoissonRandomMeasure_countingPathMeasure_smul_nnvolume_iff hm₁ hmono₁ hrc₁).2
    ⟨h0₁, hN₁, hlaw₁⟩
  have hM₂ := (isPoissonRandomMeasure_countingPathMeasure_smul_nnvolume_iff hm₂ hmono₂ hrc₂).2
    ⟨h0₂, hN₂, hlaw₂⟩
  have hsum := isPoissonRandomMeasure_add hM₁ hM₂
    (hind.comp measurable_countingPathMeasure measurable_countingPathMeasure)
  rw [← add_smul, ← ENNReal.coe_add] at hsum
  have hcount : ∀ᵐ ω ∂P, ∀ t,
      (countingPathMeasure (fun t ↦ N₁ t ω) + countingPathMeasure fun t ↦ N₂ t ω) (Iic t) =
        ((N₁ t ω + N₂ t ω : ℕ) : ℝ≥0∞) := by
    filter_upwards [ae_forall_countingPathMeasure_Iic hmono₁ hrc₁,
      ae_forall_countingPathMeasure_Iic hmono₂ hrc₂] with ω h₁ h₂ t
    simp [h₁ t, h₂ t]
  obtain ⟨-, hind', hlaw'⟩ :=
    (isPoissonRandomMeasure_smul_nnvolume_iff_count_increments hsum.measurable hcount).1 hsum
  exact ⟨hind', hlaw'⟩

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- **Bernoulli thinning of a Poisson count process.** Let `N` be a rate-`r` Poisson process
with measurable coordinates and almost surely nondecreasing right-continuous paths. Some Markov
kernel `η`, acting on its paths, produces under `P ⊗ₘ η.comap (fun ω t ↦ N t ω) _` two
independent homogeneous Poisson random measures of rates `p * r` and `(1 - p) * r`, whose
cumulative counts on `(0,t]` add up to `N t` simultaneously at all times almost surely.

The cumulative counts of the two random measures are independent processes with independent
Poisson increments of rates `p * r` and `(1 - p) * r`, by `IndepFun.natFloor_toNNReal`,
`IsPoissonRandomMeasure.hasIndepIncrements_nat_count` and
`IsPoissonRandomMeasure.hasLaw_nat_count_sub_smul_nnvolume`. The probabilities `p = 0, 1` and
rate `r = 0` are included. -/
theorem HasIndepIncrements.exists_bernoulli_thinning_of_hasLaw_poissonMeasure
    (hN : HasIndepIncrements N P) (hm : ∀ t, Measurable (N t))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone fun t ↦ N t ω)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous fun t ↦ N t ω) (r : ℝ≥0)
    (hlaw : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P)
    (p : unitInterval) :
    ∃ η : Kernel (ℝ≥0 → ℕ) (Measure ℝ≥0 × Measure ℝ≥0), IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap (fun ω t ↦ N t ω) (measurable_pi_iff.2 hm))
        (fun z ↦ z.2.1) (((unitInterval.toNNReal p * r : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap (fun ω t ↦ N t ω) (measurable_pi_iff.2 hm))
        (fun z ↦ z.2.2) ((((1 - unitInterval.toNNReal p) * r : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2)
        (P ⊗ₘ η.comap (fun ω t ↦ N t ω) (measurable_pi_iff.2 hm)) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap (fun ω t ↦ N t ω) (measurable_pi_iff.2 hm)), ∀ t,
        ⌊(z.2.1 (Ioc 0 t)).toNNReal⌋₊ + ⌊(z.2.2 (Ioc 0 t)).toNNReal⌋₊ = N t z.1 := by
  have hM := (isPoissonRandomMeasure_countingPathMeasure_smul_nnvolume_iff hm hmono hrc).2
    ⟨h0, hN, hlaw⟩
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ := hM.exists_bernoulli_thinning_smul_nnvolume p
  -- Thin the counting measure of the path.
  let κ := η.comap countingPathMeasure measurable_countingPathMeasure
  have hκ : IsMarkovKernel κ := by
    have := hη
    infer_instance
  have hcomap : κ.comap (fun ω t ↦ N t ω) (measurable_pi_iff.2 hm) =
      η.comap (fun ω ↦ countingPathMeasure fun t ↦ N t ω) hM.measurable :=
    Kernel.ext fun ω ↦ by simp only [κ, Kernel.comap_apply]
  refine ⟨κ, hκ, ?_⟩
  rw [hcomap]
  refine ⟨h₁, h₂, hind, ?_⟩
  have hfin (a : ℝ≥0) (n : ℕ) : ((a : ℝ≥0∞) • nnvolume) (Ioc 0 (n : ℝ≥0)) < ∞ := by
    rw [smul_nnvolume_Ioc]
    exact ENNReal.coe_lt_top
  -- Transfer the almost-sure path properties of `N` to the extended sample space.
  have hpath : ∀ᵐ z ∂(P ⊗ₘ η.comap (fun ω ↦ countingPathMeasure fun t ↦ N t ω) hM.measurable),
      N 0 z.1 = 0 ∧ Monotone (fun t ↦ N t z.1) ∧ IsRightContinuous fun t ↦ N t z.1 := by
    have := hM.isProbabilityMeasure
    have := hη
    have hP : ∀ᵐ ω ∂P,
        N 0 ω = 0 ∧ Monotone (fun t ↦ N t ω) ∧ IsRightContinuous fun t ↦ N t ω := by
      filter_upwards [h0, hmono, hrc] with ω h₀ h₁ h₂ using ⟨h₀, h₁, h₂⟩
    rw [← Measure.fst_compProd P (η.comap _ hM.measurable), Measure.fst] at hP
    exact ae_of_ae_map measurable_fst.aemeasurable hP
  filter_upwards [h₁.ae_forall_nat_count_add_eq h₂ (hfin _) (hfin _) hadd, hpath]
    with z hz ⟨hz0, hzmono, hzrc⟩ t
  rw [hz t]
  simp [countingPathMeasure_Ioc hzmono hzrc, hz0]

end ProbabilityTheory
