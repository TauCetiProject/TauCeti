/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Patching compatible local processes

Continuous integral processes constructed on successively larger stochastic intervals must be
patched without losing adaptation to the original filtration. This file constructs a strongly
progressive, almost surely continuous process from strongly progressive continuous stages which
agree up to their respective lifetimes. The process agrees with every stage throughout its
lifetime, including its right endpoint, outside one common null set. It is unique up to
indistinguishability. A stopped-process form gives the identities needed to patch stopped
stochastic integrals.

The construction uses the native measurable `Filter.limUnder` selection, not a modification on
a future-measurable exceptional event. Thus neither completion nor right continuity of the
filtration is needed. Lifetimes need only tend almost surely to infinity: their monotonicity
and stopping-time property are unnecessary here. In particular one can use the lifetimes of a
native pre-localizing or localizing sequence.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology

namespace TauCeti

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {τ : ℕ → Ω → WithTop ι}
  {X Y : ι → Ω → E}

/-- Agreement on stochastic intervals whose lifetimes tend to infinity implies
indistinguishability. No measurability or path regularity of the processes is required. -/
theorem indist_of_ae_eq_before_lifetimes
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hXY : ∀ n, ∀ᵐ ω ∂P, ∀ t : ι, (t : WithTop ι) ≤ τ n ω → X t ω = Y t ω) :
    X ≡ᵐ[P] Y := by
  filter_upwards [hτ, ae_all_iff.2 hXY] with ω hτω hω t
  obtain ⟨n, hn⟩ := (hτω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
  exact hω n t hn.le

variable [MeasurableSpace ι] [TopologicalSpace E] [Nonempty E]
  [IsCompletelyMetrizableSpace E] {ℱ : Filtration ι mΩ} {U : ℕ → ι → Ω → E}

/-- Patch compatible strongly progressive continuous stages on lifetimes tending almost surely
to infinity. Agreement with all stages holds simultaneously in stage and time. Lifetimes need
not be monotone or stopping times, and path continuity is only an almost-sure hypothesis. -/
theorem exists_isStronglyProgressive_patch
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hU : ∀ n, IsStronglyProgressive ℱ (U n))
    (hcont : ∀ n, ∀ᵐ ω ∂P, Continuous (U n · ω))
    (hcompat : ∀ n m, n ≤ m → ∀ᵐ ω ∂P,
      ∀ t : ι, (t : WithTop ι) ≤ τ n ω → U m t ω = U n t ω) :
    ∃ X : ι → Ω → E, IsStronglyProgressive ℱ X ∧
      (∀ᵐ ω ∂P, Continuous (X · ω)) ∧
      (∀ᵐ ω ∂P, ∀ n (t : ι), (t : WithTop ι) ≤ τ n ω → X t ω = U n t ω) := by
  let X : ι → Ω → E := fun t ω ↦ limUnder atTop (fun n ↦ U n t ω)
  have hprog : IsStronglyProgressive ℱ X := by
    intro t
    let : MeasurableSpace (Iic t × Ω) := MeasurableSpace.prod inferInstance (ℱ t)
    exact StronglyMeasurable.limUnder (fun n ↦ hU n t)
  have hgood : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤) ∧
      (∀ n, Continuous (U n · ω)) ∧
      (∀ n m, n ≤ m → ∀ t : ι, (t : WithTop ι) ≤ τ n ω → U m t ω = U n t ω) := by
    have hc : ∀ᵐ ω ∂P, ∀ n m, n ≤ m →
        ∀ t : ι, (t : WithTop ι) ≤ τ n ω → U m t ω = U n t ω := by
      exact ae_all_iff.2 fun n ↦ ae_all_iff.2 fun m ↦ ae_all_iff.2 (hcompat n m)
    filter_upwards [hτ, ae_all_iff.2 hcont, hc] with ω hτω hcw hmw
    exact ⟨hτω, hcw, hmw⟩
  have hagree : ∀ᵐ ω ∂P, ∀ n (t : ι), (t : WithTop ι) ≤ τ n ω → X t ω = U n t ω := by
    filter_upwards [hgood] with ω hω n t ht
    exact (tendsto_const_nhds.congr' (eventually_atTop.2
      ⟨n, fun m hm ↦ (hω.2.2 n m hm t ht).symm⟩)).limUnder_eq
  refine ⟨X, hprog, ?_, hagree⟩
  filter_upwards [hgood, hagree] with ω hω ha
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := (hω.1.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
  have hneigh : ∀ᶠ s : ι in 𝓝 t, (s : WithTop ι) < τ n ω :=
    (WithTop.continuous_coe.tendsto t).eventually_lt_const hn
  refine (hω.2.1 n).continuousAt.congr_of_eventuallyEq ?_
  filter_upwards [hneigh] with s hs
  exact ha n s hs.le

/-- Patch compatible stopped stages and recover their full stopped-process identities.
Each stage is already stopped at its own lifetime. Compatibility is required only when the
stage index increases, and all equalities are simultaneous in time. -/
theorem exists_isStronglyProgressive_patch_stoppedProcess [Nonempty ι]
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hU : ∀ n, IsStronglyProgressive ℱ (U n))
    (hcont : ∀ n, ∀ᵐ ω ∂P, Continuous (U n · ω))
    (hcompat : ∀ n m, n ≤ m → stoppedProcess (U m) (τ n) ≡ᵐ[P] U n) :
    ∃ X : ι → Ω → E, IsStronglyProgressive ℱ X ∧
      (∀ᵐ ω ∂P, Continuous (X · ω)) ∧
      ∀ n, stoppedProcess X (τ n) ≡ᵐ[P] U n := by
  have hc n m (hnm : n ≤ m) : ∀ᵐ ω ∂P,
      ∀ t : ι, (t : WithTop ι) ≤ τ n ω → U m t ω = U n t ω := by
    filter_upwards [hcompat n m hnm] with ω hω t ht
    simpa only [stoppedProcess_eq_of_le ht] using hω t
  obtain ⟨X, hp, hcc, ha⟩ := exists_isStronglyProgressive_patch hτ hU hcont hc
  refine ⟨X, hp, hcc, fun n ↦ ?_⟩
  filter_upwards [ha, hcompat n n le_rfl] with ω hω hs t
  rw [← hs t]
  rcases le_total (t : WithTop ι) (τ n ω) with ht | ht
  · rw [stoppedProcess_eq_of_le ht, stoppedProcess_eq_of_le ht]
    exact hω n t ht
  · rw [stoppedProcess_eq_of_ge ht, stoppedProcess_eq_of_ge ht]
    exact hω n _ (WithTop.coe_untopD_le _ _)

end TauCeti
