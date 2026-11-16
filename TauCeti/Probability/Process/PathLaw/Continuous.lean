/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ContinuousMap

/-!
# Realizing continuous processes on path space

Let `T` be second-countable and locally compact, and let `E` be second-countable and regular
with its Borel measurable structure. A process with a.e.-measurable coordinates and
a.e.-continuous paths has a measurable realization in `C(T, E)`. If its initial value is
almost everywhere `x₀`, it also has a realization in `BasedMap T E t₀ x₀`, the subtype of
continuous maps taking `t₀` to `x₀`. Each realization agrees with the process at every time
outside one common null set, even when the sample space is incomplete. For a finite source
measure, there exists exactly one measure on the corresponding path space with the
prescribed finite-dimensional laws.

Taking `T = ℝ≥0`, or a compact time interval, gives continuous-path laws in the compact-open
(or uniform, on a compact interval) topology. No Gaussian or independent-increment hypothesis
is made: this construction alone does not assert that the resulting law is Wiener measure.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 2, §4.A (Metric and Borelian Structure of C[0, ∞)).
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {T E Ω : Type*} [TopologicalSpace T] [SecondCountableTopology T]
  [LocallyCompactSpace T] [TopologicalSpace E] [SecondCountableTopology E]
  [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] {μ : Measure Ω} {X : T → Ω → E} {t₀ : T} {x₀ : E}

/-- A process with a.e.-measurable coordinates and a.e.-continuous paths admits a measurable
continuous-path realization agreeing with it at all times outside one common null set.
No completion of the sample space or measurability of the continuity event is assumed. -/
theorem exists_measurable_continuousMap_ae_eq
    (hX : ∀ t, AEMeasurable (X t) μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω)) :
    ∃ F : Ω → C(T, E), Measurable F ∧ ∀ᵐ ω ∂μ, ∀ t, F ω t = X t ω := by
  classical
  cases isEmpty_or_nonempty Ω
  · exact ⟨fun ω ↦ isEmptyElim ω, measurable_of_empty _,
      Filter.Eventually.of_forall fun ω ↦ isEmptyElim ω⟩
  cases isEmpty_or_nonempty T
  · refine ⟨fun ω ↦ ⟨fun t ↦ X t ω, continuous_of_discreteTopology⟩,
      ContinuousMap.measurable_iff_eval.2 (fun t ↦ isEmptyElim t), ?_⟩
    exact Filter.Eventually.of_forall fun _ _ ↦ rfl
  obtain ⟨ω₁⟩ := ‹Nonempty Ω›
  obtain ⟨t₁⟩ := ‹Nonempty T›
  let F : Ω → C(T, E) := fun ω ↦
    if h : Continuous (fun t ↦ X t ω) then ⟨fun t ↦ X t ω, h⟩
    else ContinuousMap.const T (X t₁ ω₁)
  have hF : ∀ᵐ ω ∂μ, ∀ t, F ω t = X t ω := by
    filter_upwards [hcont] with ω hc t
    simp [F, hc]
  have hFm : AEMeasurable F μ := ContinuousMap.aemeasurable_iff_eval.2 fun t ↦
    (hX t).congr (hF.mono fun ω hω ↦ (hω t).symm)
  refine ⟨hFm.mk F, hFm.measurable_mk, ?_⟩
  filter_upwards [hFm.ae_eq_mk, hF] with ω hω hf t
  rw [← hω]
  exact hf t

/-- An a.e.-continuous process whose initial value is `x₀` almost everywhere admits a
measurable based continuous-path realization agreeing with it simultaneously at all times
almost everywhere, outside one common null set. No completion of the sample space or
measurability of the continuity event is assumed. -/
theorem exists_measurable_basedMap_ae_eq
    (hX : ∀ t, AEMeasurable (X t) μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hstart : ∀ᵐ ω ∂μ, X t₀ ω = x₀) :
    ∃ F : Ω → BasedMap T E t₀ x₀, Measurable F ∧
      ∀ᵐ ω ∂μ, ∀ t, (F ω).1 t = X t ω := by
  classical
  obtain ⟨F, -, hF⟩ := exists_measurable_continuousMap_ae_eq hX hcont
  let G : Ω → BasedMap T E t₀ x₀ := fun ω ↦
    if h : F ω t₀ = x₀ then ⟨F ω, h⟩ else ⟨ContinuousMap.const T x₀, rfl⟩
  have hG : ∀ᵐ ω ∂μ, ∀ t, (G ω).1 t = X t ω := by
    filter_upwards [hF, hstart] with ω hf hs t
    simp [G, (hf t₀).trans hs, hf t]
  have hGm : AEMeasurable G μ := BasedMap.aemeasurable_iff_eval.2 fun t ↦
    (hX t).congr (hG.mono fun ω hω ↦ (hω t).symm)
  refine ⟨hGm.mk G, hGm.measurable_mk, ?_⟩
  filter_upwards [hGm.ae_eq_mk, hG] with ω hω hg t
  rw [← hω]
  exact hg t

/-- A finite-measure process with a.e.-measurable coordinates and a.e.-continuous paths has
exactly one measure on continuous paths with its finite-dimensional laws. -/
theorem existsUnique_continuousMap_measure_forall_finset_map_restrict_eq [IsFiniteMeasure μ]
    (hX : ∀ t, AEMeasurable (X t) μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω)) :
    ∃! ν : Measure C(T, E), ∀ I : Finset T,
      ν.map (fun γ : C(T, E) ↦ I.restrict (γ : T → E)) =
        μ.map (fun ω ↦ I.restrict (X · ω)) := by
  obtain ⟨F, hFm, hF⟩ := exists_measurable_continuousMap_ae_eq hX hcont
  have hlaw (I : Finset T) : (μ.map F).map (fun γ : C(T, E) ↦ I.restrict (γ : T → E)) =
      μ.map (fun ω ↦ I.restrict (X · ω)) := by
    rw [Measure.map_map (ContinuousMap.measurable_finsetRestrict I) hFm]
    apply Measure.map_congr
    filter_upwards [hF] with ω hω
    exact funext fun t ↦ hω t
  refine ⟨μ.map F, hlaw, ?_⟩
  intro ν hνlaw
  exact continuousMap_measure_ext_of_forall_finset_map_restrict_eq
    fun I ↦ (hνlaw I).trans (hlaw I).symm

/-- A finite-measure process with a.e.-measurable coordinates, a.e.-continuous paths and
initial value `x₀` almost everywhere has exactly one measure on based continuous paths
with its finite-dimensional laws. -/
theorem existsUnique_basedMap_measure_forall_finset_map_restrict_eq [IsFiniteMeasure μ]
    (hX : ∀ t, AEMeasurable (X t) μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hstart : ∀ᵐ ω ∂μ, X t₀ ω = x₀) :
    ∃! ν : Measure (BasedMap T E t₀ x₀),
      ∀ I : Finset T, ν.map (fun γ ↦ I.restrict (γ.1 : T → E)) =
        μ.map (fun ω ↦ I.restrict (X · ω)) := by
  obtain ⟨F, hFm, hF⟩ := exists_measurable_basedMap_ae_eq hX hcont hstart
  have hlaw (I : Finset T) : (μ.map F).map (fun γ ↦ I.restrict (γ.1 : T → E)) =
      μ.map (fun ω ↦ I.restrict (X · ω)) := by
    rw [Measure.map_map (BasedMap.measurable_finsetRestrict I) hFm]
    apply Measure.map_congr
    filter_upwards [hF] with ω hω
    exact funext fun t ↦ hω t
  refine ⟨μ.map F, hlaw, ?_⟩
  intro ν hνlaw
  exact basedMap_measure_ext_of_forall_finset_map_restrict_eq
    fun I ↦ (hνlaw I).trans (hlaw I).symm

end TauCeti
