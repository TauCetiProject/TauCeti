/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import TauCeti.MeasureTheory.Measure.ContinuousMap

/-!
# Realizing continuous processes on based path space

An a.e.-continuous process with a deterministic initial value has a measurable realization
in `BasedMap T E t₀ x₀`, the existing subtype of continuous maps taking `t₀` to `x₀`.
The realization agrees with the process at every time outside one common null set, even
when the original coordinates are only a.e. measurable and the sample space is incomplete.
Its pushforward is the unique probability law with the prescribed finite-dimensional laws.

Taking `T = ℝ≥0`, or a compact time interval, gives continuous-path laws in the compact-open
(or uniform, on a compact interval) topology. No Gaussian or independent-increment hypothesis
is made: this construction alone does not assert that the resulting law is Wiener measure.

The measurable-space input is Mathlib's `ContinuousMap.measurable_iff_eval` and the
countable-dense-evaluation criterion for a.e. measurability.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 2, §2.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {T E Ω : Type*} [TopologicalSpace T] [SecondCountableTopology T]
  [LocallyCompactSpace T] [TopologicalSpace E] [SecondCountableTopology E]
  [RegularSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] {μ : Measure Ω} {X : T → Ω → E} {t₀ : T} {x₀ : E}

/-- An a.e.-continuous process with a fixed initial value admits a literally measurable
based continuous-path realization, equal to the original process simultaneously at all times.
No completion of the sample space or measurability of its continuity event is assumed. -/
theorem exists_measurable_basedMap_ae_eq
    (hX : ∀ t, AEMeasurable (X t) μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hstart : ∀ᵐ ω ∂μ, X t₀ ω = x₀) :
    ∃ F : Ω → BasedMap T E t₀ x₀, Measurable F ∧
      ∀ᵐ ω ∂μ, ∀ t, (F ω).1 t = X t ω := by
  classical
  let F : Ω → C(T, E) := fun ω ↦
    if h : Continuous (fun t ↦ X t ω) ∧ X t₀ ω = x₀ then
      ⟨fun t ↦ X t ω, h.1⟩ else ContinuousMap.const T x₀
  have hF : ∀ᵐ ω ∂μ, ∀ t, F ω t = X t ω := by
    filter_upwards [hcont, hstart] with ω hc hs t
    simp [F, hc, hs]
  have hFstart (ω : Ω) : F ω t₀ = x₀ := by
    dsimp only [F]
    split_ifs with h
    · exact h.2
    · rfl
  have hFm : AEMeasurable F μ := ContinuousMap.aemeasurable_iff_eval.2 fun t ↦
    (hX t).congr (hF.mono fun ω hω ↦ (hω t).symm)
  let G : Ω → BasedMap T E t₀ x₀ :=
    codRestrict F {γ : C(T, E) | γ t₀ = x₀} hFstart
  have hG : AEMeasurable G μ := hFm.subtype_mk
  refine ⟨hG.mk G, hG.measurable_mk, ?_⟩
  filter_upwards [hG.ae_eq_mk, hF] with ω hω hf t
  rw [← hω]
  simpa only [G, val_codRestrict_apply] using hf t

/-- A probability process with a.e.-continuous paths and deterministic initial value has
exactly one probability law on based continuous paths with its finite-dimensional laws.
The law is constructed by a measurable realization, not by assuming a path-space measure. -/
theorem existsUnique_basedMap_law [IsProbabilityMeasure μ]
    (hX : ∀ t, AEMeasurable (X t) μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (hstart : ∀ᵐ ω ∂μ, X t₀ ω = x₀) :
    ∃! ν : Measure (BasedMap T E t₀ x₀), IsProbabilityMeasure ν ∧
      ∀ I : Finset T, ν.map (fun γ ↦ I.restrict (γ.1 : T → E)) =
        μ.map (fun ω ↦ I.restrict (X · ω)) := by
  obtain ⟨F, hFm, hF⟩ := exists_measurable_basedMap_ae_eq hX hcont hstart
  have heval (I : Finset T) : Measurable
      (fun γ : BasedMap T E t₀ x₀ ↦ I.restrict (γ.1 : T → E)) :=
    (Finset.measurable_restrict I).comp (Measurable.of_eval fun t ↦
      (ContinuousMap.measurable_eval t).comp measurable_subtype_coe)
  have hlaw (I : Finset T) : (μ.map F).map (fun γ ↦ I.restrict (γ.1 : T → E)) =
      μ.map (fun ω ↦ I.restrict (X · ω)) := by
    rw [Measure.map_map (heval I) hFm]
    apply Measure.map_congr
    filter_upwards [hF] with ω hω
    exact funext fun t ↦ hω t
  refine ⟨μ.map F, ⟨inferInstance, hlaw⟩, ?_⟩
  rintro ν ⟨-, hνlaw⟩
  exact basedMap_measure_ext fun I ↦ (hνlaw I).trans (hlaw I).symm

end TauCeti
