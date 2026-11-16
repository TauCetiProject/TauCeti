/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Process.Indistinguishable

/-!
# Continuous processes and time-product almost-everywhere identities

A time-product almost-everywhere identity between processes with almost surely continuous
paths holds simultaneously at all times of a half-open interval. The left endpoint is
included, even though it has zero Lebesgue measure. No continuity at the excluded right
endpoint is needed.

For continuous fields evaluated along a process with a deterministic starting point, this
recovers equality of the fields at that point. This is useful when an identity first obtained
almost everywhere along trajectories must be evaluated at the initial state.

On a separable topological index space with Hausdorff target, two almost surely continuous
processes that agree almost surely at every deterministic time are indistinguishable
(`TauCeti.indist_of_ae_eq_of_ae_continuous`), without measurability or finiteness hypotheses.

The main inputs are Mathlib's product-measure section theorem `ae_ae_of_ae_prod`,
`Measure.eqOn_Ico_of_ae_eq`, and `DenseRange.equalizer` along a countable dense sequence.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- Two almost surely continuous processes indexed by a separable topological space with Hausdorff
target that agree almost surely at every deterministic time are indistinguishable. Neither
measurability of paths nor finiteness of the measure is required. -/
theorem indist_of_ae_eq_of_ae_continuous {ι Ω E : Type*} [TopologicalSpace ι]
    [TopologicalSpace.SeparableSpace ι] [TopologicalSpace E] [T2Space E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}
    (hXY : ∀ t, X t =ᵐ[P] Y t)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω)) :
    X ≡ᵐ[P] Y := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact Filter.Eventually.of_forall fun _ t ↦ IsEmpty.elim ‹_› t
  · have hd : ∀ᵐ ω ∂P, ∀ n : ℕ, X (TopologicalSpace.denseSeq ι n) ω =
        Y (TopologicalSpace.denseSeq ι n) ω :=
      ae_all_iff.2 fun n ↦ hXY _
    filter_upwards [hX, hY, hd] with ω hXω hYω hdω
    exact congrFun ((TopologicalSpace.denseRange_denseSeq ι).equalizer hXω hYω (funext hdω))

variable {Ω E Y : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
  [TopologicalSpace Y] [T2Space Y] {a b : ℝ}

/-- Continuous processes equal almost everywhere for Lebesgue time times the sample measure
are equal simultaneously on `[a,b)` outside a single sample-null set. No measurability of
individual paths or joint measurability beyond the product-a.e. hypothesis is required. -/
theorem ae_eqOn_Ico_of_ae_eq_prod {f g : ℝ → Ω → Y}
    (hf : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ f t ω) (Ico a b))
    (hg : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ g t ω) (Ico a b))
    (hfg : ∀ᵐ p ∂(volume.restrict (Ico a b)).prod P, f p.1 p.2 = g p.1 p.2) :
    ∀ᵐ ω ∂P, EqOn (fun t ↦ f t ω) (fun t ↦ g t ω) (Ico a b) := by
  have hsections := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hfg)
  filter_upwards [hf, hg, hsections] with ω hf hg hfg
  exact Measure.eqOn_Ico_of_ae_eq volume hfg hf hg

/-- A time-product-a.e. identity between continuous fields along a process holds at its
deterministic starting point. Only a nonzero sample measure is needed, not a probability
measure. The process need not be adapted or solve a differential equation. -/
theorem eq_of_ae_eq_along_process [TopologicalSpace E] [NeZero P]
    {D : Set (E × ℝ)} {F G : E × ℝ → Y} {S : ℝ → Ω → E} {x : E}
    (hab : a < b) (hF : ContinuousOn F D) (hG : ContinuousOn G D)
    (hS : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ S t ω) (Ico a b))
    (hD : ∀ᵐ ω ∂P, ∀ t ∈ Ico a b, (S t ω, t) ∈ D)
    (hstart : ∀ᵐ ω ∂P, S a ω = x)
    (hfg : ∀ᵐ p ∂(volume.restrict (Ico a b)).prod P,
      F (S p.1 p.2, p.1) = G (S p.1 p.2, p.1)) :
    F (x, a) = G (x, a) := by
  have hf : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ F (S t ω, t)) (Ico a b) := by
    filter_upwards [hS, hD] with ω hS hD
    exact hF.comp (hS.prodMk continuousOn_id) hD
  have hg : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ G (S t ω, t)) (Ico a b) := by
    filter_upwards [hS, hD] with ω hS hD
    exact hG.comp (hS.prodMk continuousOn_id) hD
  obtain ⟨ω, heq, hstart⟩ := ((ae_eqOn_Ico_of_ae_eq_prod hf hg hfg).and hstart).exists
  simpa only [hstart] using heq (left_mem_Ico.mpr hab)

end TauCeti
