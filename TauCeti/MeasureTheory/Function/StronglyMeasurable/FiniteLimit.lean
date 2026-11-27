/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Almost everywhere limits with finite-measure simple approximants

Almost everywhere finite strong measurability is preserved by almost everywhere sequential
limits. The countably many finite-measure supports of the approximating simple functions
provide a common sigma-finite support
(`AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable`). This closure property is
useful when taking limits in Bochner spaces over measures that need not be sigma-finite.
-/

public section

open Filter Set TopologicalSpace
open scoped Topology

namespace MeasureTheory

/-- Almost everywhere finite strong measurability is invariant under almost everywhere equality. -/
theorem AEFinStronglyMeasurable.congr {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [Zero E] {μ : Measure α} {f g : α → E}
    (hf : AEFinStronglyMeasurable f μ) (hfg : f =ᵐ[μ] g) :
    AEFinStronglyMeasurable g μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk, hfg.symm.trans hf.ae_eq_mk⟩

/-- Countably many almost everywhere finitely strongly measurable functions have a common
measurable support on which the measure is sigma-finite: the union of the supports of the simple
approximants of their finitely strongly measurable representatives. -/
theorem AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable {α ι E : Type*}
    [MeasurableSpace α] [TopologicalSpace E] [T2Space E] [Zero E] [Countable ι]
    {μ : Measure α} {g : ι → α → E} (hg : ∀ i, AEFinStronglyMeasurable (g i) μ) :
    ∃ t, MeasurableSet t ∧ (∀ i, g i =ᵐ[μ.restrict tᶜ] 0) ∧ SigmaFinite (μ.restrict t) := by
  classical
  have hu i : FinStronglyMeasurable ((hg i).mk (g i)) μ := (hg i).finStronglyMeasurable_mk
  let T (p : ι × ℕ) := Function.support ((hu p.1).approx p.2)
  let t := ⋃ p, T p
  have ht : MeasurableSet t :=
    MeasurableSet.iUnion fun p ↦ ((hu p.1).approx p.2).measurableSet_support
  refine ⟨t, ht, fun i ↦ ?_, ?_⟩
  · rw [EventuallyEq, ae_restrict_iff' ht.compl]
    filter_upwards [(hg i).ae_eq_mk] with x hx hxt
    have hz m : (hu i).approx m x = 0 :=
      Function.notMem_support.mp fun h ↦ hxt (mem_iUnion.mpr ⟨(i, m), h⟩)
    exact hx.trans (tendsto_nhds_unique ((hu i).tendsto_approx x)
      (tendsto_const_nhds.congr fun m ↦ (hz m).symm))
  · refine Measure.sigmaFinite_of_countable ((countable_range T).insert tᶜ) ?_
      (by rw [sUnion_insert, sUnion_range, compl_union_self])
    rintro _ (rfl | ⟨p, rfl⟩)
    · simp [Measure.restrict_apply ht.compl]
    · exact (Measure.restrict_le_self _).trans_lt ((hu p.1).fin_support_approx p.2)

/-- An almost everywhere limit of a sequence of almost everywhere finitely strongly measurable
functions is almost everywhere finitely strongly measurable. -/
theorem aefinStronglyMeasurable_of_tendsto_ae {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [PseudoMetrizableSpace E] [T2Space E] [Zero E]
    {μ : Measure α} {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, AEFinStronglyMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    AEFinStronglyMeasurable g μ := by
  classical
  obtain ⟨s, hs, hzero, hσ⟩ := AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable hf
  have hg0 : ∀ᵐ x ∂μ, x ∉ s → g x = 0 := by
    have h0 := (ae_restrict_iff' hs.compl).mp (ae_all_iff.mpr hzero)
    filter_upwards [hlim, h0] with x hx hx0 hx'
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr fun n ↦ (hx0 hx' n).symm)
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦
      ⟨(hf n).mk (f n), (hf n).finStronglyMeasurable_mk.stronglyMeasurable, (hf n).ae_eq_mk⟩) hlim
  refine ⟨s.indicator (hg.mk g), ?_, ?_⟩
  · exact (hg.stronglyMeasurable_mk.indicator hs).finStronglyMeasurable_of_set_sigmaFinite
      hs (fun x hx ↦ indicator_of_notMem hx _) hσ
  · filter_upwards [hg.ae_eq_mk, hg0] with x hx hx0
    by_cases hxs : x ∈ s <;> simp [hxs, ← hx, hx0]

end MeasureTheory
