/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Finite.Support

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

/-- An almost everywhere limit of a sequence of almost everywhere finitely strongly measurable
functions is almost everywhere finitely strongly measurable. -/
theorem aefinStronglyMeasurable_of_tendsto_ae {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [PseudoMetrizableSpace E] [T2Space E] [Zero E]
    {μ : Measure α} {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, AEFinStronglyMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    AEFinStronglyMeasurable g μ := by
  obtain ⟨s, hs, hzero, hσ⟩ := AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable hf
  have hg0 : ∀ᵐ x ∂μ, x ∉ s → g x = 0 := by
    have h0 := (ae_restrict_iff' hs.compl).mp (ae_all_iff.mpr hzero)
    filter_upwards [hlim, h0] with x hx hx0 hx'
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr fun n ↦ (hx0 hx' n).symm)
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦
      ⟨(hf n).mk (f n), (hf n).finStronglyMeasurable_mk.stronglyMeasurable, (hf n).ae_eq_mk⟩) hlim
  exact TauCeti.aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite.2
    ⟨hg, s, hs, (ae_restrict_iff' hs.compl).mpr hg0, hσ⟩

end MeasureTheory
