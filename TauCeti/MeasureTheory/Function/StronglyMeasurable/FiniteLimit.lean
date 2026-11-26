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
provide a common sigma-finite support. This closure property is useful when taking limits in
Bochner spaces over measures that need not be sigma-finite.
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
  classical
  let u n := (hf n).mk (f n)
  have hu n : FinStronglyMeasurable (u n) μ := (hf n).finStronglyMeasurable_mk
  let T (p : ℕ × ℕ) := Function.support ((hu p.1).approx p.2)
  let s := ⋃ p, T p
  have hT p : MeasurableSet (T p) := ((hu p.1).approx p.2).measurableSet_support
  have hs : MeasurableSet s := MeasurableSet.iUnion hT
  have hσ : SigmaFinite (μ.restrict s) := by
    refine Measure.sigmaFinite_of_countable ((countable_range T).insert sᶜ) ?_
      (by rw [sUnion_insert, sUnion_range, compl_union_self])
    rintro _ (rfl | ⟨p, rfl⟩)
    · simp [Measure.restrict_apply hs.compl]
    · exact (Measure.restrict_le_self _).trans_lt ((hu p.1).fin_support_approx p.2)
  have hu0 n x (hx : x ∉ s) : u n x = 0 := by
    have hz m : (hu n).approx m x = 0 := by
      exact Function.notMem_support.mp (fun h ↦ hx (mem_iUnion.mpr ⟨(n, m), h⟩))
    exact tendsto_nhds_unique ((hu n).tendsto_approx x)
      (tendsto_const_nhds.congr fun m ↦ (hz m).symm)
  have heq : ∀ᵐ x ∂μ, ∀ n, f n x = u n x :=
    ae_all_iff.mpr fun n ↦ (hf n).ae_eq_mk
  have hg0 : ∀ᵐ x ∂μ, x ∉ s → g x = 0 := by
    filter_upwards [hlim, heq] with x hx he hx'
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr fun n ↦
      ((he n).trans (hu0 n x hx')).symm)
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ ⟨u n, (hu n).stronglyMeasurable, (hf n).ae_eq_mk⟩) hlim
  refine ⟨s.indicator (hg.mk g), ?_, ?_⟩
  · exact (hg.stronglyMeasurable_mk.indicator hs).finStronglyMeasurable_of_set_sigmaFinite
      hs (fun x hx ↦ indicator_of_notMem hx _) hσ
  · filter_upwards [hg.ae_eq_mk, hg0] with x hx hx0
    by_cases hxs : x ∈ s <;> simp [hxs, ← hx, hx0]

end MeasureTheory
