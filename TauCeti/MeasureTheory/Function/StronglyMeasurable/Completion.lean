/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteSupport
import TauCeti.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Strong measurability and the completion of a measure

Adjoining ambient null sets to a σ-algebra preserves almost everywhere strong measurability
for completely metrizable targets. The original σ-algebra need not be related to the measure's
ambient σ-algebra. Representatives are selected through piecewise combinations and limits;
complete metrizability ensures that the limit representative is measurable.

For the σ-algebra of `μ`-null measurable sets, on which the completion `μ.completion` lives,
pointwise strong measurability is the same as almost everywhere strong measurability for `μ`,
as long as the function has separable range (`stronglyMeasurable_nullMeasurableSpace_iff`).
The same holds for the finite-support notions: finite strong measurability for `μ.completion`
is almost everywhere finite strong measurability for `μ`, for an arbitrary measure
(`finStronglyMeasurable_completion_iff`). For a σ-finite measure both also agree with strong
measurability for the null measurable σ-algebra
(`stronglyMeasurable_nullMeasurableSpace_iff_aefinStronglyMeasurable`).

Preimages need no separate statement. If `hf : AEStronglyMeasurable f μ`, then for every set `B`
the preimages of `B` under `f` and under its strongly measurable representative `hf.mk f` agree
almost everywhere (`hf.ae_eq_mk.preimage B`) and have the same measure. For a Borel set `B` the
second preimage is measurable and the first is null measurable
(`hf.aemeasurable.nullMeasurableSet_preimage`).

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, Proposition 1.1.16 and Remarks 1.1.18–1.1.19.
-/

public section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace TauCeti.MeasureTheory

/-- Adjoining ambient null sets to an arbitrary σ-algebra does not change almost everywhere
strong measurability for a completely metrizable target. No inclusion between the original
σ-algebra and the measure's ambient σ-algebra is required. -/
@[simp]
theorem aestronglyMeasurable_eventuallyMeasurableSpace_iff {Ω β : Type*}
    {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [TopologicalSpace β]
    [IsCompletelyMetrizableSpace β] {f : Ω → β} :
    AEStronglyMeasurable[eventuallyMeasurableSpace m (ae μ)] f μ ↔
      AEStronglyMeasurable[m] f μ := by
  classical
  refine ⟨?_, fun hf ↦ hf.mono le_eventuallyMeasurableSpace⟩
  rintro ⟨g, hg, hfg⟩
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable
  have : Nonempty β := hΩ.map f
  have hgm : ∀ (g : Ω → β), StronglyMeasurable[eventuallyMeasurableSpace m (ae μ)] g →
      AEStronglyMeasurable[m] g μ := by
    intro g hg
    induction g, hg using StronglyMeasurable.induction' with
    | const c => exact stronglyMeasurable_const.aestronglyMeasurable
    | @pcw f g s _ _ hs ihf ihg =>
      obtain ⟨t, ht, hst⟩ := hs
      refine ⟨t.piecewise (ihf.mk f) (ihg.mk g),
        ihf.stronglyMeasurable_mk.piecewise ht ihg.stronglyMeasurable_mk, ?_⟩
      filter_upwards [hst, ihf.ae_eq_mk, ihg.ae_eq_mk] with ω hω hfω hgω
      simp only [Set.piecewise, ← hω, hfω, hgω]
    | @lim f g _ _ ih hlim =>
      let : MeasurableSpace Ω := m
      refine ⟨fun ω ↦ limUnder atTop (fun n ↦ (ih n).mk (f n) ω),
        StronglyMeasurable.limUnder (fun n ↦ (ih n).stronglyMeasurable_mk), ?_⟩
      filter_upwards [ae_all_iff.2 (fun n ↦ (ih n).ae_eq_mk)] with ω hω
      have hlim' := hlim ω
      simp only [hω] at hlim'
      exact hlim'.limUnder_eq.symm
  exact (hgm g hg).congr hfg.symm

section NullMeasurableSpace

variable {S β : Type*} [MeasurableSpace S] {μ : Measure S} [TopologicalSpace β]
  [PseudoMetrizableSpace β] {f : S → β}

/-- A function with separable range is strongly measurable for the σ-algebra of `μ`-null
measurable sets exactly when it is almost everywhere strongly measurable for `μ`. -/
theorem stronglyMeasurable_nullMeasurableSpace_iff (hf : IsSeparable (Set.range f)) :
    StronglyMeasurable[NullMeasurableSpace.instMeasurableSpace (μ := μ)] f ↔
      AEStronglyMeasurable f μ := by
  borelize β
  rw [aestronglyMeasurable_iff_nullMeasurable_separable]
  exact ⟨fun h ↦ ⟨h.measurable, _, hf, .of_forall Set.mem_range_self⟩,
    fun h ↦ stronglyMeasurable_iff_measurable_separable.2 ⟨h.1, hf⟩⟩

/-- For a σ-finite measure, a function with separable range is strongly measurable for the
σ-algebra of `μ`-null measurable sets exactly when it is almost everywhere finitely strongly
measurable for `μ`. -/
theorem stronglyMeasurable_nullMeasurableSpace_iff_aefinStronglyMeasurable [Zero β]
    [SigmaFinite μ] (hf : IsSeparable (Set.range f)) :
    StronglyMeasurable[NullMeasurableSpace.instMeasurableSpace (μ := μ)] f ↔
      AEFinStronglyMeasurable f μ := by
  rw [stronglyMeasurable_nullMeasurableSpace_iff hf]
  exact ⟨fun h ↦ ⟨h.mk f, h.stronglyMeasurable_mk.finStronglyMeasurable μ, h.ae_eq_mk⟩,
    fun h ↦ ⟨h.mk f, h.finStronglyMeasurable_mk.stronglyMeasurable, h.ae_eq_mk⟩⟩

/-- A function with separable range is finitely strongly measurable for the completion of `μ`
exactly when it is almost everywhere finitely strongly measurable for `μ`. No σ-finiteness of
`μ` is needed. -/
theorem finStronglyMeasurable_completion_iff [T2Space β] [Zero β]
    (hf : IsSeparable (Set.range f)) :
    FinStronglyMeasurable (α := NullMeasurableSpace S μ) f μ.completion ↔
      AEFinStronglyMeasurable f μ := by
  -- `f` is not syntactically a function on `NullMeasurableSpace S μ`, so the characterizations
  -- are chained by `Iff.trans` rather than rewritten.
  refine (finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite
    (μ := μ.completion) (f := f)).trans <|
    (and_congr (stronglyMeasurable_nullMeasurableSpace_iff hf) ⟨?_, ?_⟩).trans
      aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite.symm
  · -- Replace the null measurable support by its measurable envelope.
    rintro ⟨t, ht, hzero, hσ⟩
    have ht' : MeasurableSet (toMeasurable μ t) := measurableSet_toMeasurable μ t
    refine ⟨toMeasurable μ t, ht', ae_restrict_of_forall_mem ht'.compl
      fun x hx ↦ hzero x fun hxt ↦ hx (subset_toMeasurable μ t hxt), ?_⟩
    rw [Measure.restrict_congr_set (NullMeasurableSet.toMeasurable_ae_eq ht)]
    exact (Measure.sigmaFinite_completion_restrict_iff ht).1 hσ
  · -- Enlarge the measurable support by the null set where `f` is nonzero outside it.
    rintro ⟨t, ht, hzero, hσ⟩
    rw [Filter.EventuallyEq, ae_restrict_iff' ht.compl] at hzero
    have hN : μ {x | ¬(x ∈ tᶜ → f x = 0)} = 0 := ae_iff.1 hzero
    have hu : NullMeasurableSet (t ∪ {x | ¬(x ∈ tᶜ → f x = 0)}) μ :=
      ht.nullMeasurableSet.union (NullMeasurableSet.of_null hN)
    refine ⟨_, hu, fun x hx ↦ ?_, (Measure.sigmaFinite_completion_restrict_iff hu).2 ?_⟩
    · simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hx
      exact hx.2 hx.1
    · rw [Measure.restrict_congr_set (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 hN))]
      exact hσ

end NullMeasurableSpace

end TauCeti.MeasureTheory
