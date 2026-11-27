/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp

/-!
# The support-restricted Bochner space at infinity

`TauCeti.linftySigma` is the submodule of native `L∞` consisting of classes that are almost
everywhere finitely strongly measurable. Its inherited norm is complete when the target is
complete. The submodule is closed even for an incomplete target, and equals the whole native
space for sigma-finite measures.

This distinction is necessary over arbitrary measures: finite-measure simple approximants
cannot detect a purely infinite part of a measure, although native `L∞` can. This space is the
natural infinity endpoint for integral representations of operators on Bochner `L¹`.
The inclusion is the native submodule linear isometry `Submodule.subtypeₗᵢ`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Definition 1.2.15 and Remark 1.2.16 (the finite-support convention).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The submodule of native `L∞` whose classes admit a.e. finite-measure simple approximation. -/
def linftySigma (𝕜 : Type*) [NormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (μ : Measure α) :
    Submodule 𝕜 (Lp E ∞ μ) where
  carrier := {f | AEFinStronglyMeasurable f μ}
  zero_mem' := (aefinStronglyMeasurable_zero μ).congr (Lp.coeFn_zero E ∞ μ).symm
  add_mem' hf hg := (hf.add hg).congr (Lp.coeFn_add _ _).symm
  smul_mem' c _ hf := (hf.const_smul c).congr (Lp.coeFn_smul c _).symm

variable {μ : Measure α}

/-- Membership in the support-restricted infinity space is a.e. finite strong measurability. -/
@[simp]
theorem mem_linftySigma_iff {f : Lp E ∞ μ} :
    f ∈ linftySigma 𝕜 E μ ↔ AEFinStronglyMeasurable f μ := Iff.rfl

/-- Any a.e. representative can be used to test membership in `linftySigma`. -/
theorem mem_linftySigma_iff_of_ae_eq {f : Lp E ∞ μ} {g : α → E} (hfg : f =ᵐ[μ] g) :
    f ∈ linftySigma 𝕜 E μ ↔ AEFinStronglyMeasurable g μ :=
  ⟨fun hf ↦ hf.congr hfg, fun hg ↦ hg.congr hfg.symm⟩

/-- The support-restricted infinity space is closed without completeness of the target. -/
theorem isClosed_linftySigma : IsClosed (linftySigma 𝕜 E μ : Set (Lp E ∞ μ)) := by
  refine IsSeqClosed.isClosed fun {f g} hf hlim ↦ ?_
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  exact aefinStronglyMeasurable_of_tendsto_ae (fun n ↦ hf (ns n)) hae

/-- The inherited infinity norm is complete for a complete target. -/
instance [CompleteSpace E] : CompleteSpace (linftySigma 𝕜 E μ) :=
  isClosed_linftySigma.isComplete.completeSpace_coe

/-- On a sigma-finite space, the support-restricted infinity space is all of native `L∞`. -/
@[simp]
theorem linftySigma_eq_top [SigmaFinite μ] : linftySigma 𝕜 E μ = ⊤ := by
  apply top_unique
  intro f _
  exact ((Lp.stronglyMeasurable f).finStronglyMeasurable μ).aefinStronglyMeasurable

/-- The native isometric inclusion is onto for sigma-finite measures. -/
theorem linftySigma_subtype_surjective [SigmaFinite μ] :
    Function.Surjective (linftySigma 𝕜 E μ).subtypeₗᵢ := by
  intro f
  exact ⟨⟨f, linftySigma_eq_top (𝕜 := 𝕜) (E := E) (μ := μ) ▸ Submodule.mem_top⟩, rfl⟩

/-- If every finite-measure measurable set is null, the support-restricted infinity space is
zero. This includes a singleton of infinite measure. -/
theorem linftySigma_eq_bot_of_forall_measure_eq_zero
    (hμ : ∀ s, MeasurableSet s → μ s < ∞ → μ s = 0) :
    linftySigma 𝕜 E μ = ⊥ := by
  apply bot_unique
  intro f hf
  rw [Submodule.mem_bot]
  apply Lp.ext
  have hz : f =ᵐ[μ] 0 := by
    by_contra hne
    obtain ⟨s, hs, hpos, hfin⟩ := hf.exists_measurableSet_measure_pos_lt_top hne
    exact (ne_of_gt hpos) (hμ s hs hfin)
  exact hz.trans (Lp.coeFn_zero E ∞ μ).symm

end TauCeti

/-- Bounded postcomposition preserves the support-restricted infinity space. The norm bound
is the native `ContinuousLinearMap.norm_compLp_le`. -/
theorem ContinuousLinearMap.compLp_mem_linftySigma {α 𝕜 E F : Type*} [MeasurableSpace α]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (L : E →L[𝕜] F) {μ : Measure α}
    {f : Lp E ∞ μ} (hf : f ∈ TauCeti.linftySigma 𝕜 E μ) :
    L.compLp f ∈ TauCeti.linftySigma 𝕜 F μ := by
  obtain ⟨s, hs, hz, hσ⟩ := hf.finStronglyMeasurable_mk.exists_set_sigmaFinite
  have hL : FinStronglyMeasurable (fun x ↦ L (hf.mk f x)) μ :=
    (L.continuous.comp_stronglyMeasurable
      hf.finStronglyMeasurable_mk.stronglyMeasurable).finStronglyMeasurable_of_set_sigmaFinite
        hs (fun x hx ↦ by simp [hz x hx]) hσ
  refine hL.aefinStronglyMeasurable.congr ?_
  exact ((L.coeFn_compLp' f).trans (hf.ae_eq_mk.fun_comp L)).symm
