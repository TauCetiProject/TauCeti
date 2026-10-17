/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.DifferentialForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Regularity of planar circulation forms

Real Cn coefficient fields give Cn actual manifold forms, allowing the smooth-boundary
comparison to be applied from planar field data.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti.Green

/-- Real Cn coefficients give a Cn circulation form on the real plane. -/
theorem _root_.ContDiff.isSmoothForm_manifoldOneForm {n : WithTop ℕ∞} {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) :
    IsSmoothForm 𝓘(ℝ, ℂ) n (manifoldOneForm P Q) := by
  apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
  intro x
  rw [manifoldOneForm_inChartAt]
  have he : oneForm P Q = fun z ↦ P z • Complex.reCLM + Q z • Complex.imCLM := by
    ext z v
    simp [oneForm_apply]
  have hlin : ContDiff ℝ n (oneForm P Q) := by
    rw [he]
    exact (hP.smul contDiff_const).add (hQ.smul contDiff_const)
  exact ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hlin).contDiffWithinAt

/-- Coefficients smooth on a neighbourhood of the image give a smooth pulled-back circulation
form on a compact source. No coefficient regularity outside that neighbourhood is needed. -/
theorem _root_.ContMDiff.isSmoothForm_mpullback_manifoldOneForm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
    {n : ℕ∞} {f : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) (n + 1) f)
    {U : Set ℂ} (hU : IsOpen U) (hrange : range f ⊆ U)
    {P Q : ℂ → ℝ} (hP : ContDiffOn ℝ n P U) (hQ : ContDiffOn ℝ n Q U) :
    IsSmoothForm I n (mpullback I 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) := by
  have hK := isCompact_range hf.continuous
  obtain ⟨P', hP', _, _, heP⟩ := hP.exists_contDiff_eventuallyEq_on_isCompact hK hU hrange
  obtain ⟨Q', hQ', _, _, heQ⟩ := hQ.exists_contDiff_eventuallyEq_on_isCompact hK hU hrange
  have he : mpullback I 𝓘(ℝ, ℂ) f (manifoldOneForm P' Q') =
      mpullback I 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) := by
    ext x v
    simp only [mpullback_apply, manifoldOneForm_apply, oneForm_apply]
    rw [(heP (f x) (mem_range_self x)).eq_of_nhds,
      (heQ (f x) (mem_range_self x)).eq_of_nhds]
  rw [← he]
  exact (ContDiff.isSmoothForm_manifoldOneForm hP' hQ').mpullback hf

end TauCeti.Green
