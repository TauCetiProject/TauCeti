/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.L2

/-!
# Smooth forms are dense in geometric L²

On a compact Riemannian manifold the image of compactly supported smooth forms in
`TauCeti.L2Form` is dense. Compactness makes every smooth form compactly supported, so this
is the dense smooth domain used for the exterior derivative, codifferential and Hodge
Laplacian as unbounded operators. The result uses a continuous Riemannian metric and does
not require orientability or boundarylessness.

The proof applies density of smooth sections to the actual alternating bundle carrying its
Gram metric, through `TauCeti.WithFiberMetric`.
-/

public noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- Smooth real forms have dense image in the geometric L² space on a compact Riemannian
manifold, including in the presence of a boundary. -/
theorem compactlySupportedForms.denseRange_toL2Form :
    DenseRange (compactlySupportedForms.toL2Form I M k) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let : ContMDiffVectorBundle ∞ (E [⋀^Fin k]→L[ℝ] ℝ)
      (WithFiberMetric (formMetric I M k)) I :=
    inferInstanceAs (ContMDiffVectorBundle ∞ (E [⋀^Fin k]→L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) I)
  have hdense := ContMDiffSection.denseRange_toL2 (I := I)
    (F := E [⋀^Fin k]→L[ℝ] ℝ) (V := WithFiberMetric (formMetric I M k))
    (μ := riemannianVolume I M)
  refine hdense.mono ?_
  rintro _ ⟨s, rfl⟩
  let α : compactlySupportedForms I M k :=
    ⟨SmoothForm.ofContMDiffSection s, by simp [compactlySupportedForms_eq_top]⟩
  refine ⟨α, ?_⟩
  apply LpSection.ext
  filter_upwards [compactlySupportedForms.coeFn_toL2Form α,
    ContMDiffSection.coeFn_toL2 s] with x hα hs
  refine hα.trans ?_
  rw [WithFiberMetric.toWithFiberMetric_apply]
  -- Recover evaluation through the public inverse laws for the section/form comparison.
  have heval := congrArg (fun t ↦ t x) (SmoothForm.toContMDiffSection_ofContMDiffSection s)
  rw [SmoothForm.toContMDiffSection_apply] at heval
  exact heval.trans hs.symm

end TauCeti
