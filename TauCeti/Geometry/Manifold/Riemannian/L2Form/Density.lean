/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.WithFiberMetric
public import TauCeti.Geometry.Manifold.VectorBundle.Section.L2.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.L2.Density

/-!
# Smooth forms are dense in geometric L²

On a Riemannian manifold the image of compactly supported smooth forms in `TauCeti.L2Form` is
dense. The result uses a continuous Riemannian metric and requires neither compactness,
orientability nor boundarylessness. Density is a prerequisite for realizing the exterior
derivative, codifferential and Hodge Laplacian as unbounded operators on `L²Ωᵏ(M)`; it does not
by itself supply the metric regularity or boundary conditions that such realizations need.

The class of a compactly supported form is the class of its section of the bundle of forms, read
in the fibres carrying the Gram metric through `TauCeti.WithFiberMetric.contMDiffSectionEquiv`
(`TauCeti.compactlySupportedForms.toL2Form_eq_toL2`). Density then follows from density of
compactly supported smooth sections, `ContMDiffSection.denseRange_toL2`.
-/

public noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] {k : ℕ}

namespace compactlySupportedForms

/-- The section of the bundle of forms underlying a compactly supported form, read in the fibres
carrying the Gram metric, has compact support. -/
theorem contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported
    (α : compactlySupportedForms I M k) :
    WithFiberMetric.contMDiffSectionEquiv (formMetric I M k) α.val.toContMDiffSection ∈
      ContMDiffSection.compactlySupported I (E [⋀^Fin k]→L[ℝ] ℝ) ∞
        (WithFiberMetric (formMetric I M k)) := by
  rw [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def]
  convert (mem_compactlySupportedForms I).1 α.property using 1
  simp only [WithFiberMetric.contMDiffSectionEquiv_apply, WithFiberMetric.toWithFiberMetric_apply,
    SmoothForm.toContMDiffSection_apply]
  rfl

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The class of a compactly supported form in `L²Ωᵏ(M)` is the class of its section of the
bundle of forms, read in the fibres carrying the Gram metric. -/
theorem toL2Form_eq_toL2 (α : compactlySupportedForms I M k) :
    toL2Form I M k α = ContMDiffSection.toL2 (riemannianVolume I M)
      ⟨_, contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported α⟩ := by
  apply LpSection.ext
  filter_upwards [coeFn_toL2Form α, ContMDiffSection.coeFn_toL2 (μ := riemannianVolume I M)
    ⟨_, contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported α⟩] with x hα hs
  rw [hα, hs, WithFiberMetric.contMDiffSectionEquiv_apply,
    SmoothForm.toContMDiffSection_apply]

variable [T2Space M]

/-- Compactly supported smooth real forms have dense image in the geometric L² space on a
Riemannian manifold, including in the presence of a boundary. -/
theorem denseRange_toL2Form : DenseRange (toL2Form I M k) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  refine (ContMDiffSection.denseRange_toL2 (I := I) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := WithFiberMetric (formMetric I M k)) (μ := riemannianVolume I M)).mono ?_
  rintro _ ⟨s, rfl⟩
  let α : SmoothForm I M ℝ k := SmoothForm.ofContMDiffSection
    ((WithFiberMetric.contMDiffSectionEquiv (formMetric I M k)).symm s)
  -- The section of `α`, read in the fibres carrying the Gram metric, is `s` itself.
  have hs : WithFiberMetric.contMDiffSectionEquiv (formMetric I M k) α.toContMDiffSection =
      s := by
    simp [α]
  have hα : α ∈ compactlySupportedForms I M k := by
    rw [mem_compactlySupportedForms]
    convert (ContMDiffSection.mem_compactlySupported.1 s.property) using 1
    rw [ContMDiffSection.tsupport_def, ← hs]
    simp only [WithFiberMetric.contMDiffSectionEquiv_apply,
      WithFiberMetric.toWithFiberMetric_apply, SmoothForm.toContMDiffSection_apply]
    rfl
  refine ⟨⟨α, hα⟩, ?_⟩
  rw [toL2Form_eq_toL2]
  exact congrArg _ (Subtype.ext hs)

end compactlySupportedForms

end TauCeti
