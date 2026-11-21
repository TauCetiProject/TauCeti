/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.WithFiberMetric
import TauCeti.Geometry.Manifold.VectorBundle.Section.L2.Density

/-!
# Smooth forms are dense in geometric L²

On a Riemannian manifold the image of compactly supported smooth forms in `TauCeti.L2Form` is
dense. The result uses a continuous Riemannian metric and requires neither compactness,
orientability nor boundarylessness. Density supplies, in each source degree, a dense smooth
domain for the exterior derivative `d : L²Ωᵏ(M) → L²Ωᵏ⁺¹(M)`, the codifferential
`d* : L²Ωᵏ⁺¹(M) → L²Ωᵏ(M)` and the Hodge Laplacian on `L²Ωᵏ(M)`, as unbounded operators; it does
not by itself supply the metric regularity or boundary conditions that their closed or
self-adjoint realizations need.

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
  [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

section Comparison

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The section of the bundle of forms underlying a smooth form, read in the fibres carrying the
Gram metric, has compact support exactly when the form does. -/
theorem contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported_iff
    (α : SmoothForm I M ℝ k) :
    WithFiberMetric.contMDiffSectionEquiv (formMetric I M k) α.toContMDiffSection ∈
      ContMDiffSection.compactlySupported I (E [⋀^Fin k]→L[ℝ] ℝ) ∞
        (WithFiberMetric (formMetric I M k)) ↔ α ∈ compactlySupportedForms I M k := by
  rw [ContMDiffSection.mem_compactlySupported, WithFiberMetric.tsupport_contMDiffSectionEquiv,
    ContMDiffSection.tsupport_def, mem_compactlySupportedForms]
  simp only [SmoothForm.toContMDiffSection_apply]
  rfl

namespace compactlySupportedForms

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The class of a compactly supported form in `L²Ωᵏ(M)` is the class of its section of the
bundle of forms, read in the fibres carrying the Gram metric. -/
theorem toL2Form_eq_toL2 (α : compactlySupportedForms I M k) :
    toL2Form I M k α = ContMDiffSection.toL2 (riemannianVolume I M)
      ⟨_, (contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported_iff α.val).2
        α.property⟩ := by
  apply LpSection.ext
  filter_upwards [coeFn_toL2Form α, ContMDiffSection.coeFn_toL2 (μ := riemannianVolume I M)
    ⟨_, (contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported_iff α.val).2
      α.property⟩] with x hα hs
  rw [hα, hs, WithFiberMetric.contMDiffSectionEquiv_apply,
    SmoothForm.toContMDiffSection_apply]

end compactlySupportedForms

end Comparison

namespace compactlySupportedForms

variable [IsManifold I ∞ M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

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
  have hα : α ∈ compactlySupportedForms I M k :=
    (contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported_iff α).1 (hs ▸ s.property)
  refine ⟨⟨α, hα⟩, ?_⟩
  rw [toL2Form_eq_toL2]
  exact congrArg _ (Subtype.ext hs)

end compactlySupportedForms

end TauCeti
