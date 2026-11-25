/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.WithFiberMetric

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
(`TauCeti.compactlySupportedForms.toL2Form_eq_ofCompactlySupported`). Density then follows from
density of compactly supported smooth sections in `Lᵖ` sections for `p < ∞`,
`TauCeti.LpSection.denseRange_ofCompactlySupported`.
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
  simp only [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def,
    WithFiberMetric.contMDiffSectionEquiv_apply, SmoothForm.toContMDiffSection_apply,
    SmoothForm.closure_setOf_toWithFiberMetric_ne_zero, mem_compactlySupportedForms]

namespace compactlySupportedForms

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The class of a compactly supported form in `L²Ωᵏ(M)` is the class of its section of the
bundle of forms, read in the fibres carrying the Gram metric. -/
theorem toL2Form_eq_ofCompactlySupported (α : compactlySupportedForms I M k) :
    toL2Form I M k α = LpSection.ofCompactlySupported ℝ I 2 (riemannianVolume I M)
      ⟨_, (contMDiffSectionEquiv_toContMDiffSection_mem_compactlySupported_iff α.val).2
        α.property⟩ := by
  rw [toL2Form_apply, LpSection.ofCompactlySupported_apply, LpSection.ofCompactlySupported_apply,
    LpSection.mk_eq_mk_iff]
  refine .of_forall fun x ↦ ?_
  rw [toContinuousSection_apply, WithFiberMetric.contMDiffSectionEquiv_apply,
    SmoothForm.toContMDiffSection_apply]

end compactlySupportedForms

end Comparison

namespace compactlySupportedForms

variable [IsManifold I ∞ M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- Compactly supported smooth real forms have dense image in the geometric L² space on a
Riemannian manifold, including in the presence of a boundary. -/
theorem denseRange_toL2Form : DenseRange (toL2Form I M k) := by
  refine (LpSection.denseRange_ofCompactlySupported (𝕜 := ℝ) (I := I) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (E := WithFiberMetric (formMetric I M k)) (μ := riemannianVolume I M)
    (p := 2) ENNReal.ofNat_ne_top).mono ?_
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
  rw [toL2Form_eq_ofCompactlySupported]
  exact congrArg _ (Subtype.ext hs)

end compactlySupportedForms

end TauCeti
