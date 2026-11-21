/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.Riemannian.FormMetric
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.Section.L2.Basic
public import TauCeti.Topology.VectorBundle.Riemannian.WithFiberMetric
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Square-integrable differential forms

On a manifold `M` with a continuous Riemannian metric, the fibres of the bundle of real
`k`-forms carry the Gram inner product `TauCeti.alternatingFormInner`, which varies continuously
(`TauCeti.formMetric`). The Hilbert space `L²Ωᵏ(M)` of square-integrable `k`-forms,
`TauCeti.L2Form I M k`, is the space of square-integrable sections of the bundle of `k`-forms
for this metric and the Riemannian volume measure, with inner product
`⟪α, β⟫ = ∫ ⟨α x, β x⟩ d(vol_g)`. It is complete since the bundle has finite rank.

A compactly supported smooth form, read in the fibres carrying the Gram metric, is a compactly
supported continuous section (`TauCeti.compactlySupportedForms.toContinuousSection`), and so
defines an element of `L²Ωᵏ(M)` through `ContMDiffSection.toL2`
(`TauCeti.compactlySupportedForms.toL2Form`); this embedding is injective since the Riemannian
volume charges every nonempty open set. The `L²` adjointness of the codifferential is in
`TauCeti.Geometry.Manifold.Riemannian.L2Form.Adjoint`.

## Main definitions

* `TauCeti.L2Form I M k`: the Hilbert space of square-integrable `k`-forms.
* `TauCeti.compactlySupportedForms.toContinuousSection`: a compactly supported smooth form as a
  compactly supported continuous section of the bundle of forms with the Gram metric.
* `TauCeti.compactlySupportedForms.toL2Form`: the class in `L²Ωᵏ(M)` of a compactly supported
  smooth form.

## Main results

* `TauCeti.compactlySupportedForms.inner_toL2Form`: the `L²` inner product of compactly supported
  smooth forms is `∫ ⟨α x, β x⟩ d(vol_g)`.
* `TauCeti.compactlySupportedForms.toL2Form_injective`: distinct compactly supported smooth forms
  have distinct classes.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1–6.2.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

section Continuous

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A smooth form, read in the fibres carrying the Gram metric, is a continuous section. -/
private theorem continuous_toWithFiberMetric (α : SmoothForm I M ℝ k) :
    Continuous fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
      (E := WithFiberMetric (formMetric I M k)) x
      (WithFiberMetric.toWithFiberMetric _ x (α.val x)) :=
  (WithFiberMetric.continuous_totalSpaceMk_toWithFiberMetric_iff _).2
    α.isSmoothForm.contMDiff.continuous

section L2

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (I M k) in
/-- The Hilbert space `L²Ωᵏ(M)` of square-integrable real `k`-forms on a manifold with a
continuous Riemannian metric: the square-integrable sections of the bundle of `k`-forms, for the
Gram metric `TauCeti.formMetric` on its fibres and the Riemannian volume measure, modulo equality
almost everywhere. Its inner product is `⟪α, β⟫ = ∫ ⟨α x, β x⟩ d(vol_g)`. -/
abbrev L2Form : Type _ :=
  LpSection ℝ (E [⋀^Fin k]→L[ℝ] ℝ) (WithFiberMetric (formMetric I M k)) 2 (riemannianVolume I M)

end L2

namespace compactlySupportedForms

variable (I M k) in
/-- A compactly supported smooth `k`-form, read in the fibres carrying the Gram metric, as a
compactly supported continuous section of the bundle of `k`-forms. -/
def toContinuousSection : compactlySupportedForms I M k →ₗ[ℝ]
    ContMDiffSection.compactlySupported I (E [⋀^Fin k]→L[ℝ] ℝ) 0
      (WithFiberMetric (formMetric I M k)) where
  toFun α := ⟨⟨fun x ↦ WithFiberMetric.toWithFiberMetric _ x (α.val.val x),
    contMDiff_zero_iff.2 (continuous_toWithFiberMetric α.val)⟩, by
      rw [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def]
      convert (mem_compactlySupportedForms I).1 α.property using 1
      simp only [WithFiberMetric.toWithFiberMetric_apply]
      rfl⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The continuous section of a compactly supported form evaluates to the form, read in the
fibre carrying the Gram metric. -/
@[simp]
theorem toContinuousSection_apply (α : compactlySupportedForms I M k) (x : M) :
    (toContinuousSection I M k α : Cₛ^0⟮I; E [⋀^Fin k]→L[ℝ] ℝ,
      WithFiberMetric (formMetric I M k)⟯) x =
      WithFiberMetric.toWithFiberMetric _ x (α.val.val x) := by
  simp [toContinuousSection]

/-- A compactly supported form is determined by its continuous section. -/
theorem toContinuousSection_injective : Function.Injective (toContinuousSection I M k) := by
  intro α β h
  refine Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_
  simpa using congrArg (fun s : ContMDiffSection.compactlySupported I (E [⋀^Fin k]→L[ℝ] ℝ) 0
    (WithFiberMetric (formMetric I M k)) ↦ (s : Cₛ^0⟮I; E [⋀^Fin k]→L[ℝ] ℝ,
      WithFiberMetric (formMetric I M k)⟯) x) h

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (I M k) in
/-- The class in `L²Ωᵏ(M)` of a compactly supported smooth `k`-form: the class of its
continuous section. -/
def toL2Form : compactlySupportedForms I M k →ₗ[ℝ] L2Form I M k :=
  ContMDiffSection.toL2 (riemannianVolume I M) ∘ₗ toContinuousSection I M k

/-- The class of a compactly supported smooth form is represented by the form itself. -/
theorem coeFn_toL2Form (α : compactlySupportedForms I M k) :
    ∀ᵐ x ∂riemannianVolume I M,
      toL2Form I M k α x = WithFiberMetric.toWithFiberMetric _ x (α.val.val x) := by
  filter_upwards [ContMDiffSection.coeFn_toL2 (μ := riemannianVolume I M)
    (toContinuousSection I M k α)] with x hx
  rw [toL2Form, LinearMap.comp_apply, hx, toContinuousSection_apply]

/-- The `L²` inner product of compactly supported smooth forms is the integral of their
pointwise Gram inner product against the Riemannian volume. -/
theorem inner_toL2Form (α β : compactlySupportedForms I M k) :
    ⟪toL2Form I M k α, toL2Form I M k β⟫_ℝ =
      ∫ x, alternatingFormInner (TangentSpace I x) k (α.val.val x) (β.val.val x) ∂riemannianVolume I
          M := by
  simp only [toL2Form, LinearMap.comp_apply, ContMDiffSection.inner_toL2_left]
  refine integral_congr_ae
    ((ContMDiffSection.coeFn_toL2 (toContinuousSection I M k β)).mono fun x hx ↦ ?_)
  simp [hx]

/-- Distinct compactly supported smooth forms have distinct classes in `L²Ωᵏ(M)`, because the
Riemannian volume charges every nonempty open set. -/
theorem toL2Form_injective : Function.Injective (toL2Form I M k) :=
  ContMDiffSection.toL2_injective.comp toContinuousSection_injective

end compactlySupportedForms

end Continuous

end TauCeti
