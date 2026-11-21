/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.Riemannian.FormMetric
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.MeasureTheory.Function.LpSection.Basic
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

A compactly supported smooth form defines an element of `L²Ωᵏ(M)`
(`TauCeti.compactlySupportedForms.toL2Form`); this embedding is injective since the Riemannian
volume charges every nonempty open set. The `L²` adjointness of the codifferential is in
`TauCeti.Geometry.Manifold.Riemannian.L2Form.Adjoint`.

## Main definitions

* `TauCeti.L2Form I M k`: the Hilbert space of square-integrable `k`-forms.
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

/-- The Gram norm of a smooth form is continuous. -/
private theorem continuous_norm_toWithFiberMetric (α : SmoothForm I M ℝ k) :
    Continuous fun x ↦ ‖WithFiberMetric.toWithFiberMetric (formMetric I M k) x (α.val x)‖ :=
  Continuous.norm_bundle_of_continuousFiberNorm (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (continuous_toWithFiberMetric α)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (I M k) in
/-- The Hilbert space `L²Ωᵏ(M)` of square-integrable real `k`-forms on a manifold with a
continuous Riemannian metric: the square-integrable sections of the bundle of `k`-forms, for the
Gram metric `TauCeti.formMetric` on its fibres and the Riemannian volume measure, modulo equality
almost everywhere. Its inner product is `⟪α, β⟫ = ∫ ⟨α x, β x⟩ d(vol_g)`. -/
abbrev L2Form : Type _ :=
  LpSection ℝ (E [⋀^Fin k]→L[ℝ] ℝ) (WithFiberMetric (formMetric I M k)) 2 (riemannianVolume I M)

namespace compactlySupportedForms

variable (I M k) in
/-- The class in `L²Ωᵏ(M)` of a compactly supported smooth `k`-form. -/
def toL2Form : compactlySupportedForms I M k →ₗ[ℝ] L2Form I M k where
  toFun α := LpSection.mk _ (.of_continuous (continuous_toWithFiberMetric α.val))
    ((continuous_norm_toWithFiberMetric α.val).memLp_of_hasCompactSupport
      (hasCompactSupport_of_compactlySupportedForms α fun x h ↦ by simp [h]))
  map_add' _ _ := by
    rw [LpSection.mk_add, LpSection.mk_eq_mk_iff]
    exact .of_forall fun _ ↦ map_add _ _ _
  map_smul' _ _ := by
    rw [LpSection.mk_smul, LpSection.mk_eq_mk_iff]
    exact .of_forall fun _ ↦ by simp

/-- The class of a compactly supported smooth form is represented by the form itself. -/
theorem coeFn_toL2Form (α : compactlySupportedForms I M k) :
    ∀ᵐ x ∂riemannianVolume I M,
      toL2Form I M k α x = WithFiberMetric.toWithFiberMetric _ x (α.val.val x) :=
  LpSection.coeFn_mk _ _

/-- The `L²` inner product of compactly supported smooth forms is the integral of their
pointwise Gram inner product against the Riemannian volume. -/
theorem inner_toL2Form (α β : compactlySupportedForms I M k) :
    ⟪toL2Form I M k α, toL2Form I M k β⟫_ℝ =
      ∫ x, alternatingFormInner (TangentSpace I x) k (α.val.val x) (β.val.val x) ∂riemannianVolume I
          M := by
  simp [toL2Form]

/-- Distinct compactly supported smooth forms have distinct classes in `L²Ωᵏ(M)`, because the
Riemannian volume charges every nonempty open set. -/
theorem toL2Form_injective : Function.Injective (toL2Form I M k) := by
  refine (injective_iff_map_eq_zero _).2 fun α hα ↦ Subtype.ext <| Subtype.ext ?_
  -- The continuous fibre norm of `α` vanishes almost everywhere, hence everywhere.
  have hae : (fun x ↦ ‖WithFiberMetric.toWithFiberMetric (formMetric I M k) x (α.val.val x)‖) =ᵐ[
      riemannianVolume I M] fun _ ↦ 0 := by
    filter_upwards [coeFn_toL2Form α, (LpSection.ext_iff _ _).1 hα,
      LpSection.coeFn_zero (𝕜 := ℝ) (F := E [⋀^Fin k]→L[ℝ] ℝ)
        (E := WithFiberMetric (formMetric I M k)) (μ := riemannianVolume I M)] with x h₁ h₂ h₃
    rw [← h₁, h₂, h₃, norm_zero]
  funext x
  simpa using congr_fun ((continuous_norm_toWithFiberMetric α.val).ae_eq_iff_eq _
    continuous_const |>.1 hae) x

end compactlySupportedForms

end Continuous

end TauCeti
