/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.FormMetric
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.MeasureTheory.Function.LpSection.Basic
public import TauCeti.Topology.VectorBundle.Riemannian.WithFiberMetric
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

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
volume charges every nonempty open set. Through it, the integral identities for the
codifferential on an oriented boundaryless Riemannian manifold become identities in `L²`: the
codifferential `d*` is formally adjoint in `L²` to the exterior derivative `d` on compactly
supported smooth forms, and the Hodge Laplacian `Δ = d*d + dd*` is symmetric and nonnegative
there. These describe `d`, `d*` and `Δ` as unbounded operators on `L²Ωᵏ(M)` with the compactly
supported smooth forms as domain, the starting point for their closed and self-adjoint
extensions.

## Main definitions

* `TauCeti.L2Form I M k`: the Hilbert space of square-integrable `k`-forms.
* `TauCeti.compactlySupportedForms.toL2Form`: the class in `L²Ωᵏ(M)` of a compactly supported
  smooth form.

## Main results

* `TauCeti.compactlySupportedForms.inner_toL2Form`: the `L²` inner product of compactly supported
  smooth forms is `∫ ⟨α x, β x⟩ d(vol_g)`.
* `TauCeti.compactlySupportedForms.toL2Form_injective`: distinct compactly supported smooth forms
  have distinct classes.
* `TauCeti.compactlySupportedForms.inner_toL2Form_mextDerivₗ`: `⟪dα, β⟫ = ⟪α, d*β⟫` in `L²`.
* `TauCeti.compactlySupportedForms.inner_toL2Form_hodgeLaplacian`: `⟪Δα, β⟫ = ⟪α, Δβ⟫` in `L²`.
* `TauCeti.compactlySupportedForms.inner_toL2Form_hodgeLaplacian_self_nonneg`: `0 ≤ ⟪Δα, α⟫`.

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

section Oriented

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {m l : ℕ}

/-- The Riemannian volume and the `L²` metric need only a continuous metric. -/
local instance instIsContinuousRiemannianBundleTangentSpaceL2Form :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

namespace compactlySupportedForms

/-- On an oriented manifold the `L²` inner product of compactly supported smooth forms is the
integral of the top form `⟨α, β⟩ vol`. -/
theorem integralTopForm_inner_smul_riemannianVolumeForm_eq_inner_toL2Form
    (o : Manifold.Orientation I M (Fin m))
    (α β : compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) k (α.val.val x) (β.val.val x) •
          riemannianVolumeForm o x) =
      ⟪toL2Form I M k α, toL2Form I M k β⟫_ℝ := by
  -- `contMDiff_alternatingFormInner` needs `C^(∞ + 1)` charts.
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  rw [inner_toL2Form, integralTopForm_smul_riemannianVolumeForm o
    (α.val.isSmoothForm.contMDiff_alternatingFormInner β.val.isSmoothForm).continuous
    (hasCompactSupport_of_compactlySupportedForms α fun x h ↦ by simp [h])]

variable [BoundarylessManifold I M] [T2Space M]

/-- **The codifferential is formally adjoint in `L²` to the exterior derivative on compactly
supported smooth forms**: on an oriented boundaryless Riemannian manifold,
`⟪dα, β⟫ = ⟪α, d*β⟫` in `L²` for compactly supported smooth forms `α` of degree `k` and `β` of
degree `k + 1`. -/
theorem inner_toL2Form_mextDerivₗ (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (α : compactlySupportedForms I M k) (β : compactlySupportedForms I M (k + 1)) :
    ⟪toL2Form I M (k + 1) (mextDerivₗ I M k α), toL2Form I M (k + 1) β⟫_ℝ =
      ⟪toL2Form I M k α, toL2Form I M k (codifferential o hkl β)⟫_ℝ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rw [← integralTopForm_inner_smul_riemannianVolumeForm_eq_inner_toL2Form o,
    ← integralTopForm_inner_smul_riemannianVolumeForm_eq_inner_toL2Form o, coe_mextDerivₗ,
    coe_codifferential]
  exact SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential o hkl α β
      (.inl α.property)

/-- **The Hodge Laplacian is symmetric in `L²`**: on an oriented boundaryless Riemannian
manifold, `⟪Δα, β⟫ = ⟪α, Δβ⟫` for compactly supported smooth `k`-forms `α` and `β`. -/
theorem inner_toL2Form_hodgeLaplacian (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α β : compactlySupportedForms I M k) :
    ⟪toL2Form I M k (hodgeLaplacian o hkl α), toL2Form I M k β⟫_ℝ =
      ⟪toL2Form I M k α, toL2Form I M k (hodgeLaplacian o hkl β)⟫_ℝ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rw [← integralTopForm_inner_smul_riemannianVolumeForm_eq_inner_toL2Form o,
    ← integralTopForm_inner_smul_riemannianVolumeForm_eq_inner_toL2Form o, coe_hodgeLaplacian,
    coe_hodgeLaplacian]
  exact SmoothForm.integralTopForm_inner_hodgeLaplacian_eq_inner_hodgeLaplacian o hkl α β
    (.inl α.property)

/-- **The Hodge Laplacian is nonnegative in `L²`**: on an oriented boundaryless Riemannian
manifold, `0 ≤ ⟪Δα, α⟫` for every compactly supported smooth form `α`. -/
theorem inner_toL2Form_hodgeLaplacian_self_nonneg (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : compactlySupportedForms I M k) :
    0 ≤ ⟪toL2Form I M k (hodgeLaplacian o hkl α), toL2Form I M k α⟫_ℝ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rw [← integralTopForm_inner_smul_riemannianVolumeForm_eq_inner_toL2Form o, coe_hodgeLaplacian]
  exact SmoothForm.integralTopForm_inner_hodgeLaplacian_self_nonneg o hkl α.property

end compactlySupportedForms

end Oriented

end TauCeti
