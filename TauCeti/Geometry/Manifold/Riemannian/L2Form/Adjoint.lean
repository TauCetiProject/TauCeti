/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# The codifferential is formally adjoint to `d` in `L²`

Through the embedding `TauCeti.compactlySupportedForms.toL2Form` of compactly supported smooth
forms into `L²Ωᵏ(M)`, the integral identities for the codifferential on an oriented boundaryless
Riemannian manifold become identities in `L²`: the codifferential `d*` is formally adjoint in
`L²` to the exterior derivative `d` on compactly supported smooth forms, and the Hodge Laplacian
`Δ = d*d + dd*` is symmetric and nonnegative there. These describe `d`, `d*` and `Δ` as unbounded
operators on `L²Ωᵏ(M)` with the compactly supported smooth forms as domain, the starting point
for their closed and self-adjoint extensions.

## Main results

* `TauCeti.compactlySupportedForms.inner_toL2Form_mextDerivₗ`: `⟪dα, β⟫ = ⟪α, d*β⟫` in `L²`.
* `TauCeti.compactlySupportedForms.inner_toL2Form_hodgeLaplacian`: `⟪Δα, β⟫ = ⟪α, Δβ⟫` in `L²`.
* `TauCeti.compactlySupportedForms.inner_toL2Form_hodgeLaplacian_self_nonneg`: `0 ≤ ⟪Δα, α⟫`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1–6.2.
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
