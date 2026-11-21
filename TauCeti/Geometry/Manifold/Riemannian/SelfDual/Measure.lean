/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.Geometry.Manifold.Riemannian.FormMetric

/-!
# Self-dual energies against the Riemannian measure

On an oriented Riemannian manifold of dimension `k + k` with `k` even,
`TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic` states its energy identities for integrals
of top forms `∫_M f vol`. This file restates one of them, the Chern–Weil identity
`∫ |α|² = 2 ∫ |α⁺|² - ∫_M α ∧ α`, against the Riemannian volume measure, through
`TauCeti.integralTopForm_smul_riemannianVolumeForm`.

## Main results

* `TauCeti.SmoothForm.integral_inner_self_eq_two_mul_sub`: **Chern–Weil against the Riemannian
  measure**, `∫ |α|² = 2 ∫ |α⁺|² - ∫_M α ∧ α` for a compactly supported smooth `k`-form `α`. For
  the curvature of a connection on a line bundle over a closed four-manifold, `∫_M α ∧ α` is a
  characteristic number, so the self-dual energy controls the whole energy.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- The Riemannian volume measure needs only a continuous metric. -/
local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Chern–Weil against the Riemannian measure.** On an oriented Riemannian manifold of dimension
`k + k` with `k` even, a compactly supported smooth `k`-form `α` has
`∫ |α|² = 2 ∫ |α⁺|² - ∫_M α ∧ α`, with the energies integrated against the Riemannian volume
measure. This combines
`TauCeti.SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_add` and
`TauCeti.SmoothForm.integralTopForm_wedge_self`. -/
theorem integral_inner_self_eq_two_mul_sub (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) {α : SmoothForm I M ℝ k} (hα : α ∈ compactlySupportedForms I M k) :
    ∫ x, alternatingFormInner (TangentSpace I x) k (α.val x) (α.val x) ∂riemannianVolume I M =
      2 * ∫ x, alternatingFormInner (TangentSpace I x) k ((selfDualPart o α).val x)
        ((selfDualPart o α).val x) ∂riemannianVolume I M -
      integralTopForm o (RoughForm.wedge α.val α.val) := by
  -- `contMDiff_alternatingFormInner` needs `C^(∞ + 1)` charts.
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  -- The energy density of a compactly supported form is continuous with compact support.
  have hconv {φ : SmoothForm I M ℝ k} (hφ : φ ∈ compactlySupportedForms I M k) :=
    integralTopForm_smul_riemannianVolumeForm o
      (φ.isSmoothForm.contMDiff_alternatingFormInner φ.isSmoothForm).continuous
      (HasCompactSupport.mono' ((mem_compactlySupportedForms I).mp hφ) fun x hx ↦
        subset_tsupport _ fun h ↦ hx (by simp only [h]; exact LinearMap.map_zero₂ _ _))
  have h₁ := integralTopForm_inner_self_smul_riemannianVolumeForm_eq_add o hα
  have h₂ := integralTopForm_wedge_self o hk hα
  rw [hconv (selfDualPart_mem_compactlySupportedForms o hα),
    hconv (antiSelfDualPart_mem_compactlySupportedForms o hα)] at h₁ h₂
  rw [hconv hα] at h₁
  linarith

end TauCeti.SmoothForm
