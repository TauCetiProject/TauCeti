/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
public import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# Lagrangian maps under constant rescaling

Nonzero real rescaling of the ambient two-form leaves isotropic, coisotropic and Lagrangian
tangent images unchanged. It therefore preserves Lagrangian immersions, with the same smooth
immersion and dimension condition. These facts apply to embedded submanifolds through any smooth
embedding parametrizing them.

For an exact Lagrangian map with `f*θ = dh`, scaling the ambient primitive to `c • θ` scales its
specified primitive function to `c • h`. Both implications hold for every nonzero real `c`;
positivity is unnecessary. The ambient identity `σ = -dθ` scales in the same way, as recorded in
`TauCeti.Geometry.Symplectic.Manifold.Rescale`.

The conventions follow McDuff--Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : N → M}

/-- Isotropic tangent images are unchanged by nonzero constant rescaling. -/
@[simp]
theorem isIsotropicMap_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsIsotropicMap J f ↔ hσ.IsIsotropicMap J f := by
  simp only [isIsotropicMap_iff_forall]
  refine forall_congr' fun x ↦ ?_
  rw [hσ.symplecticFormAt_smul c hc, SymplecticForm.isIsotropic_rescale_iff]

/-- Coisotropic tangent images are unchanged by nonzero constant rescaling. -/
@[simp]
theorem isCoisotropicMap_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsCoisotropicMap J f ↔ hσ.IsCoisotropicMap J f := by
  simp only [isCoisotropicMap_iff]
  refine forall_congr' fun x ↦ ?_
  rw [hσ.symplecticFormAt_smul c hc, SymplecticForm.isCoisotropic_rescale_iff]

/-- Lagrangian tangent images are unchanged by nonzero constant rescaling. -/
@[simp]
theorem isLagrangianMap_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsLagrangianMap J f ↔ hσ.IsLagrangianMap J f := by
  simp only [isLagrangianMap_iff_forall]
  refine forall_congr' fun x ↦ ?_
  rw [hσ.symplecticFormAt_smul c hc, SymplecticForm.isLagrangian_rescale_iff]

/-- Nonzero constant rescaling preserves and reflects Lagrangian immersions. -/
@[simp]
theorem isLagrangianImmersion_smul_iff [FiniteDimensional ℝ E] (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsLagrangianImmersion J f ↔ hσ.IsLagrangianImmersion J f := by
  constructor <;> intro h
  · exact ⟨h.isImmersion, (hσ.isIsotropicMap_smul_iff c hc).1 h.isIsotropicMap,
      h.two_mul_finrank⟩
  · exact ⟨h.isImmersion, (hσ.isIsotropicMap_smul_iff c hc).2 h.isIsotropicMap,
      h.two_mul_finrank⟩

variable {hσ}

/-- An exact Lagrangian map stays exact when the form, ambient primitive and specified primitive
function are rescaled by the same nonzero constant. -/
theorem IsExactLagrangianMap.smul {θ : SmoothForm I M ℝ 1} {h : N → ℝ}
    (hL : hσ.IsExactLagrangianMap J θ f h) (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsExactLagrangianMap J (c • θ) f (c • h) := by
  refine ⟨(hσ.isLagrangianMap_smul_iff c hc).2 hL.isLagrangianMap,
    (contDiff_id.const_smul c).comp_contMDiff hL.contMDiff_primitive, ?_⟩
  rw [SmoothForm.smul_toRoughForm, mpullback_smul, hL.mpullback_eq, RoughForm.ofFunction_smul,
    mextDeriv_smul]

/-- Simultaneous rescaling of an ambient primitive and a specified primitive function preserves
and reflects exactness. -/
@[simp]
theorem isExactLagrangianMap_smul_iff {θ : SmoothForm I M ℝ 1} {h : N → ℝ}
    (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsExactLagrangianMap J (c • θ) f (c • h) ↔
      hσ.IsExactLagrangianMap J θ f h := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ hL.smul c hc⟩
  have hL' := hL.smul c⁻¹ (inv_ne_zero hc)
  simpa only [inv_smul_smul₀ hc] using hL'

end TauCeti.SmoothTwoForm.IsNondegenerate
