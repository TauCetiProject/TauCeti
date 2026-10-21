/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Morse functions under boundaryless model transport

Passing from an arbitrary boundaryless model to its vector-space-valued atlas preserves
critical points, nondegenerate critical points, the Morse index, and the Morse property on any
subset.
These comparisons use the identical extended charts, not a new choice of Morse coordinates.
Thus self-modelled local constructions can be applied without changing the critical-point data.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti
namespace BoundarylessModel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- Critical points are unchanged by the boundaryless model transport. -/
@[simp]
theorem criticalPoints_eq (f : M → ℝ) :
    criticalPoints 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) =
      (homeomorph I M).symm ⁻¹' criticalPoints I f := by
  ext x
  rw [mem_preimage, mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero, extChartAt_eq, coe_homeomorph_symm]
  rfl

/-- Nondegenerate critical points are unchanged by the boundaryless model transport. -/
@[simp]
theorem isManifoldNondegenerateCriticalPoint_iff (f : M → ℝ) (x : BoundarylessModel I M) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) x ↔
      IsManifoldNondegenerateCriticalPoint I f ((homeomorph I M).symm x) := by
  rw [TauCeti.isManifoldNondegenerateCriticalPoint_iff,
    TauCeti.isManifoldNondegenerateCriticalPoint_iff, extChartAt_eq, coe_homeomorph_symm]
  rfl

/-- The Morse index is unchanged, since the extended coordinate expression is identical. -/
@[simp]
theorem manifoldMorseIndex_eq (f : M → ℝ) (x : BoundarylessModel I M) :
    manifoldMorseIndex 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) x =
      manifoldMorseIndex I f ((homeomorph I M).symm x) := by
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, extChartAt_eq, coe_homeomorph_symm]
  rfl

/-- Being Morse on a subset is preserved, including the smoothness requirement. -/
@[simp]
theorem isMorseOn_iff (f : M → ℝ) (s : Set M) :
    IsMorseOn 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) ((homeomorph I M).symm ⁻¹' s) ↔
      IsMorseOn I f s := by
  have hsmooth := (diffeomorph I (M := M) ∞).symm.contMDiffOn_comp_diffeomorph_iff
    (I' := 𝓘(ℝ)) (f := f) (s := (homeomorph I M).symm ⁻¹' s) le_rfl
  have hforward : ⇑(diffeomorph I (M := M) ∞).symm.symm = homeomorph I M :=
    coe_diffeomorph I ∞
  simp only [coe_diffeomorph_symm, hforward, ← preimage_comp,
    Homeomorph.symm_comp_self, preimage_id] at hsmooth
  rw [TauCeti.isMorseOn_iff, TauCeti.isMorseOn_iff, hsmooth]
  apply and_congr Iff.rfl
  constructor
  · intro h x hx
    have hx' : (homeomorph I M).symm (homeomorph I M x) ∈ s := by
      rwa [Homeomorph.symm_apply_apply]
    have h' := h (homeomorph I M x) hx'
    rw [extChartAt_eq, isManifoldNondegenerateCriticalPoint_iff,
      Homeomorph.symm_apply_apply, coe_homeomorph_symm, coe_homeomorph] at h'
    exact h'
  · intro h x hx
    rw [isManifoldNondegenerateCriticalPoint_iff]
    intro hcrit
    apply h ((homeomorph I M).symm x) hx
    rw [extChartAt_eq] at hcrit
    rw [coe_homeomorph_symm] at hcrit ⊢
    exact hcrit

/-- Global Morse functions are unchanged by replacing a boundaryless model by its vector space. -/
@[simp]
theorem isMorse_iff (f : M → ℝ) :
    IsMorse 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) ↔ IsMorse I f := by
  rw [← isMorseOn_univ, ← isMorseOn_univ]
  simpa only [preimage_univ] using isMorseOn_iff I f univ

end BoundarylessModel
end TauCeti
