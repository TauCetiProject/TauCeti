/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
import TauCeti.Geometry.Manifold.Boundary.Invariance

/-!
# Boundary points in charts of the closed upper half-plane

Let `X` be a charted space modelled on the closed upper half-plane, for instance a Riemann
surface with boundary. Read in the extended chart `φ.extend closedUpperHalfPlaneModel` of any
chart `φ` of `X`, the boundary points of `X` are exactly the real points of the extended target
(`OpenPartialHomeomorph.isBoundaryPoint_extend_symm_iff`). Consequently, over an open set of `X`
without boundary points, the coordinate domain of a chart is open in `ℂ`
(`OpenPartialHomeomorph.isOpen_extend_target_inter_preimage_of_subset_compl`), the interior
counterpart of `OpenPartialHomeomorph.exists_isOpen_extend_target_inter_preimage`.

Both are topological statements: they hold for every chart, in an atlas or not, by the
topological invariance of the boundary (`OpenPartialHomeomorph.isBoundaryPoint_iff`).
-/

public section

open Set

namespace OpenPartialHomeomorph

open TauCeti ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]

/-- A point of the extended target of a chart of a space modelled on the closed upper half-plane
reads a boundary point exactly when it is real. -/
theorem isBoundaryPoint_extend_symm_iff (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane)
    {z : ℂ} (hz : z ∈ (φ.extend closedUpperHalfPlaneModel).target) :
    closedUpperHalfPlaneModel.IsBoundaryPoint ((φ.extend closedUpperHalfPlaneModel).symm z) ↔
      z.im = 0 := by
  rw [extend_target, range_closedUpperHalfPlaneModel, mem_inter_iff, mem_preimage,
    mem_ofPred_eq (p := fun z : ℂ ↦ 0 ≤ z.im)] at hz
  have h := φ.isBoundaryPoint_iff closedUpperHalfPlaneModel closedUpperHalfPlaneModel rfl
    (φ.map_target hz.1)
  simpa [φ.right_inv hz.1, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz.2] using h

/-- Over an open set `t` without boundary points, the coordinate domain of a chart `φ` of a space
modelled on the closed upper half-plane is open in `ℂ`: it is relatively open in the closed upper
half-plane and avoids the real axis. -/
theorem isOpen_extend_target_inter_preimage_of_subset_compl
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) {t : Set X} (ht : IsOpen t)
    (htb : t ⊆ (closedUpperHalfPlaneModel.boundary X)ᶜ) :
    IsOpen ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t) := by
  obtain ⟨Ω, hΩ, hD⟩ := φ.exists_isOpen_extend_target_inter_preimage ht
  -- The coordinate domain over `t` is `Ω ∩ {0 ≤ im}` and has no real points, since a real point
  -- of the extended target reads a boundary point of `X`; so it is `Ω ∩ {0 < im}`.
  have hset : (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t = Ω ∩ {z : ℂ | 0 < z.im} := by
    refine Set.ext fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · have hzD := hz
      rw [mem_inter_iff, mem_preimage] at hzD
      rw [hD, mem_inter_iff, mem_ofPred_eq (p := fun z : ℂ ↦ 0 ≤ z.im)] at hz
      rw [mem_inter_iff, mem_ofPred_eq (p := fun z : ℂ ↦ 0 < z.im)]
      refine ⟨hz.1, lt_of_le_of_ne hz.2 fun h0 ↦ ?_⟩
      -- `closedUpperHalfPlaneModel.boundary X` is by definition the set of boundary points.
      exact htb hzD.2 ((φ.isBoundaryPoint_extend_symm_iff hzD.1).2 h0.symm)
    · rw [mem_inter_iff, mem_ofPred_eq (p := fun z : ℂ ↦ 0 < z.im)] at hz
      rw [hD, mem_inter_iff, mem_ofPred_eq (p := fun z : ℂ ↦ 0 ≤ z.im)]
      exact ⟨hz.1, hz.2.le⟩
  rw [hset]
  exact hΩ.inter (isOpen_lt continuous_const Complex.continuous_im)

end OpenPartialHomeomorph
