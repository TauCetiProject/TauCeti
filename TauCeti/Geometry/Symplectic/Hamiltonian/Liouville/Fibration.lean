/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Torus
public import TauCeti.Geometry.Symplectic.Lagrangian.Fibration
public import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Submersion
import TauCeti.Topology.Connected.Basic

/-!
# The fibres of a regular Lagrangian torus fibration are tori

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`): a
proper smooth submersion with connected Lagrangian fibres, onto a Hausdorff manifold `B` of
dimension `n`. This file proves that every fibre `π⁻¹(b)` is homeomorphic to the torus
`(ℝ / ℤ)ⁿ` (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`), which justifies the
name of the notion.

The proof reduces to the topological Liouville–Arnold theorem for `n` Poisson-commuting functions
(`TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`). The smooth map
`κ = TauCeti.chartCoord J b : B → ℝⁿ`, which near `b` is a chart of `B`, pulls back to the
family `F = κ ∘ π`. Its components Poisson-commute because the fibres are Lagrangian
(`IsLagrangianFibration.poissonBracket_comp_eq_zero`); `F` is regular along
`π⁻¹(b)` because `dκ_b` is invertible and `π` is a submersion; and since `κ` is injective near `b`,
the connected compact fibre `π⁻¹(b)` is exactly the connected component of the level
`F⁻¹(F x)` through any of its points `x`. These facts about `κ ∘ π` are stated separately
(`IsLagrangianFibration.poissonBracket_chartCoord_comp`,
`IsLagrangianFibration.isRegularPoint_chartCoord_comp` and
`IsLagrangianTorusFibration.connectedComponentIn_preimage_chartCoord_comp_eq`), so that the
cotangent action on the fibres can be built from the same coordinates.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

namespace IsLagrangianFibration

variable (h : hσ.IsLagrangianFibration J π)
include h

/-- The coordinates `chartCoord J b` of the base near `b`, pulled back to `M`, are smooth. -/
theorem contMDiff_chartCoord_comp (b : B) :
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (chartCoord J b ∘ π) :=
  (contMDiff_chartCoord J b).comp h.contMDiff

/-- The coordinates `chartCoord J b` of the base, pulled back to `M`, are regular along the fibre
over `b`: the derivative of `chartCoord J b` at `b` is invertible and `π` is a submersion. -/
theorem isRegularPoint_chartCoord_comp {b : B} {y : M} (hy : π y = b) :
    IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (chartCoord J b ∘ π) y := by
  refine IsRegularPoint.comp (isRegularPoint_iff_surjective_mvfderiv.2
    fun w ↦ ⟨(Module.finBasis ℝ F).equivFunL.symm w, ?_⟩)
    (isRegularPoint_iff.2 (h.surjective_mfderiv y))
  rw [hy]
  exact (mvfderiv_chartCoord_apply J b _).trans
    ((Module.finBasis ℝ F).equivFunL.apply_symm_apply w)

variable [FiniteDimensional ℝ E] in
/-- The coordinates `chartCoord J b` of the base, pulled back to `M`, Poisson-commute, because the
fibres are Lagrangian. -/
theorem poissonBracket_chartCoord_comp (b : B) (i j : Fin (finrank ℝ F)) (y : M) :
    σ.poissonBracket ((chartCoord J b ∘ π) · i) ((chartCoord J b ∘ π) · j) y = 0 :=
  h.poissonBracket_comp_eq_zero
    ((contMDiff_pi_module_iff.1 (contMDiff_chartCoord J b) i).mdifferentiableAt (by simp))
    ((contMDiff_pi_module_iff.1 (contMDiff_chartCoord J b) j).mdifferentiableAt (by simp))

end IsLagrangianFibration

namespace IsLagrangianTorusFibration

/-- The fibre of a regular Lagrangian torus fibration through `x` is the connected component of
`x` in its level of the pulled-back coordinates `chartCoord J b ∘ π`, since `chartCoord J b` is
injective near `b`. -/
theorem connectedComponentIn_preimage_chartCoord_comp_eq (h : hσ.IsLagrangianTorusFibration J π)
    {b : B} {x : M} (hx : π x = b) :
    connectedComponentIn ((chartCoord J b ∘ π) ⁻¹' {(chartCoord J b ∘ π) x}) x = π ⁻¹' {b} := by
  obtain ⟨W, hWo, hbW, hinj⟩ := exists_isOpen_injOn_chartCoord J b
  subst hx
  exact (h.isConnected_preimage_singleton (π x)).isPreconnected
    |>.connectedComponentIn_preimage_comp_eq h.contMDiff.continuous hWo hbW hinj

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- **The fibres of a regular Lagrangian torus fibration are tori.** If `σ` is closed, so
symplectic, every fibre of a regular Lagrangian torus fibration `π : M → B` over a Hausdorff
manifold of dimension `n` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus (h : hσ.IsLagrangianTorusFibration J π)
    (hσc : σ.IsClosed) (b : B) :
    Nonempty (π ⁻¹' {b} ≃ₜ UnitAddTorus (Fin (finrank ℝ F))) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have : Nonempty M := ⟨x⟩
  have hcomp := h.connectedComponentIn_preimage_chartCoord_comp_eq hx
  obtain ⟨φ⟩ := (⟨hσc, hσ⟩ : σ.IsSymplectic).nonempty_homeomorph_unitAddTorus
    (h.contMDiff_chartCoord_comp b) (h.poissonBracket_chartCoord_comp b)
    (fun y hy ↦ h.isRegularPoint_chartCoord_comp (by rwa [hcomp] at hy))
    (by rw [Fintype.card_fin, h.two_mul_finrank]) (hcomp ▸ h.isCompact_preimage_singleton b)
  exact ⟨(Homeomorph.setCongr hcomp.symm).trans φ⟩

end IsLagrangianTorusFibration

end TauCeti.SmoothTwoForm.IsNondegenerate
