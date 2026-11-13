/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Torus
public import TauCeti.Geometry.Symplectic.Lagrangian.Fibration
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
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
(`TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`). A smooth map
`κ : B → ℝⁿ` which near `b` is a chart of `B` (localized by a bump function) pulls back to the
family `F = κ ∘ π`. Its components Poisson-commute because the fibres are Lagrangian
(`IsLagrangianFibration.poissonBracket_comp_eq_zero`); their Hamiltonian vector fields are
vertical, so complete because `π` is proper
(`IsLagrangianFibration.isCompleteVectorField_hamiltonianVectorField_comp`); `F` is regular along
`π⁻¹(b)` because `dκ_b` is invertible and `π` is a submersion; and since `κ` is injective near `b`,
the connected compact fibre `π⁻¹(b)` is exactly the connected component of the level
`F⁻¹(F x)` through any of its points `x`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

/-- **The fibres of a regular Lagrangian torus fibration are tori.** If `σ` is closed, so
symplectic, every fibre of a regular Lagrangian torus fibration `π : M → B` over a Hausdorff
manifold of dimension `n` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus (h : hσ.IsLagrangianTorusFibration J π)
    (hσc : σ.IsClosed) (b : B) :
    Nonempty (π ⁻¹' {b} ≃ₜ UnitAddTorus (Fin (finrank ℝ F))) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  rw [mem_preimage, mem_singleton_iff] at hx
  subst hx
  have : Nonempty M := ⟨x⟩
  -- A smooth map `κ₀ : B → F` with the germ of the chart at `π x`, and coordinates on `F`.
  obtain ⟨κ₀, hκ₀⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := J) (π x)
  let e : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  set G : M → Fin (finrank ℝ F) → ℝ := ((e : F →L[ℝ] Fin (finrank ℝ F) → ℝ) ∘ κ₀) ∘ π
  have hκ : ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (e ∘ κ₀) :=
    e.contDiff.comp_contMDiff κ₀.contMDiff
  have hGs : ContMDiff I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ G := hκ.comp h.contMDiff
  -- `κ₀` is injective near `π x`: it agrees there with the chart.
  obtain ⟨W, hWsub, hWo, hbW⟩ := mem_nhds_iff.1
    (hκ₀.and (extChartAt_source_mem_nhds (I := J) (π x)))
  have hinj : InjOn (e ∘ κ₀) W := fun c hc d hd hcd ↦ by
    refine (extChartAt J (π x)).injOn (hWsub hc).2 (hWsub hd).2 ?_
    rw [← (hWsub hc).1, ← (hWsub hd).1]
    exact e.injective hcd
  have hcomp : connectedComponentIn (G ⁻¹' {G x}) x = π ⁻¹' {π x} :=
    (h.isConnected_preimage_singleton (π x)).isPreconnected.connectedComponentIn_preimage_comp_eq
      h.contMDiff.continuous hWo hbW hinj
  have hreg : ∀ y ∈ connectedComponentIn (G ⁻¹' {G x}) x,
      IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) G y := by
    intro y hy
    rw [hcomp, mem_preimage, mem_singleton_iff] at hy
    refine IsRegularPoint.comp (isRegularPoint_iff_surjective_mvfderiv.2
      (mvfderiv_comp_surjective ?_ (e : F →L[ℝ] Fin (finrank ℝ F) → ℝ) e.surjective))
      (isRegularPoint_iff.2 (h.surjective_mfderiv y))
    -- `dκ₀` at `π y = π x` is the derivative of the chart there.
    rw [hy, hκ₀.mfderiv_eq, mfderiv_extChartAt_self]
    exact surjective_id
  have hσS : σ.IsSymplectic := ⟨hσc, hσ⟩
  have hGi (i : Fin (finrank ℝ F)) : ContMDiff J 𝓘(ℝ) ∞ fun c ↦ e (κ₀ c) i :=
    contMDiff_pi_module_iff.1 hκ i
  obtain ⟨φ⟩ := hσS.nonempty_homeomorph_unitAddTorus hGs
    (fun i j y ↦ h.poissonBracket_comp_eq_zero ((hGi i).mdifferentiableAt (by simp))
      ((hGi j).mdifferentiableAt (by simp)))
    (fun i ↦ h.isCompleteVectorField_hamiltonianVectorField_comp h.isProperMap
      ((hGi i).of_le (by simp)))
    hreg (by rw [Fintype.card_fin, h.two_mul_finrank])
    (hcomp ▸ h.isCompact_preimage_singleton (π x))
  exact ⟨(Homeomorph.setCongr hcomp.symm).trans φ⟩

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
