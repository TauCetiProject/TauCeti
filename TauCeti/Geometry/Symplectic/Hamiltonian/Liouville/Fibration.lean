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

Let `σ` be a symplectic form on a finite-dimensional Hausdorff boundaryless smooth manifold `M`
(with boundaryless model) and let `π : M → B` be a regular Lagrangian torus fibration
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`): a proper smooth submersion
with connected Lagrangian fibres, onto a smooth Hausdorff manifold `B` of dimension `n`. This file
proves that every fibre `π⁻¹(b)` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`
(`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`), which justifies the name of the
notion. It is the global form of the topological Liouville–Arnold theorem
(`TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`), which it applies to the
pulled-back coordinates of a chart of `B`.

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

/-- **The fibres of a regular Lagrangian torus fibration are tori.** Let `M` be a
finite-dimensional Hausdorff boundaryless smooth manifold (with boundaryless model) and `B` a
smooth Hausdorff manifold of dimension `n`. If `σ` is closed, so symplectic, every fibre of a
regular Lagrangian torus fibration `π : M → B` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus (h : hσ.IsLagrangianTorusFibration J π)
    (hσc : σ.IsClosed) (b : B) :
    Nonempty (π ⁻¹' {b} ≃ₜ UnitAddTorus (Fin (finrank ℝ F))) := by
  /- The proof applies the topological Liouville–Arnold theorem to `G = e ∘ κ₀ ∘ π`, where
  `κ₀ : B → F` is a smooth map which near `b` is the chart of `B` (localized by a bump function)
  and `e : F ≃ ℝⁿ` is a choice of coordinates. The components of `G` Poisson-commute because the
  fibres are Lagrangian, and their Hamiltonian vector fields are vertical, so complete because `π`
  is proper. `G` is regular along `π⁻¹(b)` because `dκ₀_b` is invertible and `π` is a submersion;
  and since `κ₀` is injective near `b`, the connected fibre `π⁻¹(b)` is exactly the connected
  component of the level `G⁻¹(G x)` through any of its points `x`. -/
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  rw [mem_preimage, mem_singleton_iff] at hx
  have : Nonempty M := ⟨x⟩
  -- A smooth map `κ₀ : B → F` with the germ of the chart at `b`, and coordinates on `F`.
  obtain ⟨κ₀, hκ₀⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := J) b
  let e : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  set G : M → Fin (finrank ℝ F) → ℝ := (e : F →L[ℝ] Fin (finrank ℝ F) → ℝ) ∘ (κ₀ ∘ π) with hG
  have hκ : ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (e ∘ κ₀) :=
    e.contDiff.comp_contMDiff κ₀.contMDiff
  have hGs : ContMDiff I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ G := hκ.comp h.contMDiff
  -- `b` is isolated in its level of `e ∘ κ₀`, since `κ₀` agrees near `b` with the chart.
  have hb : connectedComponentIn ((e ∘ κ₀) ⁻¹' {G x}) b = {b} := by
    refine connectedComponentIn_eq_singleton (by simp [hG, hx]) ?_
    filter_upwards [hκ₀, extChartAt_source_mem_nhds (I := J) b] with c hc hcs hcb
    refine (extChartAt J b).injOn hcs (mem_extChartAt_source b) ?_
    rw [← hc, ← hκ₀.self_of_nhds]
    simpa [hG, hx] using hcb
  -- The connected component of `x` in its level of `G` is the fibre of `π` through `x`.
  have hcomp : connectedComponentIn (G ⁻¹' {G x}) x = π ⁻¹' {b} := by
    refine Subset.antisymm (fun y hy ↦ ?_) ((h.isConnected_preimage_singleton b).isPreconnected
      |>.subset_connectedComponentIn (by simp [hx]) fun y hy ↦ ?_)
    · have := connectedComponentIn_mono (π x) (image_preimage_subset π ((e ∘ κ₀) ⁻¹' {G x}))
        (h.contMDiff.continuous.continuousOn.mapsTo_connectedComponentIn
          (mem_singleton (G x)) hy)
      rwa [hx, hb] at this
    · simp only [mem_preimage, mem_singleton_iff] at hy
      simp [hG, hy, hx]
  have hreg : ∀ y ∈ connectedComponentIn (G ⁻¹' {G x}) x,
      IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) G y := by
    intro y hy
    rw [hcomp, mem_preimage, mem_singleton_iff] at hy
    refine isRegularPoint_iff_surjective_mvfderiv.2 (mvfderiv_comp_surjective ?_ _ e.surjective)
    -- `d(κ₀ ∘ π)_y = dκ₀_(π y) ∘ dπ_y`, and `dκ₀_(π y)` is the invertible derivative of the chart
    -- at `b = π y`.
    have hκy : (κ₀ : B → F) =ᶠ[𝓝 (π y)] extChartAt J (π y) := by rwa [hy]
    have hinv : (mfderiv J 𝓘(ℝ, F) κ₀ (π y)).IsInvertible := by
      rw [hκy.mfderiv_eq]
      exact isInvertible_mfderiv_extChartAt (mem_extChartAt_source (π y))
    rw [mfderiv_comp y (κ₀.contMDiff.mdifferentiableAt (by simp)) (h.mdifferentiableAt y),
      ContinuousLinearMap.coe_comp]
    exact hinv.surjective.comp (h.surjective_mfderiv y)
  have hσS : σ.IsSymplectic := ⟨hσc, hσ⟩
  have hGi (i : Fin (finrank ℝ F)) : ContMDiff J 𝓘(ℝ) ∞ fun c ↦ e (κ₀ c) i :=
    contMDiff_pi_module_iff.1 hκ i
  obtain ⟨φ⟩ := hσS.nonempty_homeomorph_unitAddTorus hGs
    (fun i j y ↦ h.poissonBracket_comp_eq_zero ((hGi i).mdifferentiableAt (by simp))
      ((hGi j).mdifferentiableAt (by simp)))
    (fun i ↦ h.isCompleteVectorField_hamiltonianVectorField_comp h.isProperMap
      ((hGi i).of_le (by simp)))
    hreg (by rw [Fintype.card_fin, h.two_mul_finrank])
    (hcomp ▸ h.isCompact_preimage_singleton b)
  exact ⟨(Homeomorph.setCongr hcomp.symm).trans φ⟩

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
