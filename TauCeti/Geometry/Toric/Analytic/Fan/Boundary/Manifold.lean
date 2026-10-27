/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.NormalForm
public import Mathlib.Geometry.Manifold.SmoothEmbedding

import TauCeti.Geometry.Manifold.LinearSlice

/-!
# Complex manifolds on invariant toric boundary components

Each ray-indexed boundary component of a regular toric fan realization, with its original
subspace topology, admits a complex manifold structure of dimension one less than the rank of
the lattice. Its inclusion into the realization is a holomorphic smooth embedding. Combined
with `TauCeti.Toric.Fan.isClosed_analyticBoundaryComponent`, this identifies the components as
closed embedded complex hypersurfaces, including at intersections with other components.

The atlas is induced by the coordinate-hyperplane normal form of the toric boundary, using
`TauCeti.linearSliceChartedSpace`. No choice of a basis of the lattice is required from callers.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2 and 4.1.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- Each invariant boundary component, on its actual subtype with the subspace topology, admits
a complex manifold structure of dimension `rank N - 1` for which the inclusion is a holomorphic
smooth embedding. This includes points where several boundary components intersect. -/
theorem exists_isManifold_analyticBoundaryComponent_isSmoothEmbedding (ρ : Φ.Ray) :
    letI := Φ.analyticChartedSpace hΦ
    ∃ C : ChartedSpace (Fin (Module.finrank ℤ N - 1) → ℂ)
        (Φ.analyticBoundaryComponent hΦ ρ),
      letI := C
      IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ) ω
          (Φ.analyticBoundaryComponent hΦ ρ) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ)
          𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) ω
          (Subtype.val : Φ.analyticBoundaryComponent hΦ ρ → Φ.analyticRealization hΦ) := by
  classical
  let := Φ.analyticChartedSpace hΦ
  have := Φ.isManifold_analyticRealization hΦ ω
  let S := Φ.analyticBoundaryComponent hΦ ρ
  let E := Fin (Module.finrank ℤ N) → ℂ
  let F := Fin (Module.finrank ℤ N - 1) → ℂ
  have hcharts (x : S) :
      ∃ (A : (F × ℂ) ≃L[ℂ] E)
        (e : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F × ℂ)
          (Φ.analyticRealization hΦ) (F × ℂ) ω),
        (x : Φ.analyticRealization hΦ) ∈ e.source ∧
          ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0 := by
    obtain ⟨s, j, e, hx, hs, he⟩ :=
      Φ.exists_partialDiffeomorph_analyticBoundaryComponent_normalForm hΦ x ω
    have hρ : ρ ∈ s := (hs ρ).mp x.2
    let k := j ⟨ρ, hρ⟩
    have heρ (y) (hy : y ∈ e.source) : y ∈ S ↔ e y k = 0 := by
      simpa only [S, exists_prop_of_true hρ] using he y hy ρ
    -- A coordinate indexed by an existing component forces positive ambient rank. Splitting
    -- off that coordinate leaves exactly the other `rank N - 1` complex coordinates.
    let d := Module.finrank ℤ N - 1
    have hn : d + 1 = Module.finrank ℤ N := by
      have hk := k.isLt
      dsimp [d]
      omega
    let k' : Fin (d + 1) := Fin.cast hn.symm k
    let R := LinearEquiv.funCongrLeft ℂ ℂ (finCongr hn)
    let L₀ : E ≃ₗ[ℂ] (F × ℂ) :=
      R ≪≫ₗ (LinearEquiv.piCongrLeft ℂ (fun _ : Option (Fin d) ↦ ℂ)
        (finSuccEquiv' k')) ≪≫ₗ
          LinearEquiv.piOptionEquivProd (M := fun _ : Option (Fin d) ↦ ℂ) ℂ ≪≫ₗ
          LinearEquiv.prodComm ℂ ℂ (Fin d → ℂ)
    let L : E ≃L[ℂ] (F × ℂ) := L₀.toContinuousLinearEquiv
    have hL (v : E) : (L v).2 = v k := by
      simp [L, L₀, R, k', LinearEquiv.piOptionEquivProd,
        LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', Equiv.piCongrLeft']
      -- The remaining reindexing casts the chosen coordinate to the successor presentation
      -- and back; finite indices have the same value under these casts.
      rfl
    let D : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F × ℂ) E (F × ℂ) ω :=
      PartialDiffeomorph.ofOpenPartialHomeomorph L.toHomeomorph.toOpenPartialHomeomorph
        (by simpa using L.contDiff.contDiffOn)
        (by simpa using L.symm.contDiff.contDiffOn)
    refine ⟨L.symm, e.trans D, ?_, ?_⟩
    · simpa [D] using hx
    · intro y hy
      rw [heρ y hy.1]
      simpa [D, PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv] using
        (congrArg (fun z : ℂ ↦ z = 0) (hL (e y)).symm).to_iff
  choose A e hcover hslice using hcharts
  let q (x : S) := (e x).toOpenPartialHomeomorph
  have hq (x : S) : IsSliceChart (q x) ((univ : Set F) ×ˢ ({0} : Set ℂ)) S := by
    apply isSliceChart_iff.2
    intro y hy
    simpa only [q, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and] using hslice x y hy
  refine ⟨linearSliceChartedSpace q hq hcover, ?_, ?_⟩
  · exact isManifold_linearSliceChartedSpace q hq
      (fun x z hz ↦ (e x).contMDiffOn.contMDiffAt ((e x).open_source.mem_nhds hz))
      (fun x z hz ↦ (e x).symm.contMDiffOn.contMDiffAt ((e x).open_target.mem_nhds hz)) hcover
  · exact isSmoothEmbedding_subtypeVal_linearSliceChartedSpace q hq A
      (fun x ↦ (e x).contMDiffOn) (fun x ↦ (e x).symm.contMDiffOn) hcover

end TauCeti.Toric.Fan
