/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc
import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic

/-!
# Morrey's embedding up to the boundary for local Sobolev maps

Let `X` be a Riemann surface with boundary, charted on the closed upper half-plane with chart
changes in `TauCeti.borderedHolomorphicGroupoid`, and `M` a smooth manifold modelled on a
finite-dimensional real normed space. For `2 < p`, a map in the local Sobolev class
`W^{k+1,p}_loc` up to the boundary on an open set `s` (`TauCeti.MemWkpLocMapOnBordered`) is of
class `Cᵏ` on `s` up to the boundary, for the smooth structure of `X` as a manifold with
boundary: `ContMDiffOn closedUpperHalfPlaneModel I k u s`.

The class is tested in all bordered holomorphic charts of `X`, in particular in the preferred
charts, and `ContMDiffOn` is tested in the preferred charts (`contMDiffOn_iff`). In those charts
the coordinate expression is a continuous map in `MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)` for an open
`Ω ⊆ ℂ`, so it is `Cᵏ` on `Ω ∩ {0 ≤ im}` by Morrey's embedding up to the real axis
(`TauCeti.MemWkpLoc.contDiffOn_of_continuousOn_inter_setOf_im_nonneg`). The class contains the
continuity of the map, so no choice of representative is involved.

## Main results

* `TauCeti.MemWkpLocMapOnBordered.contMDiffOn`, `TauCeti.MemWkpLocMapBordered.contMDiff`: for
  `2 < p`, `W^{k+1,p}_loc` up to the boundary implies `Cᵏ` up to the boundary.
* `TauCeti.MemWkpLocMapOnBordered.contMDiffOn_infty`,
  `TauCeti.MemWkpLocMapBordered.contMDiff_infty`: a map in the class of every order is smooth up to
  the boundary.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces on half-discs).
-/

public section

open Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [HasGroupoid X borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {p : ENNReal} {u : X → M} {s : Set X}

/-- **Morrey's embedding up to the boundary.** For `2 < p`, a map from a Riemann surface with
boundary in the local Sobolev class `W^{k+1,p}_loc` up to the boundary on an open set `s` is of
class `Cᵏ` on `s`, up to the boundary of `X`. -/
theorem MemWkpLocMapOnBordered.contMDiffOn {k : ℕ} (hu : MemWkpLocMapOnBordered I p (k + 1) u s)
    (hp : 2 < p) (hs : IsOpen s) : ContMDiffOn closedUpperHalfPlaneModel I k u s := by
  have : IsManifold I k M := .of_le (n := ∞) (by exact_mod_cast le_top)
  rw [contMDiffOn_iff]
  refine ⟨hu.continuousOn, fun x y ↦ ?_⟩
  set φ := chartAt ClosedUpperHalfPlane x
  set ψ := chartAt H y
  -- The coordinate domain is a half-disc `Ω ∩ {0 ≤ im}` with `Ω` open.
  obtain ⟨Ω, hΩ, hV⟩ := φ.exists_isOpen_extend_target_inter_preimage
    (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have hw := hu.memWkpLoc_chart (StructureGroupoid.chart_mem_maximalAtlas _ x)
    (IsManifold.chart_mem_maximalAtlas y)
  have hc : ContinuousOn (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    (ψ.continuousOn_extend (I := I)).comp (hu.continuousOn.comp
      (φ.continuousOn_extend_symm.mono inter_subset_left) fun _ hz ↦ hz.2.1) fun _ hz ↦ by
      rw [OpenPartialHomeomorph.extend_source]; exact hz.2.2
  rw [hV] at hw hc
  have h := hw.contDiffOn_of_continuousOn_inter_setOf_im_nonneg (Ω := ⟨Ω, hΩ⟩) hp hc
  -- The preferred extended charts `extChartAt` are the extensions of the preferred charts.
  simp only [extChartAt, OpenPartialHomeomorph.extend_source]
  rwa [hV]

/-- **Morrey's embedding up to the boundary on the whole surface.** For `2 < p`, a map from a
Riemann surface with boundary in the local Sobolev class `W^{k+1,p}_loc` up to the boundary is
of class `Cᵏ` up to the boundary. -/
theorem MemWkpLocMapBordered.contMDiff {k : ℕ} (hu : MemWkpLocMapBordered I p (k + 1) u)
    (hp : 2 < p) : ContMDiff closedUpperHalfPlaneModel I k u :=
  contMDiffOn_univ.1
    (MemWkpLocMapOnBordered.contMDiffOn (memWkpLocMapOnGroupoid_univ.2 hu) hp isOpen_univ)

/-- For `2 < p`, a map from a Riemann surface with boundary in the local Sobolev class
`W^{k,p}_loc` up to the boundary on an open set `s` for every `k` is smooth on `s`, up to the
boundary of `X`. -/
theorem MemWkpLocMapOnBordered.contMDiffOn_infty
    (hu : ∀ k : ℕ, MemWkpLocMapOnBordered I p k u s) (hp : 2 < p) (hs : IsOpen s) :
    ContMDiffOn closedUpperHalfPlaneModel I ∞ u s :=
  _root_.contMDiffOn_infty.2 fun k ↦ (hu (k + 1)).contMDiffOn hp hs

/-- For `2 < p`, a map from a Riemann surface with boundary in the local Sobolev class
`W^{k,p}_loc` up to the boundary for every `k` is smooth up to the boundary. -/
theorem MemWkpLocMapBordered.contMDiff_infty (hu : ∀ k : ℕ, MemWkpLocMapBordered I p k u)
    (hp : 2 < p) : ContMDiff closedUpperHalfPlaneModel I ∞ u :=
  _root_.contMDiff_infty.2 fun k ↦ (hu (k + 1)).contMDiff hp

end TauCeti
