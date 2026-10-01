/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Basic
import TauCeti.Topology.Sym.Cons
import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets of basepoint-divisor intersections

A holomorphic curve in a symmetric power need not remain in one elementary-symmetric chart.
Nevertheless, local analytic equations suffice to show that its intersections with the
basepoint divisor in a compact parameter set are finite, provided the curve is not locally
contained in the divisor at any intersection. Each intersection then has a finite positive
analytic order in a local equation. This is the finiteness and local positivity needed to form
the basepoint count of a holomorphic disk; identifying the orders in overlapping charts is a
separate step.

The divisor and its local analytic equation are from
`TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Basic`. The geometric
interpretation follows Ozsváth--Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Section 2.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] {n : ℕ}
variable {f : ℂ → Sym α n} {K : Set ℂ}

/-- A curve with locally analytic symmetric-chart coordinates has only finitely many intersections
with a basepoint divisor in a compact parameter set, if it is continuous at points of that set
and is not locally contained in the divisor at any intersection.

No single chart is required to contain the image of `K`. The noncontainment condition is local
and must be established separately, for example from boundary conditions on a holomorphic disk.
-/
theorem finite_basepointDivisor_intersections_of_not_eventually_mem (z : α)
    (hK : IsCompact K)
    (hf : ∀ w ∈ K, ContinuousAt f w)
    (ha : ∀ w ∈ K, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (hnot : ∀ w ∈ K, f w ∈ Sym.basepointDivisor z →
      ¬ ∀ᶠ t in 𝓝 w, f t ∈ Sym.basepointDivisor z) :
    (K ∩ f ⁻¹' Sym.basepointDivisor z).Finite := by
  by_contra hfinite
  have hinfinite : (K ∩ f ⁻¹' Sym.basepointDivisor z).Infinite := Set.not_finite.mp hfinite
  obtain ⟨w, hwK, hacc⟩ :=
    hinfinite.exists_accPt_of_subset_isCompact hK inter_subset_left
  have hwD : f w ∈ Sym.basepointDivisor z := by
    by_contra hwD
    have hnhds : f ⁻¹' (Sym.basepointDivisor z)ᶜ ∈ 𝓝 w :=
      (hf w hwK).preimage_mem_nhds
        ((Sym.isClosed_basepointDivisor z).isOpen_compl.mem_nhds hwD)
    obtain ⟨v, ⟨hv, hvC⟩, _⟩ := (accPt_iff_nhds.mp hacc) _ hnhds
    exact hv hvC.2
  obtain ⟨_, _, g, _, _, _, _, _, htop, hisolated⟩ :=
    basepointDivisor_intersection_order z f w (hf w hwK) (ha w hwK hwD) hwD
  have hfiniteOrder : analyticOrderAt g w ≠ ⊤ := by
    intro htopOrder
    exact hnot w hwK hwD (htop.mp htopOrder)
  have havoid := hisolated hfiniteOrder
  obtain ⟨v, hvC, hvNot⟩ :=
    ((accPt_iff_frequently_nhdsNE.mp hacc).and_eventually havoid).exists
  exact hvNot hvC.2

end TauCeti

end
