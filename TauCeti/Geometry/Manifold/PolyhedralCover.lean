/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PLGroupoid.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.Polyhedral
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Polyhedral chart patches and their overlaps

A compact subset of a manifold modeled on a finite real coordinate space can be covered by
finitely many open coordinate balls whose closed balls stay inside their chart targets and
inside any prescribed neighbourhood. For the supremum norm these closed balls are compact
convex polyhedra.

On a PL manifold, the intersection of two such closed patches, read in either chart, is
exactly a finite union of compact convex polyhedra. Thus the patches and their intersections
provide polyhedral pieces for fitting chart triangulations together.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Definition 1.8
(PL manifolds), Corollary 2.3 and Chapter 2 (triangulations).
-/

public section

open Set Filter Topology Metric
open scoped Manifold

namespace TauCeti

variable {ι M : Type*} [Fintype ι] [TopologicalSpace M] [ChartedSpace (ι → ℝ) M]
  [T2Space M] [HasGroupoid M (PLGroupoid 𝓘(ℝ, ι → ℝ))]

/-- A compact subset of a PL manifold has a finite cover by open coordinate balls whose
closed patches stay inside the chart targets and a prescribed neighbourhood. The overlaps of
the closed patches, read in either chart, are finite unions of compact convex polyhedra. -/
theorem exists_finite_polyhedral_chart_cover {s U : Set M} (hs : IsCompact s)
    (hU : U ∈ 𝓝ˢ s) :
    ∃ (n : ℕ) (c : Fin n → M) (r : Fin n → ℝ),
      (∀ i, c i ∈ s ∧ 0 < r i ∧
        closedBall (chartAt (ι → ℝ) (c i) (c i)) (r i) ⊆
          (chartAt (ι → ℝ) (c i)).target ∧
        (chartAt (ι → ℝ) (c i)).symm ''
          closedBall (chartAt (ι → ℝ) (c i) (c i)) (r i) ⊆ U) ∧
      (s ⊆ ⋃ i, (chartAt (ι → ℝ) (c i)).symm ''
        ball (chartAt (ι → ℝ) (c i) (c i)) (r i)) ∧
      ∀ i j, ∃ C : Finset (Set (ι → ℝ)),
        (∀ P ∈ C, IsCompact P ∧ IsConvexPolyhedron P) ∧
        (⋃ P ∈ C, P) = (chartAt (ι → ℝ) (c i)) ''
          (((chartAt (ι → ℝ) (c i)).symm ''
            closedBall (chartAt (ι → ℝ) (c i) (c i)) (r i)) ∩
           ((chartAt (ι → ℝ) (c j)).symm ''
            closedBall (chartAt (ι → ℝ) (c j) (c j)) (r j))) := by
  classical
  let e (x : M) := chartAt (ι → ℝ) x
  -- First shrink each preferred chart inside U, then take a finite subcover.
  have hlocal (x : M) (hx : x ∈ s) : ∃ r > 0,
      closedBall (e x x) r ⊆ (e x).target ∩ (e x).symm ⁻¹' U := by
    have hxs : x ∈ (e x).source := mem_chart_source (ι → ℝ) x
    have hpre : (e x).symm ⁻¹' U ∈ 𝓝 (e x x) :=
      (e x).tendsto_symm hxs (mem_nhdsSet_iff_forall.mp hU x hx)
    exact nhds_basis_closedBall.mem_iff.mp
      (inter_mem ((e x).open_target.mem_nhds ((e x).map_source hxs)) hpre)
  choose! r hr hsub using hlocal
  let V (x : M) := (e x).symm '' ball (e x x) (r x)
  have hV (x : M) (hx : x ∈ s) : V x ∈ 𝓝 x := by
    simpa only [V, (e x).left_inv (mem_chart_source (ι → ℝ) x)] using
      (e x).symm.image_mem_nhds ((e x).map_source (mem_chart_source (ι → ℝ) x))
        (ball_mem_nhds _ (hr x hx))
  obtain ⟨a, has, hcover⟩ := hs.elim_nhds_subcover V hV
  let c : Fin a.card → M := fun i => ((a.equivFin).symm i).1
  refine ⟨a.card, c, fun i => r (c i), ?_, ?_, ?_⟩
  · intro i
    have hci : c i ∈ s := has _ ((a.equivFin).symm i).2
    refine ⟨hci, hr _ hci, fun y hy => (hsub _ hci hy).1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hsub _ hci hy).2
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨a.equivFin ⟨y, hy⟩, by
      simpa only [c, Equiv.symm_apply_apply, V, e] using hxy⟩
  · intro i j
    -- Compactness of the closed patches makes the partial PL transition's overlap finite.
    have hci : c i ∈ s := has _ ((a.equivFin).symm i).2
    have hcj : c j ∈ s := has _ ((a.equivFin).symm j).2
    have htrans := (mem_PLGroupoid_iff 𝓘(ℝ, ι → ℝ)).mp
      ((PLGroupoid 𝓘(ℝ, ι → ℝ)).compatible
        (chart_mem_atlas (ι → ℝ) (c i)) (chart_mem_atlas (ι → ℝ) (c j)))
    have hpl : IsPLOn (e (c j) ∘ (e (c i)).symm)
        ((e (c i)).symm.trans (e (c j))).source := by
      simpa only [mfld_simps] using htrans.1
    exact (e (c i)).exists_polyhedral_overlap (e (c j)) hpl
      (isCompact_closedBall _ _) (isConvexPolyhedron_closedBall_pi _ (hr _ hci).le)
      (fun y hy => (hsub _ hci hy).1)
      (isCompact_closedBall _ _) (isConvexPolyhedron_closedBall_pi _ (hr _ hcj).le)
      (fun y hy => (hsub _ hcj hy).1)

end TauCeti
