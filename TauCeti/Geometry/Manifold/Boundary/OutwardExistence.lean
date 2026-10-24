/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Existence of outward-pointing fields

A smooth finite-dimensional Hausdorff sigma-compact manifold with boundary admits a global
tangent field that points outward at every boundary point. Such a field supplies the outward
direction at the boundary; its negative, or backward flow, gives the inward direction used to
push boundary data into the manifold and is a standard input for collar and Stokes-type
constructions. The existence statement is the smooth version of J. M. Lee, *Introduction to
Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition 15.33.
-/

public section

open Set Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [T2Space M] [SigmaCompactSpace M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

local instance : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (n + 1)))
    (TangentSpace (𝓡∂ (n + 1)) : M → Type _) (𝓡∂ (n + 1)) := inferInstance

omit [T2Space M] [SigmaCompactSpace M] in
private theorem local_extension_outward {x : (𝓡∂ (n + 1)).boundary M}
    {y : M} (hy : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) (x : M)).source)
    (hby : y ∈ (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing y (FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
      (E := TangentSpace (𝓡∂ (n + 1))) (x := (x : M))
      (-EuclideanSpace.single 0 1 : TangentSpace (𝓡∂ (n + 1)) (x : M)) y) := by
  let v₀ : TangentSpace (𝓡∂ (n + 1)) (x : M) := -EuclideanSpace.single 0 1
  let g : (z : M) → TangentSpace (𝓡∂ (n + 1)) z :=
    FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
      (E := TangentSpace (𝓡∂ (n + 1))) (x := (x : M)) v₀
  have hxy : y ∈ (extChartAt (𝓡∂ (n + 1)) (x : M)).source := by
    simpa only [extChartAt_source] using hy
  rw [isOutwardPointing_iff_tangentCoordChange (x := y) (α := (x : M)) hby
    hxy
    (g y)]
  have hext : tangentCoordChange (𝓡∂ (n + 1)) y x y (g y) = v₀ := by
    let t := trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) (x : M)
    have hybase : y ∈ t.baseSet := by
      simpa [t] using hy
    have hvalue : (t ⟨(x : M), v₀⟩).2 = v₀ := by
      rw [TangentBundle.trivializationAt_apply]
      -- Read the trivialization at its centre as the identity tangent coordinate change.
      change tangentCoordChange (𝓡∂ (n + 1)) (x : M) (x : M) (x : M) v₀ = v₀
      rw [tangentCoordChange_self (x := (x : M)) (mem_extChartAt_source (I := 𝓡∂ (n + 1)) (x : M))]
    -- `TangentBundle.trivializationAt_apply` identifies this coordinate with
    -- `tangentCoordChange`; the change exposes that definitional identification.
    change (t (⟨y, g y⟩ : TangentBundle (𝓡∂ (n + 1)) M)).2 = v₀
    exact (FiberBundle.trivializationAt_extend_apply hybase v₀).trans hvalue
  rw [hext]
  simp [v₀]

/-- Every smooth finite-dimensional Hausdorff sigma-compact half-space manifold has a smooth field
pointing outward along its boundary. -/
theorem exists_isOutwardPointing :
    ∃ v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% v) ∧
        ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (v x) := by
  let v₀ : EuclideanSpace ℝ (Fin (n + 1)) := -EuclideanSpace.single 0 1
  let B := (𝓡∂ (n + 1)).boundary M
  let t : (y : M) → Set (TangentSpace (𝓡∂ (n + 1)) y) :=
    fun y ↦ {v | y ∈ B → IsOutwardPointing y v}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ B
    · simpa [t, hy] using IsOutwardPointing.convex (n := n) y
    · simpa [t, hy] using (convex_univ : Convex ℝ
        (Set.univ : Set (TangentSpace (𝓡∂ (n + 1)) y)))
  have hB : IsClosed B := by
    simpa [B] using (𝓡∂ (n + 1)).isClosed_boundary one_ne_zero
  have hloc : ∀ y₀ : M, ∃ U ∈ nhds y₀, ∃ s_loc : (y : M) →
      TangentSpace (𝓡∂ (n + 1)) y,
      (ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% s_loc) U) ∧
        ∀ y ∈ U, s_loc y ∈ t y := by
    intro y₀
    by_cases hy₀ : y₀ ∈ B
    · let x₀ : (𝓡∂ (n + 1)).boundary M := ⟨y₀, hy₀⟩
      let U := (chartAt (EuclideanHalfSpace (n + 1)) (x₀ : M)).source
      obtain ⟨s, hs, hsm⟩ := FiberBundle.exists_contMDiffOn_extend
        (M := M) (V := TangentSpace (𝓡∂ (n + 1))) (k := ∞) (x₀ := (x₀ : M))
        (𝓡∂ (n + 1)) (EuclideanSpace ℝ (Fin (n + 1))) v₀
      refine ⟨s ∩ U, Filter.inter_mem hs
          ((chartAt _ (x₀ : M)).open_source.mem_nhds (mem_chart_source _ _)),
        FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
          (E := TangentSpace (𝓡∂ (n + 1))) (x := (x₀ : M)) v₀,
        ?_, ?_⟩
      · exact hsm.mono inter_subset_left
      · intro y hy hby
        exact local_extension_outward (x := x₀) hy.2 hby
    · refine ⟨Bᶜ, hB.isOpen_compl.mem_nhds hy₀,
        (fun _ ↦ 0 : (y : M) → TangentSpace (𝓡∂ (n + 1)) y),
        ?_, ?_⟩
      · exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡∂ (n + 1)))).contMDiffOn
      · intro y hy hby
        exact (hy hby).elim
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (𝓡∂ (n + 1)) (TangentSpace (𝓡∂ (n + 1))) t ht hloc
  refine ⟨s, s.contMDiff, ?_⟩
  intro y hy
  exact hs y hy

end TauCeti
