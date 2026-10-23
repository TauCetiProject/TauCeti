/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Existence of outward-pointing fields

A smooth finite-dimensional manifold with boundary admits a global tangent field that points
outward at every boundary point. The proof extends constant negative normal fields in boundary
charts and glues them with a smooth partition of unity; the existing convexity API for outward
vectors makes the result independent of the chosen charts.
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
  -- The tangent-space fibre is definitionally the model space, but the section is dependent.
  change IsOutwardPointing y (g y)
  have hxy : y ∈ (extChartAt (𝓡∂ (n + 1)) (x : M)).source := by
    simpa only [extChartAt_source] using hy
  rw [isOutwardPointing_iff_tangentCoordChange (x := y) (α := (x : M)) hby
    hxy
    (g y)]
  have hext : tangentCoordChange (𝓡∂ (n + 1)) y x y (g y) = v₀ := by
    let t := trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) (x : M)
    let w : EuclideanSpace ℝ (Fin (n + 1)) := (t ⟨(x : M), v₀⟩).2
    have hybase : y ∈ t.baseSet := by
      simpa [t] using hy
    have hvalue : (t ⟨(x : M), v₀⟩).2 = v₀ := by
      rw [TangentBundle.trivializationAt_apply]
      -- Read the trivialization at its centre as the identity tangent coordinate change.
      change tangentCoordChange (𝓡∂ (n + 1)) (x : M) (x : M) (x : M) v₀ = v₀
      rw [tangentCoordChange_self (x := (x : M)) (mem_extChartAt_source (I := 𝓡∂ (n + 1)) (x : M))]
    have hsymm := t.symm_apply hybase w
    have hp : (⟨y, g y⟩ : TangentBundle (𝓡∂ (n + 1)) M) = t.toPartialEquiv.symm (y, w) := by
      apply TotalSpace.ext
      · exact t.proj_symm_apply' (x := w) hybase
      · exact (heq_of_eq hsymm).trans (cast_heq _ _)
    have hcoord : (t (⟨y, g y⟩ : TangentBundle (𝓡∂ (n + 1)) M)).2 = w := by
      rw [hp]
      simpa [w] using congrArg Prod.snd (t.apply_symm_apply' (x := w) hybase)
    change (t (⟨y, g y⟩ : TangentBundle (𝓡∂ (n + 1)) M)).2 = v₀
    simpa [t, TangentBundle.trivializationAt_apply] using hcoord.trans (hvalue ▸ rfl)
  rw [hext]
  simp [v₀]


/-- Every smooth finite-dimensional Hausdorff half-space manifold has a smooth field pointing
outward along its boundary. -/
theorem exists_isOutwardPointing :
    ∃ v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% v) ∧
        ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (v x) := by
  let B := (𝓡∂ (n + 1)).boundary M
  let U : B → Set M := fun x ↦ (chartAt (EuclideanHalfSpace (n + 1)) (x : M)).source
  have hU : ∀ i : B, IsOpen (U i) := fun i => (chartAt _ (i : M)).open_source
  have hcover : B ⊆ ⋃ i : B, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_chart_source _ x⟩
  have hB : IsClosed B := by
    simpa [B] using (𝓡∂ (n + 1)).isClosed_boundary one_ne_zero
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓡∂ (n + 1)) hB U hU hcover
  let v₀ : EuclideanSpace ℝ (Fin (n + 1)) := -EuclideanSpace.single 0 1
  let g : B → (z : M) → TangentSpace (𝓡∂ (n + 1)) z := fun i ↦
    FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
      (E := TangentSpace (𝓡∂ (n + 1))) (x := (i : M)) v₀
  have hg : ∀ i : B, ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (T% (g i)) (U i) := by
    intro i
    let t := trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) (i : M)
    let w : EuclideanSpace ℝ (Fin (n + 1)) := (t ⟨(i : M), v₀⟩).2
    suffices hcoord : CMDiff[t.baseSet] ∞
        (fun y ↦ (t ⟨y, FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
          (E := TangentSpace (𝓡∂ (n + 1))) (x := (i : M)) v₀ y⟩).2) by
      intro y hy
      rw [t.contMDiffWithinAt_section _ hy]
      exact hcoord y hy
    have hw : CMDiff[t.baseSet] ∞ (fun _ : M ↦ w) := contMDiffOn_const
    exact hw.congr fun y hy => by
      have hsymm := t.symm_apply hy w
      have hp : (⟨y, FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
          (E := TangentSpace (𝓡∂ (n + 1))) (x := (i : M)) v₀ y⟩ :
          TangentBundle (𝓡∂ (n + 1)) M) = t.toPartialEquiv.symm (y, w) := by
        apply TotalSpace.ext
        · exact t.proj_symm_apply' (x := w) hy
        · exact (heq_of_eq hsymm).trans (cast_heq _ _)
      rw [hp]
      simpa [w] using congrArg Prod.snd (t.apply_symm_apply' (x := w) hy)
  let s : B → (z : M) → TangentSpace (𝓡∂ (n + 1)) z := fun i y ↦
    ρ i y • g i y
  have hs : ∀ i : B, ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% (s i)) := by
    intro i
    exact (ρ i).contMDiff.contMDiffOn.smul_section_of_tsupport (hU i)
      (hρ i) (hg i)
  have hlf : LocallyFinite (fun i : B ↦ {y | s i y ≠ 0}) := by
    apply ρ.locallyFinite.subset
    intro i y hy
    have hρy : ρ i y ≠ 0 := by
      intro hzero
      apply hy
      simp [s, hzero]
    exact Function.mem_support.mpr hρy
  let v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x := fun y ↦ ∑ᶠ i, s i y
  have hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% v) := by
    exact ContMDiff.finsum_section_of_locallyFinite hlf hs
  refine ⟨v, hv, ?_⟩
  intro y hy
  change ∑ᶠ i, ρ i y • g i y ∈ {z | IsOutwardPointing y z}
  apply ρ.finsum_smul_mem_convex (g := fun i y => g i y)
    (t := {z | IsOutwardPointing y z}) hy
  · intro i hi
    apply local_extension_outward (x := i) ?_ hy
    exact (hρ i (subset_closure (Function.mem_support.mpr hi)))
  · exact IsOutwardPointing.convex (n := n) y

end TauCeti
