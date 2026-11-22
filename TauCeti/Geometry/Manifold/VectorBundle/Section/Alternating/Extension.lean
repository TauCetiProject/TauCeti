/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Extension-based interior extensionality for alternating bundle sections

Over a finite-dimensional Hausdorff smooth manifold, evaluation of global `C^n` sections (`n ≤ ∞`)
at a point is surjective (`ContMDiffSection.evalLinearMap_surjective`), so two positive-degree `C^n`
alternating bundle sections are equal whenever their interior products with all global `C^n`
sections agree (`ContMDiffSection.ext_of_interior`).
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {E H M FW FV : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV] {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n FW W I]

/-- Positive-degree alternating sections on `W` are determined by their interior products with
global `C^n` sections of `W`. -/
theorem ext_of_interior {k : ℕ}
    {φ ψ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] V x⟯}
    (h : ∀ s : Cₛ^n⟮I; FW, W⟯, interior s φ = interior s ψ) : φ = ψ := by
  ext x v
  obtain ⟨s, hsx⟩ := evalLinearMap_surjective (I := I) (F := FW) n (V := W) x (v 0)
  have hcons : Matrix.vecCons (s x) (Fin.tail v) = v := by
    rw [evalLinearMap_apply] at hsx; rw [hsx]; exact Matrix.cons_head_tail v
  simpa only [interior_apply, hcons] using congr($(h s) x (Fin.tail v))

end ContMDiffSection
