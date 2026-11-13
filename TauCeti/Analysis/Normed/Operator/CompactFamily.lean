/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact

/-!
# Uniform inverse bounds near compact families

A continuous family of bounded operators which is invertible on a compact parameter slice
remains invertible on a common neighborhood of that slice, with a uniform operator-norm bound
on its inverses. Only the domain of the operators needs to be complete.
-/

public section

open Filter Set Topology

namespace IsCompact

variable {𝕜 X Y E F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Invertibility on a compact parameter slice gives a common neighborhood in the other
parameter, with uniformly bounded inverses. The compact set may be empty. -/
theorem exists_mem_nhds_isInvertible_norm_inverse_le {K : Set X} (hK : IsCompact K)
    (L : X × Y → E →L[𝕜] F) (y₀ : Y)
    (hL : ∀ x ∈ K, ContinuousAt L (x, y₀))
    (hinv : ∀ x ∈ K, (L (x, y₀)).IsInvertible) :
    ∃ V ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ V, (L (x, y)).IsInvertible ∧ ‖(L (x, y)).inverse‖ ≤ C := by
  have hcont : ContinuousOn (fun x ↦ ‖(L (x, y₀)).inverse‖) K := by
    intro x hx
    have hi : ContinuousAt (fun A : E →L[𝕜] F ↦ A.inverse) (L (x, y₀)) :=
      ((hinv x hx).contDiffAt_map_inverse (n := 0)).continuousAt
    have hslice : ContinuousAt (fun x : X ↦ L (x, y₀)) x :=
      (hL x hx).comp_of_eq (continuousAt_id.prodMk continuousAt_const) rfl
    exact (hi.comp_of_eq hslice rfl).norm.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcont
  let C := max 0 M + 1
  have hnear : {z : X × Y | (L z).IsInvertible ∧ ‖(L z).inverse‖ < C} ∈
      (𝓝ˢ K) ×ˢ 𝓝 y₀ := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro x hx
    rw [← nhds_prod_eq]
    have hnorm : ContinuousAt (fun z ↦ ‖(L z).inverse‖) (x, y₀) :=
      (((hinv x hx).contDiffAt_map_inverse (n := 0)).continuousAt.comp (hL x hx)).norm
    have hlt : ‖(L (x, y₀)).inverse‖ < C :=
      ((hM (mem_image_of_mem _ hx)).trans (le_max_right 0 M)).trans_lt (lt_add_one _)
    exact ((hL x hx).eventually (hinv x hx).eventually_nhds).and
      (hnorm.eventually (gt_mem_nhds hlt))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hnear
  refine ⟨V, hV, C, by positivity, fun x hx y hy ↦ ?_⟩
  exact (hUV ⟨subset_of_mem_nhdsSet hU hx, hy⟩).imp_right le_of_lt

end IsCompact
