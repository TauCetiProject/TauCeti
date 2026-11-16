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

In a pseudometric parameter space, continuity on `K ×ˢ univ` upgrades this to a uniform positive
radius around `y₀` (`IsCompact.exists_pos_isInvertible_norm_inverse_le`). In particular, for a
continuous operator-valued map `Φ` on a topological real vector space and families `A, B`
continuous on `K`, invertibility of `Φ (A x)` on `K` persists to `Φ (A x - δ • B x)` on a uniform
closed interval `|δ| ≤ ε` (`IsCompact.exists_pos_isInvertible_sub_smul_norm_inverse_le`).
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

/-- Invertibility on a compact parameter slice gives a uniform positive radius around `y₀` in a
pseudometric parameter space on which all operators remain invertible with uniformly bounded
inverses. Only continuity on `K ×ˢ Set.univ` is required. -/
theorem exists_pos_isInvertible_norm_inverse_le {Z : Type*} [PseudoMetricSpace Z]
    {K : Set X} (hK : IsCompact K) (L : X × Z → E →L[𝕜] F) (z₀ : Z)
    (hL : ContinuousOn L (K ×ˢ Set.univ))
    (hinv : ∀ x ∈ K, (L (x, z₀)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ z : Z, dist z z₀ ≤ ε →
      (L (x, z)).IsInvertible ∧ ‖(L (x, z)).inverse‖ ≤ C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let L' : K × Z → E →L[𝕜] F := fun p ↦ L (p.1, p.2)
  have hL' : Continuous L' :=
    hL.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun p ↦ ⟨p.1.2, mem_univ _⟩
  obtain ⟨V, hV, C, hC, hbound⟩ :=
    isCompact_univ.exists_mem_nhds_isInvertible_norm_inverse_le L' z₀
      (fun _ _ ↦ hL'.continuousAt) (fun x _ ↦ hinv x x.2)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨r / 2, by positivity, C, hC, fun x hx z hz ↦
    hbound ⟨x, hx⟩ (mem_univ _) z (hrV ?_)⟩
  exact Metric.mem_ball.2 (hz.trans_lt (half_lt_self hr))

/-- For a continuous map `Φ` from a topological real vector space into bounded operators and
families `A, B` continuous on a compact set `K`, invertibility of `Φ (A x)` on `K` persists to
`Φ (A x - δ • B x)` on a uniform closed interval `|δ| ≤ ε` with uniformly bounded inverses. -/
theorem exists_pos_isInvertible_sub_smul_norm_inverse_le
    {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    {K : Set X} (hK : IsCompact K) (Φ : G → E →L[𝕜] F) (hΦ : Continuous Φ)
    (A B : X → G) (hA : ContinuousOn A K) (hB : ContinuousOn B K)
    (hinv : ∀ x ∈ K, (Φ (A x)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (Φ (A x - δ • B x)).IsInvertible ∧ ‖(Φ (A x - δ • B x)).inverse‖ ≤ C := by
  have hA' : ContinuousOn (fun z : X × ℝ ↦ A z.1) (K ×ˢ Set.univ) :=
    hA.comp continuousOn_fst fun _ h ↦ h.1
  have hB' : ContinuousOn (fun z : X × ℝ ↦ B z.1) (K ×ˢ Set.univ) :=
    hB.comp continuousOn_fst fun _ h ↦ h.1
  have hcont : ContinuousOn (fun z : X × ℝ ↦ Φ (A z.1 - z.2 • B z.1)) (K ×ˢ Set.univ) :=
    hΦ.comp_continuousOn (hA'.sub (continuousOn_snd.smul hB'))
  obtain ⟨ε, hε, C, hC, hbound⟩ := hK.exists_pos_isInvertible_norm_inverse_le _ 0 hcont (by
    intro x hx
    simpa only [zero_smul, sub_zero] using hinv x hx)
  refine ⟨ε, hε, C, hC, fun x hx δ hδ ↦ hbound x hx δ ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hδ

end IsCompact
