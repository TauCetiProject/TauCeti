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
radius around `z₀` (`IsCompact.exists_pos_isInvertible_norm_inverse_le`). In particular, for a
continuous operator-valued map `Φ` on a topological real vector space and families `S, J`
continuous on `K`, invertibility of `Φ (S x)` on `K` persists to `Φ (S x - δ • J x)` on a uniform
closed interval `|δ| ≤ ε` (`IsCompact.exists_pos_isInvertible_map_sub_smul_norm_inverse_le`).

A continuous family of bounded operators with a continuous family of left inverses moves norms
by a uniformly bounded factor in both directions on a compact parameter set
(`IsCompact.exists_norm_apply_le_and_norm_le`).
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

/-- Invertibility on a compact parameter slice gives a uniform positive radius around `z₀` in a
pseudometric parameter space on which all operators remain invertible with uniformly bounded
inverses. Only `ContinuousWithinAt L (K ×ˢ Set.univ) (x, z₀)` at slice points `x ∈ K` is
required. -/
theorem exists_pos_isInvertible_norm_inverse_le {Z : Type*} [PseudoMetricSpace Z]
    {K : Set X} (hK : IsCompact K) (L : X × Z → E →L[𝕜] F) (z₀ : Z)
    (hL : ∀ x ∈ K, ContinuousWithinAt L (K ×ˢ Set.univ) (x, z₀))
    (hinv : ∀ x ∈ K, (L (x, z₀)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ z : Z, dist z z₀ ≤ ε →
      (L (x, z)).IsInvertible ∧ ‖(L (x, z)).inverse‖ ≤ C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hL' : ∀ x : K, ContinuousAt (fun p : K × Z ↦ L (p.fst, p.snd)) (x, z₀) := fun x ↦
    (hL x.val x.property).tendsto.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (continuous_subtypeVal.prodMap continuous_id).continuousAt
        (Filter.Eventually.of_forall fun p ↦ ⟨p.fst.property, mem_univ _⟩)
  obtain ⟨V, hV, C, hC, hbound⟩ := isCompact_univ.exists_mem_nhds_isInvertible_norm_inverse_le
    (fun p : K × Z ↦ L (p.fst, p.snd)) z₀ (fun x _ ↦ hL' x)
    (fun x _ ↦ hinv x x.property)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  exact ⟨r / 2, by positivity, C, hC, fun x hx z hz ↦
    hbound ⟨x, hx⟩ (mem_univ _) z (hrV (Metric.mem_ball.2 (hz.trans_lt (half_lt_self hr))))⟩

/-- On a compact parameter set `K` where `Φ (S x)` is invertible, if `Φ` is continuous and `S` and
`J` are continuous on `K`, then `Φ (S x - δ • J x)` remains invertible with uniformly bounded
inverses for all sufficiently small real weights `δ`. -/
theorem exists_pos_isInvertible_map_sub_smul_norm_inverse_le
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module ℝ M] [ContinuousSMul ℝ M]
    {K : Set X} (hK : IsCompact K) {Φ : M → E →L[𝕜] F} (hΦ : Continuous Φ)
    (S J : X → M) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hinv : ∀ x ∈ K, (Φ (S x)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (Φ (S x - δ • J x)).IsInvertible ∧ ‖(Φ (S x - δ • J x)).inverse‖ ≤ C := by
  have hcont : ContinuousOn (fun z : X × ℝ ↦ Φ (S z.1 - z.2 • J z.1)) (K ×ˢ Set.univ) :=
    hΦ.comp_continuousOn <| (hS.comp (s := K ×ˢ Set.univ) continuousOn_fst fun _ h ↦ h.1).sub
      (continuousOn_snd.smul (hJ.comp (s := K ×ˢ Set.univ) continuousOn_fst fun _ h ↦ h.1))
  obtain ⟨ε, hε, C, hC, hbound⟩ := hK.exists_pos_isInvertible_norm_inverse_le _ 0
    (fun x hx ↦ hcont (x, 0) ⟨hx, mem_univ _⟩)
    fun x hx ↦ by simpa only [zero_smul, sub_zero] using hinv x hx
  exact ⟨ε, hε, C, hC, fun x hx δ hδ ↦ hbound x hx δ (by simpa [Real.dist_eq] using hδ)⟩

end IsCompact

namespace IsCompact

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a compact parameter set, a continuous family of operators `L x` with a continuous family of
left inverses `Linv x` changes norms by a uniformly bounded factor: `‖L x v‖` and `‖v‖` are
comparable uniformly in `x`, since the norms of `L` and `Linv` are bounded there. -/
theorem exists_norm_apply_le_and_norm_le {K : Set X} (hK : IsCompact K) {L : X → E →L[𝕜] F}
    {Linv : X → F →L[𝕜] E} (hL : ContinuousOn L K) (hLinv : ContinuousOn Linv K)
    (hLL : ∀ x ∈ K, (Linv x).comp (L x) = ContinuousLinearMap.id 𝕜 E) :
    ∃ c, 1 ≤ c ∧ ∀ x ∈ K, ∀ v, ‖L x v‖ ≤ c * ‖v‖ ∧ ‖v‖ ≤ c * ‖L x v‖ := by
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hL.norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hLinv.norm
  refine ⟨max 1 (max A B), le_max_left _ _, fun x hx v ↦ ⟨?_, ?_⟩⟩
  · have hAx : ‖L x‖ ≤ max 1 (max A B) :=
      (by simpa using hA _ hx : ‖L x‖ ≤ A).trans ((le_max_left A B).trans (le_max_right 1 _))
    exact ((L x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))
  · have hBx : ‖Linv x‖ ≤ max 1 (max A B) :=
      (by simpa using hB _ hx : ‖Linv x‖ ≤ B).trans ((le_max_right A B).trans (le_max_right 1 _))
    calc ‖v‖ = ‖Linv x (L x v)‖ := by
          rw [← ContinuousLinearMap.comp_apply, hLL x hx, ContinuousLinearMap.id_apply]
      _ ≤ ‖Linv x‖ * ‖L x v‖ := (Linv x).le_opNorm _
      _ ≤ max 1 (max A B) * ‖L x v‖ := mul_le_mul_of_nonneg_right hBx (norm_nonneg _)

end IsCompact
