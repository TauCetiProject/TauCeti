/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.EffectiveDomain
public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Continuous

/-!
# Compactness of subgradient images of convex functions

Let `E` be a finite-dimensional real inner product space and let `f : E → EReal` be convex
(convex real epigraph, never `⊥`), with `D` the interior of its effective domain `{x | f x ≠ ⊤}`.
Since `f` is continuous on `D`, its subgradients for the inner product are bounded over every
compact `K ⊆ D`, and the graph of the subdifferential over a closed `K ⊆ D` is closed. Hence
the subgradient image `∂f(K) = ⋃ x ∈ K, ∂f(x)` of a compact subset of `D` is compact.

## Main statements

* `TauCeti.exists_norm_le_of_mem_subdifferential` — the subgradients of `f` are bounded over
  compact subsets of `D`;
* `TauCeti.isClosed_setOf_mem_subdifferential` — the graph of the subdifferential over a closed
  subset of `D` is closed;
* `TauCeti.isCompact_subgradientImage` — the subgradient image of a compact subset of `D` is
  compact.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 24.7.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1.
-/

public section

namespace TauCeti

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
include hf hbot

/-- **Subgradients of a convex function are locally bounded.** The subgradients of a convex
`f : E → EReal` on a finite-dimensional real inner product space are bounded over a compact
subset `K` of the interior of the effective domain. -/
theorem exists_norm_le_of_mem_subdifferential {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    ∃ R, ∀ x ∈ K, ∀ y ∈ subdifferential (innerₗ E) f x, ‖y‖ ≤ R := by
  -- Compare `f` at `x ∈ K` and at `x + δ • y / ‖y‖` in a compact thickening of `K` inside the
  -- domain, where `f` is continuous, hence bounded.
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open isOpen_interior hKD
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn
    ((convexOn_toReal hf hbot).continuousOn_interior.mono hKδ)
  have hM' : ∀ x ∈ cthickening δ K, |(f x).toReal| ≤ M := fun x hx => by
    simpa only [Real.norm_eq_abs] using hM x hx
  refine ⟨2 * M / δ, fun x hx y hy => ?_⟩
  have hxδ : x ∈ cthickening δ K := self_subset_cthickening K hx
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using div_nonneg (mul_nonneg zero_le_two ((abs_nonneg _).trans (hM' x hxδ))) hδ.le
  have hy0' : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set x' := x + (δ / ‖y‖) • y
  have hx' : x' ∈ cthickening δ K := mem_cthickening_of_dist_le x' x δ K hx <| by
    simp [x', dist_eq_norm, norm_smul, hy0'.ne', abs_of_pos hδ]
  have hle := (mem_subdifferential_iff_forall_toReal_add_le _ hbot
    (ne_top_of_mem_subdifferential _ hy)).1 hy x' (interior_subset (hKδ hx'))
  have hinner : innerₗ E (x' - x) y = δ * ‖y‖ := by
    simp only [x', add_sub_cancel_left, innerₗ_apply_apply, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    field_simp
  rw [hinner] at hle
  have h₁ := (abs_le.1 (hM' x' hx')).2
  have h₂ := (abs_le.1 (hM' x hxδ)).1
  rw [le_div_iff₀ hδ]
  linarith

/-- The graph of the subdifferential of a convex `f : E → EReal` over a closed subset `K` of the
interior of the effective domain is closed. -/
theorem isClosed_setOf_mem_subdifferential {K : Set E} (hK : IsClosed K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsClosed {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} := by
  -- The graph is cut out of `K × E` by the subgradient inequalities, which are closed conditions
  -- because `f` is continuous there.
  set h : E → ℝ := fun x => (f x).toReal
  have hG : {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} =
      (K ×ˢ univ) ∩ ⋂ x' ∈ {x' | f x' ≠ ⊤},
        ((K ×ˢ univ) ∩ (fun z : E × E => h z.1 + innerₗ E (x' - z.1) z.2) ⁻¹' Iic (h x')) := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_iInter,
      mem_preimage, mem_Iic]
    refine and_congr_right fun hx => ?_
    rw [mem_subdifferential_iff_forall_toReal_add_le _ hbot (interior_subset (hKD hx))]
    exact forall₂_congr fun x' _ => (and_iff_right hx).symm
  rw [hG]
  refine (hK.prod isClosed_univ).inter (isClosed_biInter fun x' _ => ?_)
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.prod isClosed_univ)
    isClosed_Iic
  refine ContinuousOn.add (((convexOn_toReal hf hbot).continuousOn_interior.mono hKD).comp
    continuousOn_fst fun z hz => hz.1) ?_
  simp only [innerₗ_apply_apply]
  exact ((continuous_const.sub continuous_fst).inner continuous_snd).continuousOn

/-- **Subgradient images of compact sets are compact.** For a convex `f : E → EReal` on a
finite-dimensional real inner product space, the subgradient image of a compact subset of the
interior of the effective domain is compact. -/
theorem isCompact_subgradientImage {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsCompact (subgradientImage (innerₗ E) f K) := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential hf hbot hK hKD
  have hG : IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} :=
    (hK.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset
      (isClosed_setOf_mem_subdifferential hf hbot hK.isClosed hKD)
      fun z hz => ⟨hz.1, mem_closedBall_zero_iff.2 (hR z.1 hz.1 z.2 hz.2)⟩
  convert hG.image continuous_snd using 1
  ext y
  simp

end TauCeti
