/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
public import TauCeti.Topology.MetricSpace.Holder

/-!
# `C¹` maps are locally Hölder

A map that is `C¹` at a point is Lipschitz near it, hence Hölder near it for every exponent at
most one; and postcomposing a map that is Hölder near a point with a map that is `C¹` at its image
keeps the exponent. These are the local Hölder bounds needed to feed classical data and semilinear
right-hand sides into Schauder theory, where the data must be locally Hölder.

## Main declarations

* `ContDiffAt.exists_holderOnWith`: a map that is `C¹` at `x` is `α`-Hölder on a neighbourhood
  of `x` for every `α ≤ 1`.
* `ContDiffAt.exists_holderOnWith_comp`: if `Φ` is `α`-Hölder on a neighbourhood of `x` and
  continuous at `x`, and `f` is `C¹` at `Φ x`, then `f ∘ Φ` is `α`-Hölder on a neighbourhood
  of `x`.
* `ContDiffAt.exists_holderOnWith_comp_prodMk`: if `g` is `α`-Hölder on a neighbourhood of `x`
  and continuous at `x`, with `α ≤ 1`, and `f` is `C¹` at `(x, g x)`, then `y ↦ f (y, g y)` is
  `α`-Hölder on a neighbourhood of `x`. This is the form taken by a semilinear right-hand side
  `F(x, u(x))`.
-/

public section

open Set Filter Metric
open scoped NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A map that is `C¹` at `x` is `α`-Hölder on a neighbourhood of `x`, for every exponent
`α ≤ 1`. -/
theorem ContDiffAt.exists_holderOnWith {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x)
    {α : ℝ≥0} (hα : α ≤ 1) : ∃ T ∈ 𝓝 x, ∃ K, HolderOnWith K α f T := by
  obtain ⟨L, t, ht, hL⟩ := hf.exists_lipschitzOnWith
  refine ⟨t ∩ ball x 1, inter_mem ht (ball_mem_nhds x one_pos), _,
    HolderOnWith.of_le_of_dist_le (K := L) (D := 2 * L) (δ := 2) (β := 1) (fun y hy z hz _ => ?_)
      (fun y hy z hz => ?_) hα two_pos⟩
  · simpa using hL.dist_le_mul y hy.1 z hz.1
  · -- Points of `ball x 1` are at distance at most `2`.
    refine (hL.dist_le_mul y hy.1 z hz.1).trans ?_
    have h2 : dist y z ≤ 2 := ((dist_triangle_right y z x).trans
      (add_le_add (mem_ball.1 hy.2).le (mem_ball.1 hz.2).le)).trans_eq (by norm_num)
    push_cast
    nlinarith [L.coe_nonneg]

/-- If `Φ` is `α`-Hölder on a neighbourhood of `x` and continuous at `x`, and `f` is `C¹` at
`Φ x`, then `f ∘ Φ` is `α`-Hölder on a neighbourhood of `x`. -/
theorem ContDiffAt.exists_holderOnWith_comp {X : Type*} [PseudoMetricSpace X] {f : E → F}
    {Φ : X → E} {x : X} (hf : ContDiffAt ℝ 1 f (Φ x)) {K α : ℝ≥0} {T : Set X}
    (hΦ : HolderOnWith K α Φ T) (hT : T ∈ 𝓝 x) (hΦx : ContinuousAt Φ x) :
    ∃ T' ∈ 𝓝 x, ∃ K', HolderOnWith K' α (f ∘ Φ) T' := by
  obtain ⟨L, t, ht, hL⟩ := hf.exists_lipschitzOnWith
  refine ⟨T ∩ Φ ⁻¹' t, inter_mem hT (hΦx ht), L * K, ?_⟩
  simpa using (holderOnWith_one.2 hL).comp (hΦ.mono inter_subset_left) fun y hy => hy.2

/-- If `g` is `α`-Hölder on a neighbourhood of `x` and continuous at `x`, with `α ≤ 1`, and `f`
is `C¹` at `(x, g x)`, then `y ↦ f (y, g y)` is `α`-Hölder on a neighbourhood of `x`. -/
theorem ContDiffAt.exists_holderOnWith_comp_prodMk {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E × G → F} {g : E → G} {x : E} (hf : ContDiffAt ℝ 1 f (x, g x))
    {K α : ℝ≥0} (hα : α ≤ 1) {T : Set E} (hg : HolderOnWith K α g T) (hT : T ∈ 𝓝 x)
    (hgx : ContinuousAt g x) : ∃ T' ∈ 𝓝 x, ∃ K', HolderOnWith K' α (fun y => f (y, g y)) T' := by
  obtain ⟨S, hS, C, hC⟩ := (contDiffAt_id (𝕜 := ℝ) (x := x)).exists_holderOnWith hα
  -- The graph map `y ↦ (y, g y)` is `α`-Hölder near `x`, with the larger of the two constants.
  have hΦ : HolderOnWith (max C K) α (fun y => (y, g y)) (S ∩ T) := by
    intro y hy z hz
    rw [Prod.edist_eq, ENNReal.coe_max]
    exact max_le ((hC y hy.1 z hz.1).trans (by gcongr; exact le_max_left _ _))
      ((hg y hy.2 z hz.2).trans (by gcongr; exact le_max_right _ _))
  exact hf.exists_holderOnWith_comp (Φ := fun y => (y, g y)) hΦ (inter_mem hS hT)
    (continuousAt_id.prodMk hgx)
