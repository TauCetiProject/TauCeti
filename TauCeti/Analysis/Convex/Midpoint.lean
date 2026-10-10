/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous midpoint-convex functions are convex

A function `f` is *midpoint convex* on a set `s` when `f (midpoint ℝ x y) ≤ (f x + f y) / 2` for
all `x, y ∈ s`. Jensen's theorem says that on a convex set a continuous midpoint-convex function is
convex. This is how convexity is usually checked when only a two-point inequality at midpoints is
available, as in the Bruhat--Tits form of nonpositive curvature in metric geometry.

## Main results

* `TauCeti.le_chord_of_midpoint` — on `[0, 1]`, a continuous midpoint-convex real function lies
  below the chord joining its values at `0` and `1`.
* `TauCeti.convexOn_of_midpoint` — on a convex subset of a real topological vector space, a
  continuous midpoint-convex function is convex.

## References

* J. L. W. V. Jensen, *Sur les fonctions convexes et les inégalités entre les valeurs moyennes*,
  Acta Math. 30 (1906), 175--193.
-/

public section

namespace TauCeti

open Set

/-- On `[0, 1]`, a continuous midpoint-convex function lies below its chord: its value at `t` is at
most `(1 - t) * g 0 + t * g 1`. -/
theorem le_chord_of_midpoint {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, g (midpoint ℝ s t) ≤ (g s + g t) / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : g t ≤ (1 - t) * g 0 + t * g 1 := by
  -- The gap `c` between `g` and its chord vanishes at both ends of `[0, 1]`. If it had a positive
  -- maximum, the leftmost point `t₀` attaining it would be the midpoint of two points of `[0, 1]`,
  -- one strictly to the left of `t₀`, and midpoint convexity would push `c t₀` below the maximum.
  set c : ℝ → ℝ := fun u => g u - ((1 - u) * g 0 + u * g 1) with hc_def
  have hc : ContinuousOn c (Icc 0 1) := hg.sub (by fun_prop)
  have hmid : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, c ((s + u) / 2) ≤ (c s + c u) / 2 := by
    intro s hs u hu
    have := h s hs u hu
    rw [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv, ← div_eq_inv_mul] at this
    simp only [hc_def]
    linarith
  suffices ∀ u ∈ Icc (0 : ℝ) 1, c u ≤ 0 by linarith [this t ht]
  by_contra! hpos
  obtain ⟨u, hu, hcu⟩ := hpos
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨u, hu⟩ hc
  rw [isMaxOn_iff] at hmax
  -- The leftmost maximizer `t₀` of `c` on `[0, 1]`.
  set S := Icc (0 : ℝ) 1 ∩ c ⁻¹' {c v} with hS_def
  have hS : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨t₀, ⟨ht₀, ht₀v⟩, hleast⟩ := hS.exists_isLeast ⟨v, hv, rfl⟩
  have hM : 0 < c v := hcu.trans_le (hmax _ hu)
  have h0 : c 0 = 0 := by simp [hc_def]
  have h1 : c 1 = 0 := by simp [hc_def]
  have ht₀0 : 0 < t₀ := lt_of_le_of_ne ht₀.1 fun h => by
    rw [mem_preimage, mem_singleton_iff, ← h, h0] at ht₀v
    linarith
  have ht₀1 : t₀ < 1 := lt_of_le_of_ne ht₀.2 fun h => by
    rw [mem_preimage, mem_singleton_iff, h, h1] at ht₀v
    linarith
  set δ := min t₀ (1 - t₀)
  have hδ : 0 < δ := lt_min ht₀0 (by linarith)
  have hl : t₀ - δ ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [min_le_left t₀ (1 - t₀)], by linarith [min_le_right t₀ (1 - t₀)]⟩
  have hr : t₀ + δ ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith [min_le_right t₀ (1 - t₀)]⟩
  -- Strictly left of `t₀`, the gap `c` is strictly below its maximum.
  have hlt : c (t₀ - δ) < c v := by
    refine lt_of_le_of_ne (hmax _ hl) fun heq => ?_
    have := hleast ⟨hl, heq⟩
    linarith
  have := hmid _ hl _ hr
  rw [show (t₀ - δ + (t₀ + δ)) / 2 = t₀ by ring, ht₀v] at this
  linarith [hmax _ hr]

/-- **Jensen's theorem.** On a convex subset of a real topological vector space, a continuous
function that is midpoint convex is convex. -/
theorem convexOn_of_midpoint {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ} (hs : Convex ℝ s)
    (hf : ContinuousOn f s)
    (h : ∀ x ∈ s, ∀ y ∈ s, f (midpoint ℝ x y) ≤ (f x + f y) / 2) :
    ConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := fun t ht =>
    hs.lineMap_mem hx hy ht
  have key := le_chord_of_midpoint (g := fun t => f (AffineMap.lineMap x y t))
    (hf.comp AffineMap.lineMap_continuous.continuousOn hmaps)
    (fun s' hs' t ht => by
      simpa only [AffineMap.map_midpoint] using h _ (hmaps hs') _ (hmaps ht))
    (t := b) ⟨hb, by linarith⟩
  rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_module,
    ← eq_sub_of_add_eq hab] at key
  simpa only [smul_eq_mul] using key

end TauCeti
