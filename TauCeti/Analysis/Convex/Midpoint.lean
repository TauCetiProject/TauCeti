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
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper semicontinuous midpoint-convex functions are convex

A function `f` is *midpoint convex* on a set `s` when `f (midpoint ℝ x y) ≤ (f x + f y) / 2` for
all `x, y ∈ s`. Jensen's theorem says that on a convex set a continuous midpoint-convex function is
convex; upper semicontinuity already suffices. This is how convexity is usually checked when only
a two-point inequality at midpoints is available, as in the Bruhat--Tits form of nonpositive
curvature in metric geometry.

## Main results

* `TauCeti.le_chord_of_midpoint` — on `[0, 1]`, an upper semicontinuous midpoint-convex real
  function lies below the chord joining its values at `0` and `1`.
* `TauCeti.convexOn_of_midpoint` — on a convex subset of a real topological vector space, an
  upper semicontinuous midpoint-convex function is convex.

## References

* J. L. W. V. Jensen, *Sur les fonctions convexes et les inégalités entre les valeurs moyennes*,
  Acta Math. 30 (1906), 175--193.
-/

public section

namespace TauCeti

open Set

/-- On `[0, 1]`, an upper semicontinuous midpoint-convex function lies below its chord: its value
at `t` is at most `(1 - t) * g 0 + t * g 1`. -/
theorem le_chord_of_midpoint {g : ℝ → ℝ} (hg : UpperSemicontinuousOn g (Icc 0 1))
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, g (midpoint ℝ s t) ≤ (g s + g t) / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : g t ≤ (1 - t) * g 0 + t * g 1 := by
  -- The gap `c` between `g` and its chord vanishes at both ends of `[0, 1]`. If it had a positive
  -- maximum, the leftmost point `t₀` attaining it would be the midpoint of two points of `[0, 1]`,
  -- one strictly to the left of `t₀`, and midpoint convexity would push `c t₀` below the maximum.
  set c : ℝ → ℝ := fun u => g u + ((u - 1) * g 0 - u * g 1) with hc_def
  have hc : UpperSemicontinuousOn c (Icc 0 1) :=
    hg.add (Continuous.continuousOn (by fun_prop)).upperSemicontinuousOn
  have hmid : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, c ((s + u) / 2) ≤ (c s + c u) / 2 := by
    intro s hs u hu
    have := h s hs u hu
    rw [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv, ← div_eq_inv_mul] at this
    simp only [hc_def]
    linarith
  suffices ∀ u ∈ Icc (0 : ℝ) 1, c u ≤ 0 by linarith [this t ht]
  by_contra! ⟨u, hu, hcu⟩
  obtain ⟨v, hv, hmax⟩ := hc.exists_isMaxOn ⟨u, hu⟩ isCompact_Icc
  rw [isMaxOn_iff] at hmax
  -- The leftmost point `t₀` of `[0, 1]` at which `c` attains its maximum `c v`.
  obtain ⟨t₀, ⟨ht₀, ht₀v : c v ≤ c t₀⟩, hleast⟩ :=
    (hc.isCompact_inter_preimage_Ici isCompact_Icc (c v)).exists_isLeast ⟨v, hv, le_rfl⟩
  have hM : 0 < c v := hcu.trans_le (hmax _ hu)
  have h0 : c 0 = 0 := by simp [hc_def]
  have h1 : c 1 = 0 := by simp [hc_def]
  have ht₀0 : 0 < t₀ := ht₀.1.lt_of_ne (by rintro rfl; linarith)
  have ht₀1 : t₀ < 1 := ht₀.2.lt_of_ne (by rintro rfl; linarith)
  set δ := min t₀ (1 - t₀)
  have hδ : 0 < δ := lt_min ht₀0 (by linarith)
  have hδl : δ ≤ t₀ := min_le_left _ _
  have hδr : δ ≤ 1 - t₀ := min_le_right _ _
  have hl : t₀ - δ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hr : t₀ + δ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- Strictly left of `t₀`, the gap `c` is strictly below its maximum.
  have hlt : c (t₀ - δ) < c v := lt_of_not_ge fun hge => by linarith [hleast ⟨hl, hge⟩]
  have := hmid _ hl _ hr
  rw [show (t₀ - δ + (t₀ + δ)) / 2 = t₀ by ring] at this
  linarith [hmax _ hr]

/-- **Jensen's theorem.** On a convex subset of a real topological vector space, an upper
semicontinuous function that is midpoint convex is convex. In particular, so is a continuous one. -/
theorem convexOn_of_midpoint {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ} (hs : Convex ℝ s)
    (hf : UpperSemicontinuousOn f s)
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
