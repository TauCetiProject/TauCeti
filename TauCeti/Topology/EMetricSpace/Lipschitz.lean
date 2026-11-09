/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Lipschitz maps from extended metric spaces

This file gives a real-valued Lipschitz estimate for the extended distance from a fixed point,
and shows that composing a function locally Lipschitz on a set with a locally Lipschitz map keeps
it locally Lipschitz on that set.

It also glues Lipschitz bounds for curves along adjacent pieces of the real line. A curve that is
`K`-Lipschitz on a set `s` and on a set `t` to its right, the two sets sharing the point `c`, is
`K`-Lipschitz on `s ∪ t` (`LipschitzOnWith.union`): for `x ∈ s` and `y ∈ t`, the triangle
inequality through `c` costs nothing because `|x - y| = |x - c| + |c - y|`. In particular a curve
that is `K`-Lipschitz on `[a, b]` and on `[b, c]` is `K`-Lipschitz on `[a, c]`
(`LipschitzOnWith.Icc_Icc`), and two curves with a common Lipschitz constant on adjacent intervals
that agree at the junction concatenate into a curve with the same constant
(`LipschitzOnWith.if_le`). The target may be any pseudo-emetric space, for instance a domain
carrying its intrinsic extended metric.

The declaration `TauCeti.lipschitzWith_toReal_edist` and its proof follow
[Mathlib pull request #41839](https://github.com/leanprover-community/mathlib4/pull/41839),
available under Apache 2.0.
-/

public section

open Filter
open scoped ENNReal

namespace TauCeti

/-- Distance from a fixed point, converted to a real number, is `1`-Lipschitz. -/
theorem lipschitzWith_toReal_edist {X : Type*} [PseudoEMetricSpace X] (a : X) :
    LipschitzWith 1 (fun x ↦ (edist a x).toReal) := by
  intro x y
  by_cases hxy : edist x y = ∞
  · simp [hxy]
  have hxy' : edist y x ≠ ∞ := by simpa only [edist_comm] using hxy
  by_cases hax : edist a x = ∞
  · have hay : edist a y = ∞ := by
      by_contra hay
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hay, hxy'⟩) (edist_triangle a y x) hax
    simp [hax, hay]
  have hay : edist a y ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hax, hxy⟩) (edist_triangle a x y)
  suffices ENNReal.ofReal (dist (edist a x).toReal (edist a y).toReal) ≤ edist x y by
    simpa only [edist_dist, ENNReal.coe_one, one_mul] using this
  rw [ENNReal.ofReal_le_iff_le_toReal hxy, Real.dist_eq, abs_le]
  have hforward := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hax, hxy⟩)
    (edist_triangle a x y)
  have hbackward := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hay, hxy'⟩)
    (edist_triangle a y x)
  rw [ENNReal.toReal_add hax hxy] at hforward
  rw [ENNReal.toReal_add hay hxy', edist_comm y x] at hbackward
  constructor <;> linarith

end TauCeti

/-- A locally Lipschitz map composed with a function locally Lipschitz on `s` is locally Lipschitz
on `s`. -/
theorem LocallyLipschitz.comp_locallyLipschitzOn {α β γ : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {g : β → γ} {f : α → β} {s : Set α}
    (hg : LocallyLipschitz g) (hf : LocallyLipschitzOn s f) : LocallyLipschitzOn s (g ∘ f) := by
  intro x hx
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, U, hU, hKg⟩ := hg (f x)
  refine ⟨Kg * Kf, t ∩ f ⁻¹' U, inter_mem ht (hf.continuousOn x hx hU), ?_⟩
  exact hKg.comp (hKf.mono Set.inter_subset_left) fun _ hy => hy.2

section Interval

open Set
open scoped NNReal

variable {X : Type*} [PseudoEMetricSpace X] {K : ℝ≥0} {f : ℝ → X}

/-- A curve that is `K`-Lipschitz on a set `s` and on a set `t`, where `c` is the greatest element
of `s` and the least element of `t`, is `K`-Lipschitz on `s ∪ t`. -/
protected theorem LipschitzOnWith.union {s t : Set ℝ} {c : ℝ} (hs : LipschitzOnWith K f s)
    (ht : LipschitzOnWith K f t) (hsc : IsGreatest s c) (htc : IsLeast t c) :
    LipschitzOnWith K f (s ∪ t) := by
  have key {x y : ℝ} (hx : x ∈ s) (hy : y ∈ t) : edist (f x) (f y) ≤ K * edist x y := by
    have hxc : x ≤ c := hsc.2 hx
    have hcy : c ≤ y := htc.2 hy
    have hsum : edist x c + edist c y = edist x y := by
      simp only [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxc),
        abs_of_nonpos (sub_nonpos.mpr hcy), abs_of_nonpos (sub_nonpos.mpr (hxc.trans hcy)),
        neg_sub]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hxc) (sub_nonneg.mpr hcy), sub_add_sub_cancel']
    calc edist (f x) (f y) ≤ edist (f x) (f c) + edist (f c) (f y) := edist_triangle _ _ _
      _ ≤ K * edist x c + K * edist c y := add_le_add (hs hx hsc.1) (ht htc.1 hy)
      _ = K * edist x y := by rw [← mul_add, hsum]
  rintro x (hx | hx) y (hy | hy)
  · exact hs hx hy
  · exact key hx hy
  · rw [edist_comm, edist_comm x]
    exact key hy hx
  · exact ht hx hy

/-- A curve that is `K`-Lipschitz on `[a, b]` and on `[b, c]` is `K`-Lipschitz on `[a, c]`. -/
theorem LipschitzOnWith.Icc_Icc {a b c : ℝ} (hab : LipschitzOnWith K f (Icc a b))
    (hbc : LipschitzOnWith K f (Icc b c)) : LipschitzOnWith K f (Icc a c) := by
  rcases le_total a b with h₁ | h₁
  · rcases le_total b c with h₂ | h₂
    · rw [← Icc_union_Icc_eq_Icc h₁ h₂]
      exact hab.union hbc (isGreatest_Icc h₁) (isLeast_Icc h₂)
    · exact hab.mono (Icc_subset_Icc_right h₂)
  · exact hbc.mono (Icc_subset_Icc_left h₁)

/-- Two curves that are `K`-Lipschitz on `[a, c]` and on `[c, b]` respectively and agree at `c`
concatenate into a curve that is `K`-Lipschitz on `[a, b]`. -/
theorem LipschitzOnWith.if_le {g : ℝ → X} {a b c : ℝ} (hf : LipschitzOnWith K f (Icc a c))
    (hg : LipschitzOnWith K g (Icc c b)) (hfg : f c = g c) :
    LipschitzOnWith K (fun t ↦ if t ≤ c then f t else g t) (Icc a b) := by
  have heq : ∀ t ∈ Icc c b, (if t ≤ c then f t else g t) = g t := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hct
    · simp [hfg]
    · simp [hct.not_ge]
  refine LipschitzOnWith.Icc_Icc (b := c) (fun x hx y hy ↦ ?_) fun x hx y hy ↦ ?_
  · simpa only [ite_eq_left hx.2, ite_eq_left hy.2] using hf hx hy
  · rw [heq x hx, heq y hy]
    exact hg hx hy

end Interval
