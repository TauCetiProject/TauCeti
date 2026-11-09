/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Ray
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.LocallyConvex.Separation

/-!
# Short secants across a corner

Let `γ₁` and `γ₂` be two curves in a real normed space which meet at `γ₁ 0 = γ₂ 0`: think of
`γ₁` as the arc arriving at a corner, with left derivative `v₁` at `0`, and of `γ₂` as the arc
leaving it, with right derivative `v₂` at `0`. Suppose that `v₁` and `v₂` do not point in
opposite directions, `¬SameRay ℝ v₁ (-v₂)`, so that the corner is not a cusp; straight joins
and corners of either sign are allowed. Then a single continuous linear functional `L` is
positive on both tangent vectors and on every short secant `γ₂ (t + r) - γ₁ t`, `-r ≤ t ≤ 0`,
from the arriving arc to the leaving one across the corner: all these secants lie in one open
half-space.

These secants are the velocities of the moving-average rounding of a corner: if the continuous
curve `γ` is `γ₁` on `t ≤ 0` and `γ₂` on `t ≥ 0`, the `C¹` curve `c s = (2ρ)⁻¹ ∫ γ` over
`[s - ρ, s + ρ]` has `c' s = (2ρ)⁻¹ (γ (s + ρ) - γ (s - ρ))`, which for `|s| ≤ ρ` is such a
secant with `r = 2ρ` and `t = s - ρ`. So the rounded curve is regular near the corner and its
tangent stays in one open half-plane there; its turning across the corner is the angle in
`(-π, π)` between two secant directions tending to `v₁` and `v₂`. The same secants appear in
Hopf's secant proof of the theorem of turning tangents for curves with corners.

## Main results

* `TauCeti.exists_strongDual_pos_secant_of_not_sameRay_neg`: the short secants across a corner
  lie in an open half-space containing both tangent vectors.

The two tangent vectors are first separated from `0` by
`TauCeti.exists_strongDual_pos_of_not_sameRay_neg`; the one-sided slopes of `L ∘ γ₁` and
`L ∘ γ₂` at `0` then make both pieces of `L (γ₂ (t + r) - γ₁ t)` nonnegative.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2
  (1935), 50–62.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Short secants across a corner lie in an open half-space.** Let `γ₁` have left derivative
`v₁` and `γ₂` right derivative `v₂` at `0`, with `γ₁ 0 = γ₂ 0`, and with `v₁` and `v₂` not
pointing in opposite directions. Then there are `δ > 0` and a continuous linear functional `L`,
positive on both tangent vectors, such that `0 < L (γ₂ (t + r) - γ₁ t)` whenever `0 < r < δ` and
`-r ≤ t ≤ 0`. -/
theorem exists_strongDual_pos_secant_of_not_sameRay_neg {γ₁ γ₂ : ℝ → E} {v₁ v₂ : E}
    (h₁ : HasDerivWithinAt γ₁ v₁ (Iic 0) 0) (h₂ : HasDerivWithinAt γ₂ v₂ (Ici 0) 0)
    (h₀ : γ₁ 0 = γ₂ 0) (hne : ¬SameRay ℝ v₁ (-v₂)) :
    ∃ δ > 0, ∃ L : StrongDual ℝ E, 0 < L v₁ ∧ 0 < L v₂ ∧
      ∀ r ∈ Ioo (0 : ℝ) δ, ∀ t ∈ Icc (-r) 0, 0 < L (γ₂ (t + r) - γ₁ t) := by
  obtain ⟨L, hL₁, hL₂⟩ := exists_strongDual_pos_of_not_sameRay_neg hne
  -- The one-sided slopes of `L ∘ γᵢ` at `0` tend to `L vᵢ > 0`, so they are eventually positive.
  have hs₁ : ∀ᶠ t in 𝓝[<] 0, 0 < slope (L ∘ γ₁) 0 t := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp (L.hasFDerivAt.comp_hasDerivWithinAt 0 h₁)
    rw [Iic_sdiff_right] at h
    exact h.eventually (lt_mem_nhds hL₁)
  have hs₂ : ∀ᶠ t in 𝓝[>] 0, 0 < slope (L ∘ γ₂) 0 t := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp (L.hasFDerivAt.comp_hasDerivWithinAt 0 h₂)
    rw [Ici_sdiff_left] at h
    exact h.eventually (lt_mem_nhds hL₂)
  obtain ⟨a, ha, hsa⟩ := Metric.mem_nhdsWithin_iff.mp hs₁
  obtain ⟨b, hb, hsb⟩ := Metric.mem_nhdsWithin_iff.mp hs₂
  have hlt₁ {t : ℝ} (ht : t ∈ Ioo (-a) 0) : L (γ₁ t) < L (γ₁ 0) := by
    have h := hsa ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;>
      linarith [ht.1, ht.2], ht.2⟩
    rw [mem_ofPred_eq, slope_def_field, sub_zero] at h
    have h' := ((div_pos_iff.mp h).resolve_left fun h' => by linarith [h'.2, ht.2]).1
    simp only [Function.comp_apply] at h'
    linarith
  have hlt₂ {s : ℝ} (hs : s ∈ Ioo 0 b) : L (γ₂ 0) < L (γ₂ s) := by
    have h := hsb ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;>
      linarith [hs.1, hs.2], hs.1⟩
    rw [mem_ofPred_eq, slope_def_field, sub_zero] at h
    have h' := (div_pos_iff_of_pos_right hs.1).mp h
    simp only [Function.comp_apply] at h'
    linarith
  refine ⟨min a b, lt_min ha hb, L, hL₁, hL₂, fun r hr t ht => ?_⟩
  have hra : r < a := hr.2.trans_le (min_le_left _ _)
  have hrb : r < b := hr.2.trans_le (min_le_right _ _)
  have hL₀ : L (γ₁ 0) = L (γ₂ 0) := by rw [h₀]
  rw [map_sub, sub_pos]
  rcases ht.2.lt_or_eq with htlt | rfl
  · have h₁ : L (γ₁ t) < L (γ₁ 0) := hlt₁ ⟨by linarith [ht.1], htlt⟩
    rcases ht.1.lt_or_eq with htr | htr
    · linarith [hlt₂ (s := t + r) ⟨by linarith, by linarith⟩]
    · subst htr
      rw [neg_add_cancel]
      linarith
  · linarith [hlt₂ (s := 0 + r) ⟨by linarith [hr.1], by linarith⟩]

end TauCeti
