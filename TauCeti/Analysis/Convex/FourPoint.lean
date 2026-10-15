/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Four-point inequalities for convex functions

If two points lie between two endpoints and have the same sum as those endpoints, convexity
bounds the sum of their function values by the sum at the endpoints. For ordered real points
`x₁ ≤ x₂` and `y₁ ≤ y₂`, the uncrossed displacements `x₁ - y₁` and `x₂ - y₂` lie between the
crossed displacements `x₁ - y₂` and `x₂ - y₁` and have the same sum. Thus convex displacement
costs satisfy the Monge four-point inequality. In particular this holds for `|x - y| ^ p` when
`1 ≤ p`, the inequality used in uncrossing finite transport plans.

## References

* C. Villani, *Topics in Optimal Transportation*, AMS 2003, §2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
-/

public section

namespace TauCeti

/-- Convexity bounds the sum at two intermediate points by the sum at two endpoints whenever
both pairs have the same sum. Only the endpoints need to be assumed in the convex domain. -/
theorem add_le_add_of_convexOn_of_add_eq {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜} (hf : ConvexOn 𝕜 s f)
    {a b c d : 𝕜} (hc : c ∈ s) (hd : d ∈ s) (hca : c ≤ a) (had : a ≤ d)
    (hsum : a + b = c + d) : f a + f b ≤ f c + f d := by
  rcases eq_or_lt_of_le (hca.trans had) with hcd | hcd
  · have ha : a = c := by order
    have hb : b = d := by rw [ha] at hsum; exact add_left_cancel hsum
    simp [ha, hb, hcd]
  · let u := (d - a) / (d - c)
    let v := (a - c) / (d - c)
    have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr had) (sub_pos.mpr hcd).le
    have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hca) (sub_pos.mpr hcd).le
    have huv : u + v = 1 := by dsimp [u, v]; field_simp; ring
    have ha : u * c + v * d = a := by dsimp [u, v]; field_simp; ring
    have hb : v * c + u * d = b := by
      dsimp [u, v]
      field_simp
      nlinarith [hsum]
    have h₁ := hf.2 hc hd hu hv huv
    have h₂ := hf.2 hc hd hv hu (by linarith)
    simp only [smul_eq_mul, ha, hb] at h₁ h₂
    calc
      f a + f b ≤ (u * f c + v * f d) + (v * f c + u * f d) := add_le_add h₁ h₂
      _ = f c + f d := by
        linear_combination (f c + f d) * huv

/-- Convex displacement costs satisfy the Monge four-point inequality on ordered points.
The convexity domain need only contain the two extreme, crossed displacements. -/
theorem add_sub_le_add_sub_of_convexOn {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜} (hf : ConvexOn 𝕜 s f)
    {x₁ x₂ y₁ y₂ : 𝕜} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (h₁ : x₁ - y₂ ∈ s) (h₂ : x₂ - y₁ ∈ s) :
    f (x₁ - y₁) + f (x₂ - y₂) ≤ f (x₁ - y₂) + f (x₂ - y₁) := by
  exact add_le_add_of_convexOn_of_add_eq hf h₁ h₂ (by linarith) (by linarith) (by ring)

/-- The power-distance cost `|x - y| ^ p` satisfies the Monge four-point inequality for every
real exponent `1 ≤ p`. This includes the non-strict endpoint `p = 1` and coincident points. -/
theorem abs_sub_rpow_add_abs_sub_rpow_le {p x₁ x₂ y₁ y₂ : ℝ} (hp : 1 ≤ p)
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    |x₁ - y₁| ^ p + |x₂ - y₂| ^ p ≤ |x₁ - y₂| ^ p + |x₂ - y₁| ^ p := by
  have hf : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    have hnorm := (convexOn_univ_norm (E := ℝ)).2 (Set.mem_univ x) (Set.mem_univ y)
      ha hb hab
    have hpow := (convexOn_rpow hp).2 (abs_nonneg x) (abs_nonneg y) ha hb hab
    simp only [Real.norm_eq_abs, smul_eq_mul] at hnorm hpow ⊢
    exact (Real.rpow_le_rpow (abs_nonneg _) hnorm (zero_le_one.trans hp)).trans hpow
  exact add_sub_le_add_sub_of_convexOn hf hx hy (Set.mem_univ _) (Set.mem_univ _)

end TauCeti
