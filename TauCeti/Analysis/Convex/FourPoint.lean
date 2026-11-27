/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Mul
import TauCeti.Analysis.Convex.StrictConvexSpace

/-!
# Four-point inequalities for convex functions

If two points lie between two endpoints and have the same sum as those endpoints, convexity
bounds the sum of their function values by the sum at the endpoints. For ordered real points
`x₁ ≤ x₂` and `y₁ ≤ y₂`, the uncrossed displacements `x₁ - y₁` and `x₂ - y₂` lie between the
crossed displacements `x₁ - y₂` and `x₂ - y₁` and have the same sum. Thus convex displacement
costs satisfy the Monge four-point inequality. In particular this holds for `|x - y| ^ p` when
`1 ≤ p`, the inequality used in uncrossing finite transport plans.

`Real.norm_one_div_add_pow_add_one_div_add_sub_pow_le` uses Mathlib's `convexOn_zpow`
and `TauCeti.add_le_add_of_convexOn_of_add_eq` to bound paired reciprocal powers by their
sum at the endpoints.

## References

* C. Villani, *Topics in Optimal Transportation*, AMS 2003, §2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
-/

public section

namespace TauCeti

variable {𝕜 β : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β]

/-- Convexity bounds the sum at two intermediate points by the sum at two endpoints whenever
both pairs have the same sum. The function may take values in any ordered additive monoid that is
a `𝕜`-module, and only the endpoints need to be assumed in the convex domain. -/
theorem add_le_add_of_convexOn_of_add_eq {s : Set 𝕜} {f : 𝕜 → β} (hf : ConvexOn 𝕜 s f)
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
      f a + f b ≤ (u • f c + v • f d) + (v • f c + u • f d) := add_le_add h₁ h₂
      _ = f c + f d := by
        match_scalars <;> linear_combination huv

/-- Convex displacement costs satisfy the Monge four-point inequality on ordered points.
The convexity domain need only contain the two extreme, crossed displacements. -/
theorem add_sub_le_add_sub_of_convexOn {s : Set 𝕜} {f : 𝕜 → β} (hf : ConvexOn 𝕜 s f)
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
    simpa only [Real.norm_eq_abs] using convexOn_norm_rpow (E := ℝ) hp
  exact add_sub_le_add_sub_of_convexOn hf hx hy (Set.mem_univ _) (Set.mem_univ _)

end TauCeti

namespace Real

open Set

/-- Moving two positive bases towards one another with their sum fixed bounds the
norm of the sum of their reciprocal powers by the original reciprocal-power sum. -/
theorem norm_one_div_add_pow_add_one_div_add_sub_pow_le {a s t : ℝ}
    (ha : 0 < a) (ht : t ∈ Icc 0 s) (k : ℕ) :
    ‖1 / (a + t) ^ k + 1 / (a + s - t) ^ k‖ ≤ 1 / a ^ k + 1 / (a + s) ^ k := by
  have hf : ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ 1 / x ^ k) := by
    simpa only [zpow_neg, zpow_natCast, one_div] using (convexOn_zpow (𝕜 := ℝ) (-(k : ℤ)))
  have ht₀ : 0 ≤ t := ht.1
  have hb : 0 < a + s := by linarith [ht.2]
  have hb' : 0 < a + s - t := by linarith [ht.2]
  rw [norm_of_nonneg (by positivity)]
  exact TauCeti.add_le_add_of_convexOn_of_add_eq hf ha hb (by linarith)
    (by linarith [ht.2]) (by ring)

end Real
