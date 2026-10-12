/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Vanishing order under a root-of-unity rotation

For an analytic germ `f` and a primitive `N`th root of unity `ζ`, the difference
`f (ζ * t) - f t` detects every nonconstant term of degree less than `N`.
Thus its order, capped at `N`, equals the capped order of `f t - f 0`.
This converts contacts of ramified root branches with their central values into
contacts between branches permuted by rotation.
-/

public section

open Filter Topology

/-- Rotation by a primitive `N`th root detects the first nonconstant term below degree `N`.
The equality remains valid for a constant germ and for contact order at least `N`. -/
theorem AnalyticAt.min_analyticOrderAt_comp_mul_sub {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f 0)
    {N : ℕ} {ζ : 𝕜} (hζ : IsPrimitiveRoot ζ N) :
    min (N : ℕ∞) (analyticOrderAt (fun t ↦ f (ζ * t) - f t) 0) =
      min (N : ℕ∞) (analyticOrderAt (fun t ↦ f t - f 0) 0) := by
  let g : 𝕜 → 𝕜 := fun t ↦ f t - f 0
  have hg : AnalyticAt 𝕜 g 0 := hf.sub analyticAt_const
  have hrot : AnalyticAt 𝕜 (fun t ↦ ζ * t) 0 := analyticAt_const.mul analyticAt_id
  have htend : Tendsto (fun t : 𝕜 ↦ ζ * t) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, mul_zero] using hrot.continuousAt
  have hdiff : AnalyticAt 𝕜 (fun t ↦ f (ζ * t) - f t) 0 :=
    (hf.comp_of_eq hrot (mul_zero _)).sub hf
  by_cases hge : (N : ℕ∞) ≤ analyticOrderAt g 0
  · obtain ⟨v, hv, heq⟩ := (natCast_le_analyticOrderAt hg).1 hge
    have hbound : (N : ℕ∞) ≤ analyticOrderAt (fun t ↦ f (ζ * t) - f t) 0 := by
      apply (natCast_le_analyticOrderAt hdiff).2
      refine ⟨fun t ↦ ζ ^ N * v (ζ * t) - v t,
        (analyticAt_const.mul (hv.comp_of_eq hrot (mul_zero _))).sub hv, ?_⟩
      filter_upwards [heq, htend.eventually heq] with t ht hζt
      simp only [g, sub_zero, smul_eq_mul, mul_pow] at ht hζt ⊢
      rw [← sub_sub_sub_cancel_right (f (ζ * t)) (f t) (f 0), hζt, ht]
      ring
    exact (min_eq_left hbound).trans (min_eq_left hge).symm
  · have hlt : analyticOrderAt g 0 < (N : ℕ∞) := lt_of_not_ge hge
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hmN : m < N := by simpa only [← hm, Nat.cast_lt] using hlt
    have hm0 : m ≠ 0 := by
      intro hz
      have := hg.analyticOrderAt_eq_zero.1 (by rw [← hm, hz]; rfl)
      exact this (sub_self _)
    obtain ⟨v, hv, hv0, heq⟩ := hg.analyticOrderAt_eq_natCast.1 hm.symm
    have horder : analyticOrderAt (fun t ↦ f (ζ * t) - f t) 0 = m := by
      apply hdiff.analyticOrderAt_eq_natCast.2
      refine ⟨fun t ↦ ζ ^ m * v (ζ * t) - v t,
        (analyticAt_const.mul (hv.comp_of_eq hrot (mul_zero _))).sub hv, ?_, ?_⟩
      · simpa only [mul_zero] using
          sub_ne_zero.2 (fun h ↦ hζ.pow_ne_one_of_pos_of_lt hm0 hmN
            (mul_right_cancel₀ hv0 (by simpa only [one_mul] using h)))
      · filter_upwards [heq, htend.eventually heq] with t ht hζt
        simp only [g, sub_zero, smul_eq_mul, mul_pow] at ht hζt ⊢
        rw [← sub_sub_sub_cancel_right (f (ζ * t)) (f t) (f 0), hζt, ht]
        ring
    rw [horder, ← hm]
