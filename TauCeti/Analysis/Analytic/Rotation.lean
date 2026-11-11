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
theorem AnalyticAt.min_analyticOrderAt_comp_mul_sub {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E}
    (hf : AnalyticAt 𝕜 f 0) {N : ℕ} {ζ : 𝕜} (hζ : IsPrimitiveRoot ζ N) :
    min (N : ℕ∞) (analyticOrderAt (fun t ↦ f (ζ * t) - f t) 0) =
      min (N : ℕ∞) (analyticOrderAt (fun t ↦ f t - f 0) 0) := by
  have hg : AnalyticAt 𝕜 (fun t ↦ f t - f 0) 0 := hf.sub analyticAt_const
  have hrot : AnalyticAt 𝕜 (fun t ↦ ζ * t) 0 := analyticAt_const.mul analyticAt_id
  have hdiff : AnalyticAt 𝕜 (fun t ↦ f (ζ * t) - f t) 0 :=
    (hf.comp_of_eq hrot (mul_zero _)).sub hf
  -- A local factorization `f t - f 0 = t ^ k • v t` transfers to the rotation difference.
  have key {k : ℕ} {v : 𝕜 → E} (hv : AnalyticAt 𝕜 v 0)
      (heq : ∀ᶠ t in 𝓝 0, f t - f 0 = (t - 0) ^ k • v t) :
      AnalyticAt 𝕜 (fun t ↦ ζ ^ k • v (ζ * t) - v t) 0 ∧
        ∀ᶠ t in 𝓝 0, f (ζ * t) - f t = (t - 0) ^ k • (ζ ^ k • v (ζ * t) - v t) := by
    refine ⟨(hv.comp_of_eq hrot (mul_zero _)).const_smul.sub hv, ?_⟩
    have htend : Tendsto (fun t : 𝕜 ↦ ζ * t) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, mul_zero] using hrot.continuousAt
    filter_upwards [heq, htend.eventually heq] with t ht hζt
    rw [← sub_sub_sub_cancel_right (f (ζ * t)) (f t) (f 0), hζt, ht]
    module
  by_cases hge : (N : ℕ∞) ≤ analyticOrderAt (fun t ↦ f t - f 0) 0
  · obtain ⟨v, hv, heq⟩ := (natCast_le_analyticOrderAt hg).1 hge
    rw [min_eq_left ((natCast_le_analyticOrderAt hdiff).2 ⟨_, key hv heq⟩), min_eq_left hge]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt (not_le.1 hge))
    have hmN : m < N := by simpa only [← hm, Nat.cast_lt, not_le] using hge
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hg.analyticOrderAt_ne_zero.2 (sub_self _) (by rw [← hm, Nat.cast_zero])
    obtain ⟨v, hv, hv0, heq⟩ := hg.analyticOrderAt_eq_natCast.1 hm.symm
    have hv0' : ζ ^ m • v (ζ * 0) - v 0 ≠ 0 := by
      simpa only [mul_zero, sub_smul, one_smul] using
        smul_ne_zero (sub_ne_zero.2 (hζ.pow_ne_one_of_pos_of_lt hm0 hmN)) hv0
    rw [hdiff.analyticOrderAt_eq_natCast.2 ⟨_, (key hv heq).1, hv0', (key hv heq).2⟩, hm]
