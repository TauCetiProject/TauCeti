/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Local images of real-symmetric complex coordinates

A complex coordinate commuting with conjugation near a real point and having positive real
strict derivative preserves the upper side of the real axis locally. Its image of a small upper
half-disc agrees with the upper half-plane in a neighbourhood of the image of the centre.
In particular, upper half-disc coverage is a consequence of the derivative and symmetry,
rather than an additional assumption on the coordinate.

The strict derivative controls differences between a point and its conjugate. This gives a
uniform sign estimate even for approaches tangential to the real axis. Holomorphic coordinates
satisfy the strict differentiability hypothesis; the result applies to the exponential
coordinates compactifying logarithmic Schwarz--Christoffel ends.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate NNReal

namespace HasStrictDerivAt

variable {f : ℂ → ℂ} {x d : ℝ}

/-- A real-symmetric complex map with positive real strict derivative preserves the sign of
the upper-half-plane condition near a real point, including tangential approaches. -/
theorem eventually_im_pos_iff_of_conj (hf : HasStrictDerivAt f (d : ℂ) (x : ℂ))
    (hd : 0 < d) (hsym : ∀ᶠ z in 𝓝 (x : ℂ), f (conj z) = conj (f z)) :
    ∀ᶠ z in 𝓝 (x : ℂ), 0 < (f z).im ↔ 0 < z.im := by
  obtain ⟨s, hs, happrox⟩ := hf.hasStrictFDerivAt.approximates_deriv_on_nhds
    (c := (d / 2).toNNReal) (Or.inr (Real.toNNReal_pos.mpr (half_pos hd)))
  have hconj : Tendsto conj (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
    simpa using continuous_conj.tendsto (x : ℂ)
  filter_upwards [hs, hconj.eventually hs, hsym] with z hz hzc hsymz
  have hbound := (abs_im_le_norm _).trans (happrox z hz (conj z) hzc)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, sub_im, mul_im,
    ofReal_re, ofReal_im, hsymz, conj_im, ← dist_eq_norm, dist_self_conj, mul_zero, zero_add,
    Real.coe_toNNReal _ (half_pos hd).le] at hbound
  rcases abs_le.mp hbound with ⟨hl, hu⟩
  cases abs_cases z.im <;> constructor <;> intro <;> nlinarith

/-- A real-symmetric complex map with positive real strict derivative is injective on a
disc of radius less than any prescribed `R > 0`, and on that disc it preserves the sign of the
upper-half-plane condition. Inside a sufficiently small target disc, its image of the source
upper half-disc is exactly the target upper half-disc. The discs are centred at `x` and `f x`;
no image or half-plane preservation hypothesis is required. -/
theorem exists_ball_image_inter_upperHalfPlane_of_conj
    (hf : HasStrictDerivAt f (d : ℂ) (x : ℂ)) (hd : 0 < d)
    (hsym : ∀ᶠ z in 𝓝 (x : ℂ), f (conj z) = conj (f z)) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo 0 R, InjOn f (ball (x : ℂ) r) ∧
      (∀ z ∈ ball (x : ℂ) r, 0 < (f z).im ↔ 0 < z.im) ∧
      ∃ δ : ℝ, 0 < δ ∧
        (f '' (ball (x : ℂ) r ∩ upperHalfPlaneSet)) ∩ ball (f x) δ =
          ball (f x) δ ∩ upperHalfPlaneSet := by
  have hdC : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
  have hleft := hf.eventually_left_inverse hdC
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.eventually_nhds_iff.mp
    (hleft.and (hf.eventually_im_pos_iff_of_conj hd hsym))
  let r := min r₀ (R / 2)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hball : ∀ z ∈ ball (x : ℂ) r,
      hf.localInverse f (d : ℂ) (x : ℂ) hdC (f z) = z ∧
        (0 < (f z).im ↔ 0 < z.im) :=
    fun _ hz => hball₀ (ball_subset_ball (min_le_left _ _) hz)
  have hinj : InjOn f (ball (x : ℂ) r) := by
    intro z hz w hw hzw
    rw [← (hball z hz).1, ← (hball w hw).1, hzw]
  have himage : f '' ball (x : ℂ) r ∈ 𝓝 (f x) := by
    rw [← hf.map_nhds_eq hdC]
    exact Filter.image_mem_map (ball_mem_nhds _ hr)
  obtain ⟨δ, hδ, htarget⟩ := Metric.mem_nhds_iff.mp himage
  refine ⟨r, ⟨hr, hrR⟩, hinj, fun z hz => (hball z hz).2, δ, hδ, ?_⟩
  ext w
  constructor
  · rintro ⟨⟨z, ⟨hz, hzim⟩, rfl⟩, hw⟩
    exact ⟨hw, (hball z hz).2.mpr hzim⟩
  · rintro ⟨hw, hwim⟩
    obtain ⟨z, hz, rfl⟩ := htarget hw
    exact ⟨⟨z, ⟨hz, (hball z hz).2.mp hwim⟩, rfl⟩, hw⟩

end HasStrictDerivAt
