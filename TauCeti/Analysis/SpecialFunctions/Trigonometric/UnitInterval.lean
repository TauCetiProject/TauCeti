/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Trigonometric functions on the unit interval

The cosine `t ↦ cos (π t)` is injective on the unit interval `I`, and the sine `t ↦ sin (π t)` is
positive on its interior. The point `(cos 2πt, sin 2πt)` runs once around the unit circle as `t`
runs over `I`: it reaches every point, it is `(1, 0)` only at the end points, and it is injective
away from the end points.

## Main declarations

* `TauCeti.cos_pi_mul_injective`: `t ↦ cos (π t)` is injective on `I`.
* `TauCeti.sin_pi_mul_pos`: `sin (π t) > 0` for `t ∈ I` different from `0` and `1`.
* `TauCeti.exists_cos_sin_two_pi_mul_eq`, `TauCeti.eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one` and
  `TauCeti.eq_or_of_cos_sin_two_pi_mul_eq`: `t ↦ (cos 2πt, sin 2πt)` covers the unit circle, meets
  `(1, 0)` only at the end points of `I`, and identifies only the two end points.
-/

public section

open Real
open scoped unitInterval

namespace TauCeti

/-- `t ↦ cos (π t)` is injective on the unit interval. -/
theorem cos_pi_mul_injective : Function.Injective (fun t : I => cos (π * t)) := by
  intro a b h
  refine Subtype.ext (mul_left_cancel₀ pi_ne_zero (Real.injOn_cos ?_ ?_ h))
  · exact ⟨by positivity [a.2.1], mul_le_of_le_one_right pi_pos.le a.2.2⟩
  · exact ⟨by positivity [b.2.1], mul_le_of_le_one_right pi_pos.le b.2.2⟩

/-- `sin (π t)` is positive on the open unit interval. -/
theorem sin_pi_mul_pos {t : I} (h0 : t ≠ 0) (h1 : t ≠ 1) : 0 < sin (π * t) := by
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
  exact sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])

/-- Every point `(a, b)` of the unit circle is `(cos 2πt, sin 2πt)` for some `t` in the unit
interval. -/
theorem exists_cos_sin_two_pi_mul_eq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ t : I, cos (2 * π * t) = a ∧ sin (2 * π * t) = b := by
  let z : ℂ := ⟨a, b⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
    nlinarith
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hp : (0 : ℝ) < 2 * π := by positivity
  -- Reduce the argument of `z` modulo `2π` into `[0, 2π)`.
  have hr : toIcoMod hp 0 z.arg = z.arg - (toIcoDiv hp 0 z.arg : ℝ) * (2 * π) := by
    rw [toIcoMod, zsmul_eq_mul]
  have hmem := toIcoMod_mem_Ico' hp z.arg
  refine ⟨⟨toIcoMod hp 0 z.arg / (2 * π), div_nonneg hmem.1 hp.le, (div_le_one hp).2 hmem.2.le⟩,
    ?_⟩
  simp only [mul_div_cancel₀ _ hp.ne', hr, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]
  exact ⟨by rw [Complex.cos_arg hz0, hz, div_one], by rw [Complex.sin_arg, hz, div_one]⟩

/-- On the unit interval, `cos 2πt = 1` only at the end points. -/
theorem eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one {t : I} (h : cos (2 * π * t) = 1) :
    t = 0 ∨ t = 1 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
  have hnt : (n : ℝ) = t := mul_right_cancel₀ (by positivity : (2 * π) ≠ 0) (by linarith)
  have h0 : 0 ≤ n := by exact_mod_cast hnt ▸ t.2.1
  have h1 : n ≤ 1 := by exact_mod_cast hnt ▸ t.2.2
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact Or.inl (Subtype.ext (by simpa using hnt.symm))
  · exact Or.inr (Subtype.ext (by simpa using hnt.symm))

/-- On the unit interval, `cos 2πt` and `sin 2πt` determine `t`, except that they agree at the two
end points. -/
theorem eq_or_of_cos_sin_two_pi_mul_eq {s t : I} (hc : cos (2 * π * s) = cos (2 * π * t))
    (hs : sin (2 * π * s) = sin (2 * π * t)) : s = t ∨ s = 0 ∧ t = 1 ∨ s = 1 ∧ t = 0 := by
  obtain ⟨n, hn⟩ := Real.exists_int_eq_add_of_cos_sin_eq hc hs
  have hs0 := s.2.1
  have hs1 := s.2.2
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hlo : (-1 : ℝ) ≤ n := by linarith
  have hhi : (n : ℝ) ≤ 1 := by linarith
  have hlo' : -1 ≤ n := by exact_mod_cast hlo
  have hhi' : n ≤ 1 := by exact_mod_cast hhi
  obtain rfl | rfl | rfl : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  · push_cast at hn
    exact Or.inr (Or.inl ⟨Subtype.ext (by rw [Set.Icc.coe_zero]; linarith),
      Subtype.ext (by rw [Set.Icc.coe_one]; linarith)⟩)
  · exact Or.inl (Subtype.ext (by simpa using hn))
  · push_cast at hn
    exact Or.inr (Or.inr ⟨Subtype.ext (by rw [Set.Icc.coe_one]; linarith),
      Subtype.ext (by rw [Set.Icc.coe_zero]; linarith)⟩)

end TauCeti
