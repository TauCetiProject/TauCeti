/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Normalising a real angle into `[0, 2π)`

`Real.Angle` is `ℝ` modulo `2π`, and `toIcoMod Real.two_pi_pos 0` is the section of the quotient
map picking the representative in `[0, 2π)`. Mathlib records one direction of the relationship
between the two, as `Real.Angle.coe_toIcoMod`: normalising and then projecting to `Real.Angle`
changes nothing.

This file records that the section is *injective on angles* — the normalisations of two reals
agree exactly when the reals agree in `Real.Angle`. That is the transport step behind any
computation of a normalised angle: the identity is proved in `Real.Angle`, where `2π` is
invisible, and then read back as an equality of representatives.

It also records how the representative `Real.Angle.toReal ∈ (-π, π]` behaves on differences of
angles of the same sign, the difference counterpart of Mathlib's `toReal_add_of_sign_eq_neg_sign`,
and on sums of two angles that add up to a third angle plus `π`.

For integers `m ≠ 0` and `n`, the cosine of `2 n π / m` is one exactly when `m ∣ n`; this bounds
the order of the rank-two rotations in the geometric representation of a Coxeter group.

## Main results

* `Real.exists_int_eq_add_of_cos_sin_eq`: reals whose `cos` and `sin` at `2π` times them agree
  differ by an integer.
* `Real.cos_two_mul_pi_div_eq_one_iff_dvd`: for integers `m ≠ 0` and `n`,
  `cos (2 n (π / m)) = 1` exactly when `m ∣ n`.
* `Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq`: two reals have the same `[0, 2π)` representative
  exactly when they are equal in `Real.Angle`.
* `Real.Angle.toReal_sub_of_sign_eq`: for angles of the same sign, the subtracted one not `π`,
  `toReal` of the difference is the difference of the `toReal`s.
* `Real.Angle.sign_sub_pos_iff_toReal_lt_of_sign_eq`: for angles of the same nonzero sign, the
  difference has positive sign exactly when the representatives increase.
* `Real.Angle.toReal_add_toReal_eq_add_pi_or_eq_sub_pi`: if `θ₁ + θ₂ = θ + π`, then the sum of the
  representatives of `θ₁` and `θ₂` is that of `θ` plus or minus `π`; the sign is `+` exactly when
  this sum is positive (`Real.Angle.toReal_add_toReal_eq_add_pi_iff`) and `-` exactly when it is
  nonpositive (`Real.Angle.toReal_add_toReal_eq_sub_pi_iff`).
* `Real.Angle.eq_two_mul_of_abs_toReal_eq`: if `θ + α = β ∈ (0, 2π)` with `|θ| = α`, then
  `β = 2α`.
-/

public section

/-- **Equal angles are exactly equal normalisations.** Two reals agree in `Real.Angle` — that is,
differ by an integer multiple of `2π` — exactly when their representatives in `[0, 2π)` agree,
since the normalisation discards precisely such a multiple.

The forward direction is Mathlib's `Real.Angle.coe_toIcoMod` applied on both sides; the reverse
shifts one argument by the multiple and uses `toIcoMod_add_zsmul`. -/
theorem Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq {x y : ℝ} :
    toIcoMod Real.two_pi_pos 0 x = toIcoMod Real.two_pi_pos 0 y ↔
      (x : Real.Angle) = (y : Real.Angle) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Real.Angle.coe_toIcoMod x 0, ← Real.Angle.coe_toIcoMod y 0, h]
  · obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    have hshift : x = y + k • (2 * Real.pi) := by rw [zsmul_eq_mul]; linarith
    rw [hshift, toIcoMod_add_zsmul]

/-- The representative of a difference of two angles of the same sign is the difference of the
representatives, provided the subtracted angle is not `π`. -/
theorem Real.Angle.toReal_sub_of_sign_eq {θ ψ : Real.Angle} (hψ : ψ ≠ ↑Real.pi)
    (hs : θ.sign = ψ.sign) : (θ - ψ).toReal = θ.toReal - ψ.toReal := by
  have hψ' : -ψ ≠ ↑Real.pi := fun h ↦ hψ (by rw [← neg_neg ψ, h, Real.Angle.neg_coe_pi])
  rw [sub_eq_add_neg, Real.Angle.toReal_add_of_sign_eq_neg_sign (.inr hψ')
    (by rw [Real.Angle.sign_neg, neg_neg, hs]), Real.Angle.toReal_neg_eq_neg_toReal_iff.2 hψ,
    ← sub_eq_add_neg]

/-- For two angles of the same nonzero sign, their difference has positive sign exactly when their
representatives are in increasing order. -/
theorem Real.Angle.sign_sub_pos_iff_toReal_lt_of_sign_eq {θ ψ : Real.Angle}
    (hs : θ.sign = ψ.sign) (h0 : θ.sign ≠ 0) : (ψ - θ).sign = 1 ↔ θ.toReal < ψ.toReal := by
  rw [← Real.Angle.sign_toReal (Real.Angle.sub_ne_pi_of_sign_eq_of_sign_ne_zero ψ θ hs.symm h0),
    Real.Angle.toReal_sub_of_sign_eq (Real.Angle.sign_ne_zero_iff.1 h0).2 hs.symm, sign_eq_one_iff,
    sub_pos]

/-- If two angles add up to a third one plus `π`, the sum of their representatives is the
representative of the third angle plus `π` exactly when this sum is positive. -/
theorem Real.Angle.toReal_add_toReal_eq_add_pi_iff {θ₁ θ₂ θ : Real.Angle}
    (h : θ₁ + θ₂ = θ + Real.pi) :
    θ₁.toReal + θ₂.toReal = θ.toReal + Real.pi ↔ 0 < θ₁.toReal + θ₂.toReal := by
  refine ⟨fun he ↦ by linarith [θ.neg_pi_lt_toReal], fun hpos ↦ ?_⟩
  have hθ : θ = ((θ₁.toReal + θ₂.toReal - Real.pi : ℝ) : Real.Angle) := by simp [h]
  rw [hθ, Real.Angle.toReal_coe_eq_self_iff.2
    ⟨by linarith, by linarith [θ₁.toReal_le_pi, θ₂.toReal_le_pi]⟩]
  ring

/-- If two angles add up to a third one plus `π`, the sum of their representatives is the
representative of the third angle minus `π` exactly when this sum is nonpositive. -/
theorem Real.Angle.toReal_add_toReal_eq_sub_pi_iff {θ₁ θ₂ θ : Real.Angle}
    (h : θ₁ + θ₂ = θ + Real.pi) :
    θ₁.toReal + θ₂.toReal = θ.toReal - Real.pi ↔ θ₁.toReal + θ₂.toReal ≤ 0 := by
  refine ⟨fun he ↦ by linarith [θ.toReal_le_pi], fun hnonpos ↦ ?_⟩
  have hθ : θ = ((θ₁.toReal + θ₂.toReal + Real.pi : ℝ) : Real.Angle) := by
    rw [← add_zero θ, ← Real.Angle.coe_pi_add_coe_pi, ← add_assoc, ← h]
    simp
  rw [hθ, Real.Angle.toReal_coe_eq_self_iff.2
    ⟨by linarith [θ₁.neg_pi_lt_toReal, θ₂.neg_pi_lt_toReal], by linarith⟩]
  ring

/-- If two angles add up to a third one plus `π`, the sum of their representatives is the
representative of the third angle plus `π` or minus `π`. -/
theorem Real.Angle.toReal_add_toReal_eq_add_pi_or_eq_sub_pi {θ₁ θ₂ θ : Real.Angle}
    (h : θ₁ + θ₂ = θ + Real.pi) :
    θ₁.toReal + θ₂.toReal = θ.toReal + Real.pi ∨ θ₁.toReal + θ₂.toReal = θ.toReal - Real.pi :=
  (lt_or_ge 0 (θ₁.toReal + θ₂.toReal)).imp (Real.Angle.toReal_add_toReal_eq_add_pi_iff h).2
    (Real.Angle.toReal_add_toReal_eq_sub_pi_iff h).2

/-- If `cos` and `sin` agree at `2πa` and `2πb`, then `a` and `b` differ by an integer: this is
Mathlib's `Real.Angle.cos_sin_inj` read through `Real.Angle.angle_eq_iff_two_pi_dvd_sub`. -/
theorem Real.exists_int_eq_add_of_cos_sin_eq {a b : ℝ}
    (hc : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b))
    (hs : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b)) : ∃ n : ℤ, a = b + n := by
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)
  exact ⟨n, mul_left_cancel₀ Real.two_pi_pos.ne' (by linarith)⟩

/-- The cosine of `2 * n * (π / m)` is one, for an integer `m ≠ 0`, exactly when `m` divides `n`.
So a rotation through the angle `2 π / m` has `n`-th power the identity exactly when `m ∣ n`. -/
theorem Real.cos_two_mul_pi_div_eq_one_iff_dvd {m n : ℤ} (hm : m ≠ 0) :
    Real.cos (2 * (n : ℝ) * (Real.pi / m)) = 1 ↔ m ∣ n := by
  have hm0 : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
  -- `2 * n * (π / m)` is `n / m` turns of `2π`
  have hturn : 2 * (n : ℝ) * (Real.pi / m) = n / m * (2 * Real.pi) := by field_simp
  rw [hturn, Real.cos_eq_one_iff]
  refine ⟨fun ⟨j, hj⟩ ↦ ⟨j, ?_⟩, fun ⟨j, hj⟩ ↦ ⟨j, by subst hj; push_cast; field_simp⟩⟩
  have hjn : (j : ℝ) = n / m := mul_right_cancel₀ Real.two_pi_pos.ne' hj
  have hnj : (n : ℝ) = m * j := by rw [hjn]; field_simp
  exact_mod_cast hnj

/-- If the oriented angles `θ` and `α` add up to `β ∈ (0, 2π)`, where `|θ| = α`,
then `β = 2α`: the other possibility `θ = -α` would force `β` to be a multiple of `2π`. -/
theorem Real.Angle.eq_two_mul_of_abs_toReal_eq {θ : Real.Angle} {α β : ℝ}
    (hθ : |θ.toReal| = α) (hβ : θ + α = β) (hβ₀ : 0 < β) (hβ2π : β < 2 * Real.pi) :
    β = 2 * α := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hα₀ : 0 ≤ α := hθ ▸ abs_nonneg _
  have hαπ : α ≤ Real.pi := hθ ▸ θ.abs_toReal_le_pi
  have hsum : ((θ.toReal + α : ℝ) : Real.Angle) = β := by
    rw [Real.Angle.coe_add, θ.coe_toReal, hβ]
  -- `β ∈ (0, 2π)` is not a multiple of `2π`, so `θ.toReal + α` is not zero
  have h0 : θ.toReal + α ≠ 0 := fun h ↦ hβ₀.ne <|
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 2 * Real.pi) (a := 0) (x := 0) (y := β)
      ⟨le_rfl, by linarith⟩ ⟨hβ₀.le, by linarith⟩).1 (by rwa [h] at hsum)
  -- hence `θ.toReal = α`, and `2α ∈ (0, 2π]` and `β ∈ (0, 2π)` represent the same angle
  have hθα : θ.toReal = α := ((abs_eq hα₀).1 hθ).resolve_right fun h ↦ h0 (by linarith)
  rw [hθα] at hsum h0
  linarith [(AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := 2 * Real.pi) (a := 0) (x := α + α)
    (y := β) ⟨lt_of_le_of_ne (by linarith) h0.symm, by linarith⟩ ⟨hβ₀, by linarith⟩).1 hsum]
