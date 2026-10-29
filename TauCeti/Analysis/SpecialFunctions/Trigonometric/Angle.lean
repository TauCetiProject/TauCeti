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
angles of the same sign, the difference counterpart of Mathlib's `toReal_add_of_sign_eq_neg_sign`.

## Main results

* `Real.exists_int_eq_add_of_cos_sin_eq`: reals whose `cos` and `sin` at `2π` times them agree
  differ by an integer.
* `Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq`: two reals have the same `[0, 2π)` representative
  exactly when they are equal in `Real.Angle`.
* `Real.Angle.toReal_sub_of_sign_eq`: for angles of the same sign, the subtracted one not `π`,
  `toReal` of the difference is the difference of the `toReal`s.
* `Real.Angle.sign_sub_pos_iff_toReal_lt_of_sign_eq`: for angles of the same nonzero sign, the
  difference has positive sign exactly when the representatives increase.
* `Real.Angle.eq_two_mul_of_abs_toReal_eq`: if `θ + α = β ∈ (0, π)` with `|θ| = α`, then
  `β = 2α`.
-/

public section

namespace TauCeti

/-- **Equal angles are exactly equal normalisations.** Two reals agree in `Real.Angle` — that is,
differ by an integer multiple of `2π` — exactly when their representatives in `[0, 2π)` agree,
since the normalisation discards precisely such a multiple.

The forward direction is Mathlib's `Real.Angle.coe_toIcoMod` applied on both sides; the reverse
shifts one argument by the multiple and uses `toIcoMod_add_zsmul`. -/
theorem _root_.Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq {x y : ℝ} :
    toIcoMod Real.two_pi_pos 0 x = toIcoMod Real.two_pi_pos 0 y ↔
      (x : Real.Angle) = (y : Real.Angle) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Real.Angle.coe_toIcoMod x 0, ← Real.Angle.coe_toIcoMod y 0, h]
  · obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    have hshift : x = y + k • (2 * Real.pi) := by rw [zsmul_eq_mul]; linarith
    rw [hshift, toIcoMod_add_zsmul]

/-- The representative of a difference of two angles of the same sign is the difference of the
representatives, provided the subtracted angle is not `π`. -/
theorem _root_.Real.Angle.toReal_sub_of_sign_eq {θ ψ : Real.Angle} (hψ : ψ ≠ ↑Real.pi)
    (hs : θ.sign = ψ.sign) : (θ - ψ).toReal = θ.toReal - ψ.toReal := by
  have hψ' : -ψ ≠ ↑Real.pi := fun h ↦ hψ (by rw [← neg_neg ψ, h, Real.Angle.neg_coe_pi])
  rw [sub_eq_add_neg, Real.Angle.toReal_add_of_sign_eq_neg_sign (.inr hψ')
    (by rw [Real.Angle.sign_neg, neg_neg, hs]), Real.Angle.toReal_neg_eq_neg_toReal_iff.2 hψ,
    ← sub_eq_add_neg]

/-- For two angles of the same nonzero sign, their difference has positive sign exactly when their
representatives are in increasing order. -/
theorem _root_.Real.Angle.sign_sub_pos_iff_toReal_lt_of_sign_eq {θ ψ : Real.Angle}
    (hs : θ.sign = ψ.sign) (h0 : θ.sign ≠ 0) : (ψ - θ).sign = 1 ↔ θ.toReal < ψ.toReal := by
  rw [← Real.Angle.sign_toReal (Real.Angle.sub_ne_pi_of_sign_eq_of_sign_ne_zero ψ θ hs.symm h0),
    Real.Angle.toReal_sub_of_sign_eq (Real.Angle.sign_ne_zero_iff.1 h0).2 hs.symm, sign_eq_one_iff,
    sub_pos]

/-- If `cos` and `sin` agree at `2πa` and `2πb`, then `a` and `b` differ by an integer: this is
Mathlib's `Real.Angle.cos_sin_inj` read through `Real.Angle.angle_eq_iff_two_pi_dvd_sub`. -/
theorem _root_.Real.exists_int_eq_add_of_cos_sin_eq {a b : ℝ}
    (hc : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b))
    (hs : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b)) : ∃ n : ℤ, a = b + n := by
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi (by linarith)

/-- If the oriented angles `θ` and `α` add up to `β ∈ (0, π)`, where `|θ| = α`,
then `β = 2α`: the other possibility `θ = -α` would force `β = 0`. -/
theorem _root_.Real.Angle.eq_two_mul_of_abs_toReal_eq {θ : Real.Angle} {α β : ℝ}
    (hθ : |θ.toReal| = α) (hβ : θ + α = β) (hβ₀ : 0 < β) (hβπ : β < Real.pi) :
    β = 2 * α := by
  have hα₀ : 0 ≤ α := hθ ▸ abs_nonneg _
  have hαπ : α ≤ Real.pi := hθ ▸ θ.abs_toReal_le_pi
  have hπ := Real.pi_pos
  have hβrep : (β : Real.Angle).toReal = β :=
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, hβπ.le⟩
  have hsum : ((θ.toReal + α : ℝ) : Real.Angle) = β := by
    rw [Real.Angle.coe_add, θ.coe_toReal, hβ]
  rcases (abs_eq hα₀).1 hθ with hpos | hneg
  · rw [hpos] at hsum
    by_cases hα : α = 0
    · have h := congrArg Real.Angle.toReal hsum
      rw [hα, zero_add, Real.Angle.coe_zero, Real.Angle.toReal_zero, hβrep] at h
      linarith
    · have hαpos : 0 < α := lt_of_le_of_ne hα₀ (Ne.symm hα)
      let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
      have h := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := 2 * Real.pi) (a := 0)
        (x := α + α) (y := β) ⟨by linarith, by linarith⟩ ⟨hβ₀, by linarith⟩).1 hsum
      linarith
  · have hzero : θ.toReal + α = 0 := by linarith
    have h := congrArg Real.Angle.toReal hsum
    rw [hzero, Real.Angle.coe_zero, Real.Angle.toReal_zero, hβrep] at h
    linarith

end TauCeti
