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

* `Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq`: two reals have the same `[0, 2π)` representative
  exactly when they are equal in `Real.Angle`.
* `Real.Angle.toReal_sub_of_sign_eq`: for angles of the same sign, the subtracted one not `π`,
  `toReal` of the difference is the difference of the `toReal`s.
* `Real.Angle.sign_sub_pos_iff_toReal_lt`: for angles of positive sign, the difference has
  positive sign exactly when the representatives increase.
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

/-- For two angles of positive sign, their difference has positive sign exactly when their
representatives are in increasing order. -/
theorem _root_.Real.Angle.sign_sub_pos_iff_toReal_lt {θ ψ : Real.Angle} (hθ : θ.sign = 1)
    (hψ : ψ.sign = 1) : (ψ - θ).sign = 1 ↔ θ.toReal < ψ.toReal := by
  obtain ⟨h₁, h₂⟩ := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 hθ
  obtain ⟨h₃, h₄⟩ := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 hψ
  rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos,
    Real.Angle.toReal_sub_of_sign_eq (Real.Angle.sign_ne_zero_iff.1 (by rw [hθ]; decide)).2
      (hψ.trans hθ.symm),
    Set.mem_Ioo, sub_pos, and_iff_left_iff_imp]
  exact fun _ ↦ by linarith

end TauCeti
