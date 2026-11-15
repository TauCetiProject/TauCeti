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

For a natural number `m ≠ 0`, if the cosine of `2 n π / m` is one then `m ∣ n`; this bounds the
order of the rank-two rotations in the geometric representation of a Coxeter group.

## Main results

* `Real.exists_int_eq_add_of_cos_sin_eq`: reals whose `cos` and `sin` at `2π` times them agree
  differ by an integer.
* `TauCeti.dvd_of_cos_two_mul_pi_div_eq_one`: if `cos (2 n (π / m)) = 1` for a nonzero natural `m`,
  then `m ∣ n`.
* `TauCeti.toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos` and
  `TauCeti.eq_of_cos_sign_change_fin`: a sampled sinusoid `cos (α₀ + 2π k / h)` (`2 ≤ h`) changes
  sign from positive to nonpositive at most once on `Fin h`.
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

/-- If two angles add up to a third one plus `π`, the sum of their representatives is the
representative of the third angle plus `π` exactly when this sum is positive. -/
theorem _root_.Real.Angle.toReal_add_toReal_eq_add_pi_iff {θ₁ θ₂ θ : Real.Angle}
    (h : θ₁ + θ₂ = θ + Real.pi) :
    θ₁.toReal + θ₂.toReal = θ.toReal + Real.pi ↔ 0 < θ₁.toReal + θ₂.toReal := by
  refine ⟨fun he ↦ by linarith [θ.neg_pi_lt_toReal], fun hpos ↦ ?_⟩
  have hθ : θ = ((θ₁.toReal + θ₂.toReal - Real.pi : ℝ) : Real.Angle) := by simp [h]
  rw [hθ, Real.Angle.toReal_coe_eq_self_iff.2
    ⟨by linarith, by linarith [θ₁.toReal_le_pi, θ₂.toReal_le_pi]⟩]
  ring

/-- If two angles add up to a third one plus `π`, the sum of their representatives is the
representative of the third angle minus `π` exactly when this sum is nonpositive. -/
theorem _root_.Real.Angle.toReal_add_toReal_eq_sub_pi_iff {θ₁ θ₂ θ : Real.Angle}
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
theorem _root_.Real.Angle.toReal_add_toReal_eq_add_pi_or_eq_sub_pi {θ₁ θ₂ θ : Real.Angle}
    (h : θ₁ + θ₂ = θ + Real.pi) :
    θ₁.toReal + θ₂.toReal = θ.toReal + Real.pi ∨ θ₁.toReal + θ₂.toReal = θ.toReal - Real.pi :=
  (lt_or_ge 0 (θ₁.toReal + θ₂.toReal)).imp (Real.Angle.toReal_add_toReal_eq_add_pi_iff h).2
    (Real.Angle.toReal_add_toReal_eq_sub_pi_iff h).2

/-- If `cos` and `sin` agree at `2πa` and `2πb`, then `a` and `b` differ by an integer: this is
Mathlib's `Real.Angle.cos_sin_inj` read through `Real.Angle.angle_eq_iff_two_pi_dvd_sub`. -/
theorem _root_.Real.exists_int_eq_add_of_cos_sin_eq {a b : ℝ}
    (hc : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b))
    (hs : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b)) : ∃ n : ℤ, a = b + n := by
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi (by linarith)

/-- If the cosine of `2 * n * (π / m)` is one, with `m` a nonzero natural number, then `m` divides
`n`, so a rotation through the angle `2 π / m` whose `n`-th power is the identity forces `m ∣ n`. -/
theorem dvd_of_cos_two_mul_pi_div_eq_one {m n : ℕ} (hm : m ≠ 0)
    (h : Real.cos (2 * (n : ℝ) * (Real.pi / m)) = 1) : m ∣ n := by
  obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 h
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hmul : (j : ℝ) * (2 * Real.pi) * (m : ℝ) = 2 * (n : ℝ) * Real.pi := by
    rw [hj]
    field_simp
  have hcancel : (j : ℝ) * (m : ℝ) = (n : ℝ) :=
    mul_right_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0) (by linear_combination hmul)
  have hint : (m : ℤ) ∣ (n : ℤ) := ⟨j, by
    have : (n : ℤ) = j * (m : ℤ) := by exact_mod_cast hcancel.symm
    linarith⟩
  exact Int.ofNat_dvd.1 (by simpa using hint)

/-- If `0 < δ ≤ π`, `0 < cos α`, and `cos (α + δ) ≤ 0`, then the `[-π, π)` representative
`toIcoMod Real.two_pi_pos (-π) α` lies in `[π / 2 - δ, π / 2)`. -/
theorem toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos {δ α : ℝ}
    (hδ0 : 0 < δ) (hδpi : δ ≤ Real.pi) (hcos : 0 < Real.cos α) (hcos_add : Real.cos (α + δ) ≤ 0) :
    toIcoMod Real.two_pi_pos (-Real.pi) α ∈ Set.Ico (Real.pi / 2 - δ) (Real.pi / 2) := by
  set β := toIcoMod Real.two_pi_pos (-Real.pi) α
  set m := toIcoDiv Real.two_pi_pos (-Real.pi) α
  have hmem := toIcoMod_mem_Ico Real.two_pi_pos (-Real.pi) α
  have hshift : β = α - m * (2 * Real.pi) :=
    (self_sub_toIcoDiv_mul Real.two_pi_pos (-Real.pi) α).symm
  have hcosβ : 0 < Real.cos β := by rwa [hshift, Real.cos_sub_int_mul_two_pi]
  have hβ_gt : -(Real.pi / 2) < β := by
    by_contra! hle
    have hnp :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (x := -β) (by linarith) (by linarith [hmem.1])
    rw [Real.cos_neg] at hnp; linarith
  have hβ_lt : β < Real.pi / 2 := by
    by_contra! hge; linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hge (by linarith [hmem.2])]
  refine ⟨?_, hβ_lt⟩; by_contra! hlt
  have hca : Real.cos (β + δ) = Real.cos (α + δ) := by
    rw [hshift, show α - m * (2 * Real.pi) + δ = α + δ - m * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi]
  linarith [Real.cos_pos_of_mem_Ioo (x := β + δ) ⟨by linarith, by linarith⟩]

/-- A sampled sinusoid `cos (α₀ + 2π k / h)` (`2 ≤ h`) changes sign from strictly positive to
nonpositive at most once as `k` ranges over `Fin h`. -/
theorem eq_of_cos_sign_change_fin {h : ℕ} (hh : 2 ≤ h) {α₀ : ℝ} {k₁ k₂ : Fin h}
    (hpos₁ : 0 < Real.cos (α₀ + 2 * Real.pi * (k₁ : ℝ) / h))
    (hneg₁ : Real.cos (α₀ + 2 * Real.pi * ((k₁ : ℝ) + 1) / h) ≤ 0)
    (hpos₂ : 0 < Real.cos (α₀ + 2 * Real.pi * (k₂ : ℝ) / h))
    (hneg₂ : Real.cos (α₀ + 2 * Real.pi * ((k₂ : ℝ) + 1) / h) ≤ 0) :
    k₁ = k₂ := by
  have hh_pos : (0 : ℝ) < h := by positivity
  set δ : ℝ := 2 * Real.pi / h
  have hδ0 : 0 < δ := div_pos Real.two_pi_pos hh_pos
  have hδpi : δ ≤ Real.pi := (div_le_iff₀' hh_pos).mpr
    (mul_le_mul_of_nonneg_right (Nat.ofNat_le_cast.mpr hh) Real.pi_pos.le)
  set α₁ := α₀ + 2 * Real.pi * (k₁ : ℝ) / h; set α₂ := α₀ + 2 * Real.pi * (k₂ : ℝ) / h
  obtain ⟨hlo₁, hhi₁⟩ := toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos hδ0 hδpi hpos₁
    (by rwa [show α₁ + δ = α₀ + 2 * Real.pi * ((k₁ : ℝ) + 1) / h by simp only [α₁, δ]; ring])
  obtain ⟨hlo₂, hhi₂⟩ := toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos hδ0 hδpi hpos₂
    (by rwa [show α₂ + δ = α₀ + 2 * Real.pi * ((k₂ : ℝ) + 1) / h by simp only [α₂, δ]; ring])
  set m₁ := toIcoDiv Real.two_pi_pos (-Real.pi) α₁; set m₂ := toIcoDiv Real.two_pi_pos (-Real.pi) α₂
  rw [← self_sub_toIcoDiv_mul Real.two_pi_pos (-Real.pi)] at hlo₁ hhi₁ hlo₂ hhi₂
  set n : ℤ := (k₂ : ℤ) - (k₁ : ℤ) - (m₂ - m₁) * (h : ℤ)
  have hdiff : (n : ℝ) * δ = (α₂ - m₂ * (2 * Real.pi)) - (α₁ - m₁ * (2 * Real.pi)) := by
    simp only [n, α₁, α₂, δ]; push_cast; field_simp; ring
  have hn_gt : (-1 : ℤ) < n := (Int.cast_lt (R := ℝ)).mp
    (lt_of_mul_lt_mul_right (a := δ) (by push_cast; linarith) hδ0.le)
  have hn_lt : n < (1 : ℤ) := (Int.cast_lt (R := ℝ)).mp
    (lt_of_mul_lt_mul_right (a := δ) (by push_cast; linarith) hδ0.le)
  have hdvd : (h : ℤ) ∣ ((k₂ : ℤ) - (k₁ : ℤ)) := ⟨m₂ - m₁, by rw [mul_comm]; omega⟩
  have := Nat.eq_zero_of_dvd_of_lt (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd) (by omega)
  exact Fin.ext (by omega)

/-- If the oriented angles `θ` and `α` add up to `β ∈ (0, π)`, where `|θ| = α`,
then `β = 2α`: the other possibility `θ = -α` would force `β = 0`. -/
theorem _root_.Real.Angle.eq_two_mul_of_abs_toReal_eq {θ : Real.Angle} {α β : ℝ}
    (hθ : |θ.toReal| = α) (hβ : θ + α = β) (hβ₀ : 0 < β) (hβπ : β < Real.pi) :
    β = 2 * α := by
  have hα₀ : 0 ≤ α := hθ ▸ abs_nonneg _
  have hαπ : α ≤ Real.pi := hθ ▸ θ.abs_toReal_le_pi
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
