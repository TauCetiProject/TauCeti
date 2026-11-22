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
* `TauCeti.coprime_of_mul_eq_mul_pi` and `TauCeti.eq_pi_div_of_cos_two_mul_eq_one`: a positive
  angle `θ` whose `2h`-th multiple is a multiple of `2π` minimally, with no `2nθ + qπ` in `(0, θ)`,
  equals `π / h`.
* `TauCeti.toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos` and
  `TauCeti.eq_of_cos_pos_of_cos_add_one_nonpos`: a sampled sinusoid `cos (α₀ + 2π k / h)` passes
  from strictly positive to nonpositive at most once on `Fin h`.
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

namespace TauCeti

/-- If `h > 0` satisfies `h * θ = m * π` while `cos (2 h' θ) ≠ 1` for all `0 < h' < h`, then
`|m|` and `h` are coprime. -/
theorem coprime_of_mul_eq_mul_pi {h : ℕ} (hh : 0 < h) {θ : ℝ} {m : ℤ}
    (hmθ : (h : ℝ) * θ = (m : ℝ) * Real.pi)
    (hmin : ∀ h' : ℕ, 0 < h' → h' < h → Real.cos (2 * (h' : ℝ) * θ) ≠ 1) :
    m.natAbs.Coprime h := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne1
  set d := m.natAbs.gcd h
  have hd_h : d ∣ h := Nat.gcd_dvd_right _ _
  have hd_m : (d : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.gcd_dvd_left m.natAbs h)
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ hh
  have hcast_h : (d : ℝ) * ((h / d : ℕ) : ℝ) = h := by exact_mod_cast Nat.mul_div_cancel' hd_h
  have hcast_m : (d : ℝ) * ((m / (d : ℤ) : ℤ) : ℝ) = m := by
    exact_mod_cast Int.mul_ediv_cancel' hd_m
  have hcos_div : Real.cos (2 * ((h / d : ℕ) : ℝ) * θ) = 1 :=
    (Real.cos_eq_one_iff _).mpr ⟨m / (d : ℤ), mul_left_cancel₀ (by positivity : (d : ℝ) ≠ 0)
      (by linear_combination -2 * hmθ - 2 * θ * hcast_h + 2 * Real.pi * hcast_m)⟩
  exact hmin (h / d) (Nat.div_pos (Nat.le_of_dvd hh hd_h) hd0)
    (Nat.div_lt_self hh (Nat.lt_of_le_of_ne hd0 (Ne.symm hne1))) hcos_div

/-- Given `a : ℤ` and `b : ℕ` with `0 < b`, Bézout's identity yields a nonnegative coefficient
`n : ℕ` for `a` (reducing `Int.gcdA a b` modulo `b`) and an integer coefficient `q : ℤ` for `b`
with `a * n + b * q = a.gcd b`. -/
private theorem exists_nat_mul_add_int_mul_eq_gcd (a : ℤ) {b : ℕ} (hb : 0 < b) :
    ∃ (n : ℕ) (q : ℤ), a * n + b * q = a.gcd b := by
  have hbz : (b : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hb.ne'
  refine ⟨(Int.gcdA a b % b).toNat, Int.gcdB a b + a * (Int.gcdA a b / b), ?_⟩
  linear_combination -Int.gcd_eq_gcd_ab a (b : ℤ) +
    a * Int.mul_ediv_add_emod (Int.gcdA a b) b +
    a * Int.toNat_of_nonneg (Int.emod_nonneg _ hbz)

/-- If `θ > 0` has `h > 0` as the least positive natural with `cos (2 h θ) = 1`, and no angle
`2 n θ + q π` (`n : ℕ`, `q : ℤ`) falls inside `(0, θ)`, then `θ = π / h`. -/
theorem eq_pi_div_of_cos_two_mul_eq_one {h : ℕ} (hh : 0 < h) {θ : ℝ} (hθpos : 0 < θ)
    (hcos : Real.cos (2 * (h : ℝ) * θ) = 1)
    (hmin : ∀ h' : ℕ, 0 < h' → h' < h → Real.cos (2 * (h' : ℝ) * θ) ≠ 1)
    (hwall : ∀ (n : ℕ) (q : ℤ),
      ¬ (0 < 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi ∧ 2 * (n : ℝ) * θ + (q : ℝ) * Real.pi < θ)) :
    θ = Real.pi / (h : ℝ) := by
  -- Phase 1: write `h * θ = m * π` with `m > 0` coprime to `h`.
  have hhpos : (0 : ℝ) < h := by positivity
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (2 * (h : ℝ) * θ)).mp hcos
  have hmθ : (h : ℝ) * θ = (m : ℝ) * Real.pi := by linarith
  have hmpos : 0 < m :=
    Int.cast_pos.mp (pos_of_mul_pos_left (hmθ ▸ mul_pos hhpos hθpos) Real.pi_pos.le)
  have hcop := coprime_of_mul_eq_mul_pi hh hmθ hmin
  suffices m = 1 by rw [this, Int.cast_one, one_mul] at hmθ; rw [eq_div_iff hhpos.ne']; linarith
  -- Phase 2: assuming `m ≠ 1`, bound `g = gcd (2 * m) h` strictly below `m`.
  by_contra hm1
  set g : ℕ := (2 * m).gcd (h : ℤ)
  have hg_h : g ∣ h := by simpa [g] using Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (2 * m) h)
  have hg_2 : g ∣ 2 := (hcop.coprime_dvd_right hg_h).symm.dvd_of_dvd_mul_right <| by
    exact_mod_cast (by simpa [g, Int.natAbs_of_nonneg hmpos.le] using Int.gcd_dvd_left (2 * m) h :
      (g : ℤ) ∣ 2 * (m.natAbs : ℤ))
  have hg_lt_m : (g : ℤ) < m := by
    have := Nat.le_of_dvd (by norm_num) hg_2
    have : m = 2 → g ≠ 2 := fun hm2 hg2 ↦ Nat.not_coprime_of_dvd_of_dvd one_lt_two (dvd_refl 2)
      (hg2 ▸ hg_h) (by simpa [hm2] using hcop)
    omega
  -- Phase 3: apply Bézout to place `2 * n * θ + q * π = (g / h) * π` inside `(0, θ)`.
  obtain ⟨n, q, hbez⟩ := exists_nat_mul_add_int_mul_eq_gcd (2 * m) hh
  have hcr : 2 * (m : ℝ) * n + h * q = g := by exact_mod_cast hbez
  have hcomb : (h : ℝ) * (2 * (n : ℝ) * θ + (q : ℝ) * Real.pi) = (g : ℝ) * Real.pi := by
    linear_combination 2 * (n : ℝ) * hmθ + Real.pi * hcr
  exact hwall n q ⟨pos_of_mul_pos_right (hcomb ▸ mul_pos (by
      exact_mod_cast Int.gcd_pos_of_ne_zero_right (2 * m) (by omega)) Real.pi_pos) hhpos.le,
    lt_of_mul_lt_mul_left (by
      rw [hcomb, hmθ]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hg_lt_m) Real.pi_pos) hhpos.le⟩

/-- If `0 ≤ δ`, `0 < cos α`, and `cos (α + δ) ≤ 0`, then the `[-π, π)` representative
`toIcoMod Real.two_pi_pos (-π) α` lies in `[π / 2 - δ, π / 2)`. -/
theorem toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos {δ α : ℝ}
    (hδ0 : 0 ≤ δ) (hcos : 0 < Real.cos α) (hcos_add : Real.cos (α + δ) ≤ 0) :
    toIcoMod Real.two_pi_pos (-Real.pi) α ∈ Set.Ico (Real.pi / 2 - δ) (Real.pi / 2) := by
  set β := toIcoMod Real.two_pi_pos (-Real.pi) α; set m := toIcoDiv Real.two_pi_pos (-Real.pi) α
  have hmem := toIcoMod_mem_Ico Real.two_pi_pos (-Real.pi) α
  have hshift : β = α - m * (2 * Real.pi) := (self_sub_toIcoDiv_mul ..).symm
  have hcosβ : 0 < Real.cos β := by rwa [hshift, Real.cos_sub_int_mul_two_pi]
  have hβ_gt : -(Real.pi / 2) < β := by by_contra! hle; linarith [Real.cos_neg β ▸
    Real.cos_nonpos_of_pi_div_two_le_of_le (x := -β) (by linarith) (by linarith [hmem.1])]
  have hβ_lt : β < Real.pi / 2 := by
    by_contra! hge; linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hge (by linarith [hmem.2])]
  refine ⟨?_, hβ_lt⟩; by_contra! hlt
  have hca : Real.cos (β + δ) = Real.cos (α + δ) := by
    rw [show β + δ = α + δ - m * (2 * Real.pi) by rw [hshift]; ring, Real.cos_sub_int_mul_two_pi]
  linarith [Real.cos_pos_of_mem_Ioo (x := β + δ) ⟨by linarith, by linarith⟩]

/-- A sampled sinusoid `cos (α₀ + 2π k / h)` passes from strictly positive at `k` to nonpositive at
`k + 1` at most once as `k` ranges over `Fin h`. -/
theorem eq_of_cos_pos_of_cos_add_one_nonpos {h : ℕ} {α₀ : ℝ} {k₁ k₂ : Fin h}
    (hpos₁ : 0 < Real.cos (α₀ + 2 * Real.pi * (k₁ : ℝ) / h))
    (hneg₁ : Real.cos (α₀ + 2 * Real.pi * ((k₁ : ℝ) + 1) / h) ≤ 0)
    (hpos₂ : 0 < Real.cos (α₀ + 2 * Real.pi * (k₂ : ℝ) / h))
    (hneg₂ : Real.cos (α₀ + 2 * Real.pi * ((k₂ : ℝ) + 1) / h) ≤ 0) : k₁ = k₂ := by
  have hh_pos : (0 : ℝ) < h := Nat.cast_pos.mpr k₁.pos
  set δ : ℝ := 2 * Real.pi / h; let α : Fin h → ℝ := fun k ↦ α₀ + 2 * Real.pi * (k : ℝ) / h
  have hmem (k : Fin h) (hp : 0 < Real.cos (α k))
      (hn : Real.cos (α₀ + 2 * Real.pi * ((k : ℝ) + 1) / h) ≤ 0) :=
    toIcoMod_neg_pi_mem_Ico_of_cos_pos_of_cos_add_nonpos (div_pos Real.two_pi_pos hh_pos).le hp
      ((by simp only [α, δ]; ring : α k + δ = α₀ + 2 * Real.pi * ((k : ℝ) + 1) / h) ▸ hn)
  obtain ⟨hlo₁, hhi₁⟩ := hmem k₁ hpos₁ hneg₁; obtain ⟨hlo₂, hhi₂⟩ := hmem k₂ hpos₂ hneg₂
  set m₁ := toIcoDiv Real.two_pi_pos (-Real.pi) (α k₁)
  set m₂ := toIcoDiv Real.two_pi_pos (-Real.pi) (α k₂)
  rw [← self_sub_toIcoDiv_mul Real.two_pi_pos (-Real.pi)] at hlo₁ hhi₁ hlo₂ hhi₂
  set n : ℤ := (k₂ : ℤ) - (k₁ : ℤ) - (m₂ - m₁) * (h : ℤ)
  have hdiff : (n : ℝ) * δ = (α k₂ - m₂ * (2 * Real.pi)) - (α k₁ - m₁ * (2 * Real.pi)) := by
    simp only [n, α, δ]; push_cast; field_simp; ring
  have h0 : (-1 : ℤ) < n ∧ n < 1 := by
    simp only [← Int.cast_lt (R := ℝ)]; push_cast; exact ⟨by nlinarith, by nlinarith⟩
  have hdvd : h ∣ ((k₂ : ℤ) - k₁).natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr (⟨m₂ - m₁, by rw [mul_comm]; omega⟩ : (h : ℤ) ∣ k₂ - k₁)
  have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega); exact Fin.ext (by omega)

end TauCeti

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
