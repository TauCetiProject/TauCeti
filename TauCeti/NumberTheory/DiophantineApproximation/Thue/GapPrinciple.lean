/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.Height.House
import TauCeti.NumberTheory.DiophantineApproximation.Thue.AnalyticBound
import TauCeti.NumberTheory.DiophantineApproximation.Thue.ArithmeticBound
import TauCeti.NumberTheory.DiophantineApproximation.Thue.Auxiliary

/-!
# Thue's gap principle and Thue's approximation theorem

Let `α` be an algebraic number of degree `d ≥ 2` and let `κ > d / 2 + 1`. Thue's gap principle
says that a good rational approximation `ξ₁` of `α`, that is `|ξ₁ - α| ≤ H(ξ₁) ^ (-κ)`, of large
height controls the heights of all other good approximations: there are constants `C` and `λ`,
depending only on `α` and `κ`, such that `H(ξ₁) ≥ C` implies `H(ξ) ≤ H(ξ₁) ^ λ` for every `ξ ∈ ℚ`
with `|ξ - α| ≤ H(ξ) ^ (-κ)`. Here `H` is the multiplicative height `Height.mulHeight₁` on `ℚ`.
The constants are Evertse's explicit ones: for `ε = (κ - 1 - d / 2) / ((2 κ + 2) d)`, or any
smaller positive `ε`, one may take `λ = 1 + 2 (1 + κ d) / (ε d)` and `C = (2 C₂) ^ (2 / (ε d))`,
where `C₂` bounds the values of Thue's auxiliary polynomials near `α`.

By Northcott's theorem there are only finitely many rationals of bounded height, so the gap
principle gives **Thue's approximation theorem**: `|ξ - α| ≤ H(ξ) ^ (-κ)` has only finitely many
rational solutions `ξ`.

## Main results

* `TauCeti.thueC₂`: Thue's constant `C₂`, bounding the auxiliary polynomials near `α`.
* `TauCeti.thueC₂_def`: the explicit formula for `C₂`.
* `TauCeti.thue_gap_principle`: Thue's gap principle with explicit constants, for complex
  algebraic `α`.
* `TauCeti.thue_approximation`: Thue's approximation theorem, for complex algebraic `α`.
* `TauCeti.thue_approximation_real`: Thue's approximation theorem for real algebraic `α`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Theorems 6.9
  and 6.14.
-/

public section

open Polynomial Height Real

namespace TauCeti

/-- Thue's constant `C₂ = 2 ^ ((1 / 2 + ε) d) (1 + |α|) ^ (1 + (1 / 2 + ε) d) C₁`, where
`C₁ = (48 b max(1, house α)) ^ (d (1 + 1 / ε))` and `d` is the degree of `α`. Its `r`-th power
bounds the values near `α` of Thue's auxiliary polynomials of parameter `r` (Evertse, ch. 6). -/
noncomputable def thueC₂ (α : ℂ) (b : ℕ) (ε : ℝ) : ℝ :=
  2 ^ ((1 / 2 + ε) * (minpoly ℚ α).natDegree) *
    (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * (minpoly ℚ α).natDegree) *
    (48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε))

/-- The defining formula of Thue's constant `C₂`. -/
theorem thueC₂_def (α : ℂ) (b : ℕ) (ε : ℝ) :
    thueC₂ α b ε = 2 ^ ((1 / 2 + ε) * (minpoly ℚ α).natDegree) *
      (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * (minpoly ℚ α).natDegree) *
      (48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε)) :=
  (rfl)

/-- Thue's constant `C₂` is at least `1`. -/
theorem one_le_thueC₂ (α : ℂ) {b : ℕ} (hb : 0 < b) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ thueC₂ α b ε := by
  have hb1 : (1 : ℝ) ≤ 48 * b * max 1 (house α) := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [le_max_left (1 : ℝ) (house α)]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_rpow one_le_two (by positivity))
    (one_le_rpow (by linarith [norm_nonneg α]) (by positivity)))
    (one_le_rpow hb1 (by positivity))

/-- **Thue's key inequality.** For Thue's auxiliary polynomials of parameter `r` and rational
points `ξ₁, ξ₂` with `‖ξ₁ - α‖ ≤ 1`, some order `k ≤ d (2 ε r + 1)` satisfies
`(H(ξ₁) ^ (N - k) H(ξ₂))⁻¹ ≤ C₂ ^ r (‖ξ₁ - α‖ ^ (r - k) + ‖ξ₂ - α‖)`, where
`N = ⌊(1 / 2 + ε) d r⌋`. -/
private theorem thue_key_inequality {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {b : ℕ}
    (hb : 0 < b) (hbα : IsIntegral ℤ ((b : ℂ) * α)) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    {r : ℕ} (hr : 0 < r) {ξ₁ : ℚ} (h₁ : ‖(ξ₁ : ℂ) - α‖ ≤ 1) (ξ₂ : ℚ) :
    ∃ k : ℕ, k ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ ∧
      (k : ℝ) ≤ (minpoly ℚ α).natDegree * (2 * ε * r + 1) ∧
      (mulHeight₁ ξ₁ ^ (⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ - k) *
          mulHeight₁ ξ₂)⁻¹ ≤
        thueC₂ α b ε ^ r * (‖(ξ₁ : ℂ) - α‖ ^ (r - k) + ‖(ξ₂ : ℂ) - α‖) := by
  obtain ⟨P, Q, hPQ, hP, hQ, hdvd, hPC, hQC⟩ :=
    exists_thue_auxiliary_polynomials hb hbα hε₀ hε hr
  obtain ⟨k, hkN, hk, hlow⟩ :=
    exists_thue_hasseDeriv_lower_bound hd hε₀.le hε hr hPQ hP hQ hdvd ξ₁ ξ₂
  have hlen (R : ℤ[X]) : (R.map (Int.castRingHom ℂ)).l1Norm = R.l1Norm :=
    R.l1Norm_map _ fun n ↦ by simp [Int.norm_eq_abs]
  have hdeg {R : ℤ[X]} (hR : R.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊) :
      ((R.map (Int.castRingHom ℂ)).natDegree : ℝ) ≤ (1 / 2 + ε) * (minpoly ℚ α).natDegree * r :=
    (Nat.cast_le.2 ((natDegree_map_le).trans hR)).trans (Nat.floor_le (by positivity))
  -- The rational value of an integer polynomial at `ξ₁`, cast to `ℂ`, is its complex value.
  have hcast (R : ℤ[X]) : ((aeval ξ₁ R : ℚ) : ℂ) = (R.map (Int.castRingHom ℂ)).eval (ξ₁ : ℂ) := by
    have := aeval_algebraMap_apply ℂ ξ₁ R
    simp only [eq_ratCast] at this
    rw [← this, aeval_def, eval_map, algebraMap_int_eq]
  -- `thueC₂ α b ε` is the constant `2 ^ δ (1 + ‖α‖) ^ (1 + δ) C₁` of
  -- `norm_eval_hasseDeriv_sub_mul_le` with `δ = (1 / 2 + ε) d`.
  rw [thueC₂_def]
  refine ⟨k, hkN, hk, hlow.trans_eq ?_ |>.trans <| norm_eval_hasseDeriv_sub_mul_le (ξ₂ : ℂ) k hr
    (hdeg hP) (hdeg hQ) ((hlen P).trans_le hPC) ((hlen Q).trans_le hQC) hdvd h₁⟩
  rw [← Complex.norm_ratCast]
  push_cast
  rw [hcast, hcast, hasseDeriv_map, hasseDeriv_map]

/-- **Thue's key inequality in logarithmic form.** Let `κ ≥ 0` and let `ξ₁, ξ₂` be rationals
with `|ξᵢ - α| ≤ H(ξᵢ) ^ (-κ)`. For Thue's auxiliary polynomials of parameter `r`, some order
`k ≤ d (2 ε r + 1)` makes one of the two error terms dominate:
`min (κ (r - k) log H(ξ₁)) (κ log H(ξ₂)) ≤ (N - k) log H(ξ₁) + log H(ξ₂) + r log (2 C₂)`, where
`N = ⌊(1 / 2 + ε) d r⌋`. -/
private theorem thue_key_log_inequality {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {b : ℕ}
    (hb : 0 < b) (hbα : IsIntegral ℤ ((b : ℂ) * α)) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    {r : ℕ} (hr : 0 < r) {κ : ℝ} (hκ : 0 ≤ κ) {ξ₁ ξ₂ : ℚ}
    (h₁ : ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ)) (h₂ : ‖(ξ₂ : ℂ) - α‖ ≤ mulHeight₁ ξ₂ ^ (-κ)) :
    ∃ k : ℕ, k ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ ∧
      (k : ℝ) ≤ (minpoly ℚ α).natDegree * (2 * ε * r + 1) ∧
      min (κ * ((r - k : ℕ) * log (mulHeight₁ ξ₁))) (κ * log (mulHeight₁ ξ₂)) ≤
        ((⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ - k : ℕ) : ℝ) * log (mulHeight₁ ξ₁) +
          log (mulHeight₁ ξ₂) +
          r * log (2 * thueC₂ α b ε) := by
  have h₁' : ‖(ξ₁ : ℂ) - α‖ ≤ 1 :=
    h₁.trans (rpow_le_one_of_one_le_of_nonpos (one_le_mulHeight₁ ξ₁) (by linarith))
  obtain ⟨k, hkN, hk, hkey⟩ := thue_key_inequality hd hb hbα hε₀ hε hr h₁' ξ₂
  refine ⟨k, hkN, hk, ?_⟩
  set C₂ := thueC₂ α b ε
  have hC₂ : 0 < C₂ := zero_lt_one.trans_le (one_le_thueC₂ α hb hε₀)
  set N := ⌊(1 / 2 + ε) * ((minpoly ℚ α).natDegree : ℝ) * r⌋₊
  set H₁ := mulHeight₁ ξ₁
  set H₂ := mulHeight₁ ξ₂
  have hH₁ : 0 < H₁ := mulHeight₁_pos ξ₁
  have hH₂ : 0 < H₂ := mulHeight₁_pos ξ₂
  -- Bound both error terms of the key inequality by their maximum.
  set X := (H₁ ^ (-κ)) ^ (r - k)
  set Y := H₂ ^ (-κ)
  have hM : 0 < max X Y := lt_max_of_lt_right (by positivity)
  have hle : (H₁ ^ (N - k) * H₂)⁻¹ ≤ (2 * C₂) ^ r * max X Y := by
    have h2 : (2 : ℝ) ≤ 2 ^ r := by
      simpa using pow_le_pow_right₀ one_le_two (Nat.one_le_iff_ne_zero.2 hr.ne')
    have hX := pow_le_pow_left₀ (norm_nonneg _) h₁ (r - k)
    calc
      _ ≤ C₂ ^ r * (‖(ξ₁ : ℂ) - α‖ ^ (r - k) + ‖(ξ₂ : ℂ) - α‖) := hkey
      _ ≤ C₂ ^ r * (2 * max X Y) := by
        gcongr
        linarith [le_max_left X Y, le_max_right X Y]
      _ ≤ C₂ ^ r * (2 ^ r * max X Y) := by gcongr
      _ = (2 * C₂) ^ r * max X Y := by ring
  have hlog := log_le_log (by positivity) hle
  rw [log_inv, log_mul (by positivity) hH₂.ne', log_mul (by positivity) hM.ne', log_pow,
    log_pow] at hlog
  rcases le_total X Y with hXY | hXY
  · rw [max_eq_right hXY, log_rpow hH₂] at hlog
    exact min_le_iff.2 (Or.inr (by linarith))
  · rw [max_eq_left hXY, log_pow, log_rpow hH₁] at hlog
    exact min_le_iff.2 (Or.inl (by linarith))

/-- The two cases of the gap principle, for `t = log H(ξ₂) / log H(ξ₁)`. Let `ℓ₁ > 0`,
`G ≤ ε d ℓ₁ / 2`, `N ≤ (1 / 2 + ε) d r` and `k ≤ d (2 ε r + 1)`, and suppose that
`min (κ (r - k) ℓ₁) (κ t ℓ₁) ≤ (N - k) ℓ₁ + t ℓ₁ + r G`. Then, with
`a = (1 / 2 + ε) d + ε d / 2`, either `(κ - 1) t ≤ a r` or
`(κ - 2 ε d (κ - 1) - a) r - (κ - 1) d ≤ t`. -/
private theorem thue_gap_cases {κ ε d ℓ₁ t G : ℝ} {N k r : ℕ} (hκ : 1 < κ) (hℓ₁ : 0 < ℓ₁)
    (hG : G ≤ ε * d / 2 * ℓ₁) (hN : (N : ℝ) ≤ (1 / 2 + ε) * d * r) (hkN : k ≤ N)
    (hk : (k : ℝ) ≤ d * (2 * ε * r + 1))
    (h : min (κ * ((r - k : ℕ) * ℓ₁)) (κ * (t * ℓ₁)) ≤ (N - k : ℕ) * ℓ₁ + t * ℓ₁ + r * G) :
    (κ - 1) * t ≤ ((1 / 2 + ε) * d + ε * d / 2) * r ∨
      (κ - 2 * (ε * d) * (κ - 1) - ((1 / 2 + ε) * d + ε * d / 2)) * r - (κ - 1) * d ≤ t := by
  have hNk : ((N - k : ℕ) : ℝ) = N - k := Nat.cast_sub hkN
  have hN' : (N : ℝ) * ℓ₁ ≤ (1 / 2 + ε) * d * r * ℓ₁ := mul_le_mul_of_nonneg_right hN hℓ₁.le
  have hkℓ : 0 ≤ (k : ℝ) * ℓ₁ := by positivity
  have hrG : r * G ≤ r * (ε * d / 2 * ℓ₁) := mul_le_mul_of_nonneg_left hG (by positivity)
  rw [hNk] at h
  rcases min_le_iff.1 h with h | h
  · -- The first error term dominates, which bounds `t` from below.
    right
    have hrk : (r : ℝ) - k ≤ ((r - k : ℕ) : ℝ) := by
      rcases le_total k r with hkr | hkr
      · rw [Nat.cast_sub hkr]
      · rw [Nat.sub_eq_zero_of_le hkr, Nat.cast_zero, sub_nonpos]
        exact_mod_cast hkr
    have hkr : κ * ((r - k) * ℓ₁) ≤ κ * (((r - k : ℕ) : ℝ) * ℓ₁) := by gcongr
    have hkk : (κ - 1) * (k * ℓ₁) ≤ (κ - 1) * (d * (2 * ε * r + 1) * ℓ₁) := by gcongr
    refine le_of_mul_le_mul_right ?_ hℓ₁
    linarith
  · -- The second error term dominates, which bounds `t` from above.
    left
    refine le_of_mul_le_mul_right ?_ hℓ₁
    linarith

/-- The exponent arithmetic in the second case of the gap principle. Let `e > 0` satisfy
`(2 κ + 2) e ≤ κ - 1 - d / 2` with `κ > 1` and `d ≥ 2`, and put `a = d / 2 + 3 e / 2`. If
`(κ - 1) t ≤ a (r + 1)` and `B r - (κ - 1) d ≤ t` for some `B ≥ 1` and `t ≥ 0`, then
`t e ≤ 2 (1 + κ d)`. -/
private theorem thue_gap_exponent_le {κ d e B t r : ℝ} (hκ : 1 < κ) (hd : 2 ≤ d) (he : 0 < e)
    (hu : (2 * κ + 2) * e ≤ κ - 1 - d / 2) (hB : 1 ≤ B) (ht : 0 ≤ t)
    (hxr : (κ - 1) * t ≤ (d / 2 + 3 * e / 2) * (r + 1)) (hBr : B * r - (κ - 1) * d ≤ t) :
    t * e ≤ 2 * (1 + κ * d) := by
  set a := d / 2 + 3 * e / 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have he' : e < 1 / 2 := by nlinarith
  -- Eliminating `r` gives `t (B (κ - 1) - a) ≤ a (B + (κ - 1) d)`.
  have h₁ : t * (B * (κ - 1) - a) ≤ a * (B + (κ - 1) * d) := by
    nlinarith [mul_le_mul_of_nonneg_left hBr ha,
      mul_le_mul_of_nonneg_left hxr (by linarith : 0 ≤ B)]
  -- Since `κ - 1 - a ≥ (2 κ + 1 / 2) e` and `B ≥ 1`, dividing by `B` leaves
  -- `t e (2 κ + 1 / 2) ≤ a (1 + (κ - 1) d)`.
  have hκa : (2 * κ + 1 / 2) * e ≤ κ - 1 - a := by rw [ha_def]; linarith
  have h₂ : B * (t * e * (2 * κ + 1 / 2)) ≤ B * (a * (1 + (κ - 1) * d)) := by
    nlinarith [mul_nonneg (mul_nonneg ht (by linarith : 0 ≤ B)) (sub_nonneg.2 hκa),
      mul_nonneg (mul_nonneg ht (sub_nonneg.2 hB)) ha,
      mul_nonneg (mul_nonneg ha (mul_nonneg (by linarith : 0 ≤ κ - 1) (by linarith : 0 ≤ d)))
        (sub_nonneg.2 hB)]
  have h₃ := le_of_mul_le_mul_left h₂ (by linarith)
  -- Finally `a ≤ d ≤ 4 κ + 1` and `1 + (κ - 1) d ≤ 1 + κ d`.
  have h₄ : a * (1 + (κ - 1) * d) ≤ (2 * κ + 1 / 2) * (2 * (1 + κ * d)) := by
    have had : a ≤ 2 * (2 * κ + 1 / 2) := by
      have : 0 < (2 * κ + 2) * e := mul_pos (by linarith) he
      rw [ha_def]
      linarith
    nlinarith [mul_le_mul had (by nlinarith : 1 + (κ - 1) * d ≤ 1 + κ * d) (by nlinarith)
      (by linarith)]
  nlinarith

/-- The exponent bound behind the gap principle. Let `ε > 0` satisfy
`(2 κ + 2) ε d ≤ κ - 1 - d / 2` with `κ > 1` and `d ≥ 2`, let `ℓ₁ > 0` and `G ≤ ε d ℓ₁ / 2`, and
suppose that for every `r > 0` some `k ≤ N = ⌊(1 / 2 + ε) d r⌋` with `k ≤ d (2 ε r + 1)`
satisfies `min (κ (r - k) ℓ₁) (κ t ℓ₁) ≤ (N - k) ℓ₁ + t ℓ₁ + r G`. Then
`t ≤ 1 + 2 (1 + κ d) / (ε d)`. -/
private theorem thue_gap_exponent_le_of_forall {κ ε d ℓ₁ t G : ℝ} (hκ : 1 < κ) (hd : 2 ≤ d)
    (hε : 0 < ε) (hu : (2 * κ + 2) * (ε * d) ≤ κ - 1 - d / 2) (hℓ₁ : 0 < ℓ₁)
    (hG : G ≤ ε * d / 2 * ℓ₁)
    (hkey : ∀ r : ℕ, 0 < r → ∃ k : ℕ, k ≤ ⌊(1 / 2 + ε) * d * r⌋₊ ∧ (k : ℝ) ≤ d * (2 * ε * r + 1) ∧
      min (κ * ((r - k : ℕ) * ℓ₁)) (κ * (t * ℓ₁)) ≤
        (⌊(1 / 2 + ε) * d * r⌋₊ - k : ℕ) * ℓ₁ + t * ℓ₁ + r * G) :
    t ≤ 1 + 2 * (1 + κ * d) / (ε * d) := by
  -- If `t` is larger, choose `r` with `a r < (κ - 1) t ≤ a (r + 1)`, where
  -- `a = d / 2 + 3 ε d / 2`. The second error term then contradicts `a r < (κ - 1) t`, and the
  -- first one forces `t ε d ≤ 2 (1 + κ d)`.
  by_contra! ht
  have hu₀ : 0 < ε * d := by positivity
  have hpos : 0 < 2 * (1 + κ * d) / (ε * d) := by positivity
  have ha : (1 / 2 + ε) * d + ε * d / 2 = d / 2 + 3 * (ε * d) / 2 := by ring
  set x := (κ - 1) * t / (d / 2 + 3 * (ε * d) / 2)
  have hx : 1 < x := by
    rw [lt_div_iff₀ (by positivity), one_mul]
    nlinarith
  obtain ⟨k, hkN, hk, hmin⟩ :=
    hkey (⌈x⌉₊ - 1) (by have := Nat.lt_ceil.2 (by exact_mod_cast hx : ((1 : ℕ) : ℝ) < x); omega)
  have hr : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = ⌈x⌉₊ - 1 := by
    rw [Nat.cast_sub (Nat.one_le_ceil_iff.2 (by positivity)), Nat.cast_one]
  rcases thue_gap_cases hκ hℓ₁ hG (Nat.floor_le (by positivity)) hkN hk hmin with hcase | hcase
  · have hrx : (d / 2 + 3 * (ε * d) / 2) * ((⌈x⌉₊ - 1 : ℕ) : ℝ) < (κ - 1) * t := by
      rw [← lt_div_iff₀' (by positivity), hr, sub_lt_iff_lt_add]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  · have hxr : (κ - 1) * t ≤ (d / 2 + 3 * (ε * d) / 2) * ((⌈x⌉₊ - 1 : ℕ) + 1) := by
      rw [← div_le_iff₀' (by positivity), hr, sub_add_cancel]
      exact Nat.le_ceil x
    -- `B ≥ 1` follows from `(2 κ + 2) ε d ≤ κ - 1 - d / 2`, with `5 ε d / 2 ≥ 0` to spare.
    have hB : 1 ≤ κ - 2 * (ε * d) * (κ - 1) - (d / 2 + 3 * (ε * d) / 2) := by linarith
    have := thue_gap_exponent_le hκ hd hu₀ hu hB (by linarith) hxr (ha ▸ hcase)
    rw [← le_div_iff₀ hu₀] at this
    linarith

/-- **Thue's gap principle** (Evertse, Theorem 6.14), with explicit constants. Let `α` be a
complex algebraic number of degree `d ≥ 2`, let `κ > d / 2 + 1`, and let `b ≥ 1` be an integer
with `b α` integral. Take `0 < ε ≤ (κ - 1 - d / 2) / ((2 κ + 2) d)`, the upper end being
Evertse's choice of `ε`, and put
`C₁ = (48 b max(1, house α)) ^ (d (1 + 1 / ε))`,
`C₂ = 2 ^ ((1 / 2 + ε) d) (1 + |α|) ^ (1 + (1 / 2 + ε) d) C₁` (that is, `thueC₂ α b ε`) and
`λ = 1 + 2 (1 + κ d) / (ε d)`. If the rationals `ξ₁` and `ξ` satisfy `|ξ₁ - α| ≤ H(ξ₁) ^ (-κ)`,
`H(ξ₁) ≥ (2 C₂) ^ (2 / (ε d))` and `|ξ - α| ≤ H(ξ) ^ (-κ)`, then `H(ξ) ≤ H(ξ₁) ^ λ`.
Evertse's height threshold `max(e, (2 C₂) ^ (2 / (ε d)))` is at least the one assumed here. The
degree hypothesis already forces `α` to be algebraic. -/
theorem thue_gap_principle {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) {b : ℕ} (hb : 0 < b)
    (hbα : IsIntegral ℤ ((b : ℂ) * α)) {ε : ℝ} (hε₀ : 0 < ε)
    (hε : ε ≤ (κ - 1 - (minpoly ℚ α).natDegree / 2) / ((2 * κ + 2) * (minpoly ℚ α).natDegree))
    {ξ₁ ξ : ℚ} (h₁ : ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ))
    (hC : (2 * thueC₂ α b ε) ^ (2 / (ε * (minpoly ℚ α).natDegree)) ≤ mulHeight₁ ξ₁)
    (h : ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ)) :
    mulHeight₁ ξ ≤
      mulHeight₁ ξ₁ ^ (1 + 2 * (1 + κ * (minpoly ℚ α).natDegree) /
        (ε * (minpoly ℚ α).natDegree)) := by
  -- Write `t = log H(ξ) / log H(ξ₁)`. The logarithmic key inequality holds for every `r`, so
  -- the exponent bound gives `t ≤ λ`.
  set d : ℝ := ((minpoly ℚ α).natDegree : ℝ) with hd_def
  have hd2 : (2 : ℝ) ≤ d := by rw [hd_def]; exact_mod_cast hd
  have hκ1 : 1 < κ := by linarith
  have hu₀ : 0 < ε * d := by positivity
  have hu : (2 * κ + 2) * (ε * d) ≤ κ - 1 - d / 2 := by
    have := (le_div_iff₀ (by positivity)).1 hε
    linarith
  have hεd : ε * d < 1 / 2 := by nlinarith
  have hε' : ε < 1 / 2 := by nlinarith
  set C₂ := thueC₂ α b ε
  have h2C₂ : 1 < 2 * C₂ := by linarith [one_le_thueC₂ α hb hε₀]
  have hH₁ : 1 < mulHeight₁ ξ₁ := (one_lt_rpow h2C₂ (by positivity)).trans_le hC
  set ℓ₁ := log (mulHeight₁ ξ₁)
  have hℓ₁ : 0 < ℓ₁ := log_pos hH₁
  have hG : log (2 * C₂) ≤ ε * d / 2 * ℓ₁ := by
    have := log_le_log (by positivity) hC
    rw [log_rpow (by positivity)] at this
    calc
      log (2 * C₂) = ε * d / 2 * (2 / (ε * d) * log (2 * C₂)) := by field_simp
      _ ≤ ε * d / 2 * ℓ₁ := by gcongr
  have ht := thue_gap_exponent_le_of_forall (t := log (mulHeight₁ ξ) / ℓ₁) hκ1 hd2 hε₀ hu hℓ₁ hG
    fun r hr ↦ by
      simpa only [div_mul_cancel₀ _ hℓ₁.ne'] using
        thue_key_log_inequality hd hb hbα hε₀ hε' hr (by linarith) h₁ h
  rw [← log_le_log_iff (mulHeight₁_pos ξ) (by positivity), log_rpow (by linarith)]
  rwa [div_le_iff₀ hℓ₁] at ht

/-- **Thue's approximation theorem**, for complex `α`. Let `α` be a complex algebraic number of
degree `d ≥ 2` and let `κ > d / 2 + 1`. Then only finitely many rationals `ξ` satisfy
`|ξ - α| ≤ H(ξ) ^ (-κ)`. This is a variant of Evertse, Theorem 6.9, rather than that statement
verbatim: here `α` may be complex and every degree `d ≥ 2` is allowed. -/
theorem thue_approximation {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) :
    {ξ : ℚ | ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ)}.Finite := by
  have hα : IsIntegral ℚ α := by
    by_contra h
    rw [minpoly.eq_zero h, natDegree_zero] at hd
    omega
  have hb : 0 < Algebra.natDenominator α :=
    Nat.pos_of_ne_zero (Algebra.natDenominator_ne_zero_of_isAlgebraic_rat hα.isAlgebraic)
  have hbα : IsIntegral ℤ ((Algebra.natDenominator α : ℂ) * α) := by
    simpa [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul α
  have hd₀ : (0 : ℝ) < (minpoly ℚ α).natDegree := by exact_mod_cast (by omega : 0 < _)
  -- Evertse's choice of `ε` yields a height threshold `C` and an exponent `λ`.
  obtain ⟨C, lam, hgap⟩ : ∃ C lam : ℝ, ∀ ξ₁ ξ : ℚ, ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ) →
      C ≤ mulHeight₁ ξ₁ → ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ) →
        mulHeight₁ ξ ≤ mulHeight₁ ξ₁ ^ lam :=
    ⟨_, _, fun ξ₁ ξ h₁ hC h ↦ thue_gap_principle hd hκ hb hbα
      (div_pos (by linarith) (by nlinarith)) le_rfl h₁ hC h⟩
  by_cases h : ∃ ξ₁ : ℚ, ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ) ∧ C ≤ mulHeight₁ ξ₁
  · -- One solution of height at least `C` bounds the heights of all others.
    obtain ⟨ξ₁, h₁, hC⟩ := h
    exact (NumberField.finite_setOfPred_mulHeight₁_le ℚ (mulHeight₁ ξ₁ ^ lam)).subset
      fun ξ hξ ↦ hgap ξ₁ ξ h₁ hC hξ
  · push Not at h
    exact (NumberField.finite_setOfPred_mulHeight₁_le ℚ C).subset fun ξ hξ ↦ (h ξ hξ).le

/-- **Thue's approximation theorem** for real `α`. Let `α` be a real algebraic number of degree
`d ≥ 2` and let `κ > d / 2 + 1`. Then only finitely many rationals `ξ` satisfy
`|ξ - α| ≤ H(ξ) ^ (-κ)`. This is a variant of Evertse, Theorem 6.9, rather than that statement
verbatim: every degree `d ≥ 2` is allowed. -/
theorem thue_approximation_real {α : ℝ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) :
    {ξ : ℚ | |(ξ : ℝ) - α| ≤ mulHeight₁ ξ ^ (-κ)}.Finite := by
  have hmin : minpoly ℚ (α : ℂ) = minpoly ℚ α :=
    minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective α
  convert thue_approximation (α := α) (hmin ▸ hd) (hmin ▸ hκ) using 3 with ξ
  rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

end TauCeti
