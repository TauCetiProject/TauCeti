/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Thue.AnalyticBound
public import TauCeti.NumberTheory.DiophantineApproximation.Thue.ArithmeticBound
public import TauCeti.NumberTheory.DiophantineApproximation.Thue.Auxiliary

/-!
# Thue's gap principle and Thue's approximation theorem

Let `α` be an algebraic number of degree `d ≥ 2` and let `κ > d / 2 + 1`. Thue's gap principle
says that a good rational approximation `ξ₁` of `α`, that is `|ξ₁ - α| ≤ H(ξ₁) ^ (-κ)`, of large
height controls the heights of all other good approximations: there are constants `C` and `λ`,
depending only on `α` and `κ`, such that `H(ξ₁) ≥ C` implies `H(ξ) ≤ H(ξ₁) ^ λ` for every `ξ ∈ ℚ`
with `|ξ - α| ≤ H(ξ) ^ (-κ)`. Here `H` is the multiplicative height `Height.mulHeight₁` on `ℚ`.
The constants are explicit, as in Evertse's proof: for any
`0 < ε ≤ (κ - 1 - d / 2) / ((2 κ + 2) d)` one may take `λ = 1 + 2 (1 + κ d) / (ε d)` and
`C = (2 C₂) ^ (2 / (ε d))`, where `C₂` is the explicit bound for Thue's auxiliary polynomials
near `α`.

By Northcott's theorem there are only finitely many rationals of bounded height, so the gap
principle gives **Thue's approximation theorem**: `|ξ - α| ≤ H(ξ) ^ (-κ)` has only finitely many
rational solutions `ξ`.

## Main results

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
        (2 ^ ((1 / 2 + ε) * (minpoly ℚ α).natDegree) *
            (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * (minpoly ℚ α).natDegree) *
            (48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε))) ^ r *
          (‖(ξ₁ : ℂ) - α‖ ^ (r - k) + ‖(ξ₂ : ℂ) - α‖) := by
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
  refine ⟨k, hkN, hk, hlow.trans_eq ?_ |>.trans <| norm_eval_hasseDeriv_sub_mul_le (ξ₂ : ℂ) k hr
    (hdeg hP) (hdeg hQ) ((hlen P).trans_le hPC) ((hlen Q).trans_le hQC) hdvd h₁⟩
  rw [← Complex.norm_ratCast]
  push_cast
  rw [hcast, hcast, hasseDeriv_map, hasseDeriv_map]

/-- **Thue's key inequality in logarithmic form.** For `r ≥ 1`, `κ ≥ 0` and rationals `ξ₁, ξ₂`
with `‖ξᵢ - α‖ ≤ H(ξᵢ) ^ (-κ)`, some order `k ≤ d (2 ε r + 1)` satisfies
`κ min((r - k) log H(ξ₁), log H(ξ₂)) ≤ ((1 / 2 + ε) d r - k) log H(ξ₁) + log H(ξ₂) + r log (2 C₂)`,
where `C₂` is the constant of `thue_key_inequality`. -/
private theorem thue_key_inequality_log {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {b : ℕ}
    (hb : 0 < b) (hbα : IsIntegral ℤ ((b : ℂ) * α)) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    {r : ℕ} (hr : 0 < r) {κ : ℝ} (hκ : 0 ≤ κ) {ξ₁ ξ₂ : ℚ}
    (h₁ : ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ)) (h₂ : ‖(ξ₂ : ℂ) - α‖ ≤ mulHeight₁ ξ₂ ^ (-κ)) :
    ∃ k : ℕ, (k : ℝ) ≤ (minpoly ℚ α).natDegree * (2 * ε * r + 1) ∧
      min (κ * ((r - k) * log (mulHeight₁ ξ₁))) (κ * log (mulHeight₁ ξ₂)) ≤
        ((1 / 2 + ε) * (minpoly ℚ α).natDegree * r - k) * log (mulHeight₁ ξ₁) +
          log (mulHeight₁ ξ₂) + r * log (2 * (2 ^ ((1 / 2 + ε) * (minpoly ℚ α).natDegree) *
            (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * (minpoly ℚ α).natDegree) *
            (48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε)))) := by
  set d : ℝ := ((minpoly ℚ α).natDegree : ℝ)
  set C₂ := 2 ^ ((1 / 2 + ε) * d) * (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * d) *
    (48 * b * max 1 (house α)) ^ (d * (1 + 1 / ε))
  set H₁ := mulHeight₁ ξ₁
  set H₂ := mulHeight₁ ξ₂
  have hH₁ : 0 < H₁ := mulHeight₁_pos ξ₁
  have hH₂ : 0 < H₂ := mulHeight₁_pos ξ₂
  have hℓ₁ : 0 ≤ log H₁ := log_nonneg (one_le_mulHeight₁ ξ₁)
  have h₁' : ‖(ξ₁ : ℂ) - α‖ ≤ 1 :=
    h₁.trans (rpow_le_one_of_one_le_of_nonpos (one_le_mulHeight₁ ξ₁) (by linarith))
  obtain ⟨k, hkN, hk, hkey⟩ := thue_key_inequality hd hb hbα hε₀ hε hr h₁' ξ₂
  refine ⟨k, hk, ?_⟩
  set N := ⌊(1 / 2 + ε) * d * r⌋₊
  have hN : (N : ℝ) * log H₁ ≤ (1 / 2 + ε) * d * r * log H₁ :=
    mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hℓ₁
  -- Bound both terms of the key inequality by their maximum.
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
  have hlog : -((N - k) * log H₁ + log H₂) ≤ r * log (2 * C₂) + log (max X Y) := by
    have := log_le_log (by positivity) hle
    rwa [log_inv, log_mul (by positivity) (by positivity), log_mul (by positivity) hM.ne',
      log_pow, log_pow, Nat.cast_sub hkN] at this
  rcases le_total X Y with hXY | hXY
  · rw [max_eq_right hXY, log_rpow hH₂] at hlog
    exact (min_le_right _ _).trans (by linarith)
  · rw [max_eq_left hXY, log_pow, log_rpow hH₁] at hlog
    have hrk : (r : ℝ) - k ≤ ((r - k : ℕ) : ℝ) := by
      rcases le_total k r with h | h
      · rw [Nat.cast_sub h]
      · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_nonpos]
        exact_mod_cast h
    have hkr : κ * ((r - k) * log H₁) ≤ κ * (((r - k : ℕ) : ℝ) * log H₁) := by gcongr
    exact (min_le_left _ _).trans (by linarith)

/-- The exponent comparison in the second case of the gap principle: if `(κ - 1) t ≤ a (r + 1)`
and `B r - (κ - 1) d ≤ t`, then `t (B (κ - 1) - a) ≤ a (B + (κ - 1) d)`. -/
private theorem thue_gap_exponent_le {κ a B d t r : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hxr : (κ - 1) * t ≤ a * (r + 1)) (hBr : B * r - (κ - 1) * d ≤ t) :
    t * (B * (κ - 1) - a) ≤ a * (B + (κ - 1) * d) := by
  nlinarith [mul_le_mul_of_nonneg_left hBr ha, mul_le_mul_of_nonneg_left hxr hB]

/-- If `u (2 κ + 2) ≤ κ - 1 - d / 2`, then `u < 1 / 2`, so the exponent
`λ = 1 + 2 (1 + κ d) / u` of the gap principle exceeds `1 + 4 (1 + κ d)`. -/
private theorem thue_gap_exponent_gt {κ d u : ℝ} (hd : 2 ≤ d) (hκ : d / 2 + 1 < κ) (hu : 0 < u)
    (huκ : u * (2 * κ + 2) ≤ κ - 1 - d / 2) :
    u < 1 / 2 ∧ 1 + 4 * (1 + κ * d) < 1 + 2 * (1 + κ * d) / u := by
  have hu2 : u < 1 / 2 := by nlinarith
  have hκd : 0 < 1 + κ * d := by nlinarith
  refine ⟨hu2, ?_⟩
  rw [add_lt_add_iff_left, lt_div_iff₀ hu]
  nlinarith [mul_lt_mul_of_pos_left hu2 hκd]

/-- The exponent comparison of the explicit gap principle. Put `a = d / 2 + 3 u / 2` and
`B = κ - 2 u (κ - 1) - a`, where `u (2 κ + 2) ≤ κ - 1 - d / 2`. Then no
`t > 1 + 2 (1 + κ d) / u` satisfies both `(κ - 1) t ≤ a (r + 1)` and `B r - (κ - 1) d ≤ t`. -/
private theorem thue_gap_exponent_contra {κ d u t r : ℝ} (hd : 2 ≤ d) (hκ : d / 2 + 1 < κ)
    (hu : 0 < u) (huκ : u * (2 * κ + 2) ≤ κ - 1 - d / 2) (ht : 1 + 2 * (1 + κ * d) / u < t)
    (hxr : (κ - 1) * t ≤ (d / 2 + 3 * u / 2) * (r + 1))
    (hBr : (κ - 2 * u * (κ - 1) - (d / 2 + 3 * u / 2)) * r - (κ - 1) * d ≤ t) : False := by
  set a := d / 2 + 3 * u / 2 with ha
  set B := κ - 2 * u * (κ - 1) - a
  set L := 2 * (1 + κ * d) / u with hL
  obtain ⟨hu2, -⟩ := thue_gap_exponent_gt hd hκ hu huκ
  have hκ0 : 0 ≤ κ := by linarith
  -- `D = B (κ - 1) - a` is at least `u (9 κ / 2 - 2)`, so `λ D ≥ (1 + κ d) (9 κ - 4)`.
  have hD : u * (9 * κ / 2 - 2) ≤ B * (κ - 1) - a := by
    nlinarith [mul_le_mul_of_nonneg_left huκ hκ0]
  have hDpos : 0 < B * (κ - 1) - a := lt_of_lt_of_le (by nlinarith) hD
  have hLD : (1 + κ * d) * (9 * κ - 4) ≤ L * (B * (κ - 1) - a) := by
    calc (1 + κ * d) * (9 * κ - 4) = L * u * (9 * κ / 2 - 2) := by
          rw [hL, div_mul_cancel₀ _ hu.ne']
          ring
      _ ≤ L * (B * (κ - 1) - a) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hD (div_nonneg (by nlinarith) hu.le)
  -- On the other side, `a (B + (κ - 1) d) ≤ d κ (1 + d) ≤ (1 + κ d) (9 κ - 4)`.
  have hrhs : a * (B + (κ - 1) * d) ≤ (1 + κ * d) * (9 * κ - 4) := by
    have hBd : B + (κ - 1) * d ≤ κ * (1 + d) := by nlinarith [mul_pos hu (by linarith : 0 < κ - 1)]
    calc a * (B + (κ - 1) * d) ≤ d * (κ * (1 + d)) :=
          mul_le_mul (by linarith) hBd (by nlinarith) (by linarith)
      _ ≤ (1 + κ * d) * (9 * κ - 4) := by
          nlinarith [mul_pos (mul_pos (by linarith) (by linarith) : 0 < κ * d)
            (by linarith : 0 < 9 * κ - 5 - d)]
  have hle := thue_gap_exponent_le (by positivity) (by linarith) hxr hBr
  nlinarith [mul_lt_mul_of_pos_right ht hDpos]

/-- The logarithmic core of the explicit gap principle. Let `ε d (2 κ + 2) ≤ κ - 1 - d / 2`, let
`ℓ₁ > 0` and `G ≤ ε d ℓ₁ / 2`, and let `t > 1 + 2 (1 + κ d) / (ε d)`. Then it is not the case that
every `r ≥ 1` admits some `k ≤ d (2 ε r + 1)` with
`κ min((r - k) ℓ₁, t ℓ₁) ≤ ((1 / 2 + ε) d r - k) ℓ₁ + t ℓ₁ + r G`. -/
private theorem thue_gap_log_contra {κ d ε ℓ₁ t G : ℝ} (hd : 2 ≤ d) (hκ : d / 2 + 1 < κ)
    (hε₀ : 0 < ε) (huκ : ε * d * (2 * κ + 2) ≤ κ - 1 - d / 2) (hℓ₁ : 0 < ℓ₁)
    (hG : G ≤ ε * d / 2 * ℓ₁) (ht : 1 + 2 * (1 + κ * d) / (ε * d) < t)
    (hkey : ∀ r : ℕ, 0 < r → ∃ k : ℕ, (k : ℝ) ≤ d * (2 * ε * r + 1) ∧
      min (κ * ((r - k) * ℓ₁)) (κ * (t * ℓ₁)) ≤ ((1 / 2 + ε) * d * r - k) * ℓ₁ + t * ℓ₁ + r * G) :
    False := by
  have hu : 0 < ε * d := by positivity
  obtain ⟨hu2, hlam⟩ := thue_gap_exponent_gt hd hκ hu huκ
  set a := d / 2 + 3 * (ε * d) / 2 with ha_def
  have ha : 0 < a := by positivity
  -- Choose `r = ⌈x⌉ - 1`, where `x = (κ - 1) t / a > 1`.
  set x := (κ - 1) * t / a
  have hx : 1 < x := by
    have hκd : d ≤ κ * d := by nlinarith
    rw [lt_div_iff₀ ha, one_mul]
    nlinarith
  set r := ⌈x⌉₊ - 1
  have hr : 0 < r := by
    have := Nat.lt_ceil.2 (by exact_mod_cast hx : ((1 : ℕ) : ℝ) < x)
    omega
  have hr_cast : (r : ℝ) = ⌈x⌉₊ - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hrx : a * r < (κ - 1) * t := by
    rw [← lt_div_iff₀' ha, hr_cast, sub_lt_iff_lt_add]
    exact Nat.ceil_lt_add_one (by linarith)
  have hxr : (κ - 1) * t ≤ a * (r + 1) := by
    rw [← div_le_iff₀' ha, hr_cast, sub_add_cancel]
    exact Nat.le_ceil x
  obtain ⟨k, hk, hmin⟩ := hkey r hr
  have hrG : r * G ≤ r * (ε * d / 2 * ℓ₁) := mul_le_mul_of_nonneg_left hG (by positivity)
  have hkℓ : 0 ≤ (k : ℝ) * ℓ₁ := by positivity
  rcases min_le_iff.1 hmin with hX | hY
  · -- If the first term is the minimum, then `B r - (κ - 1) d ≤ t`, contradicting `t > λ`.
    have hkk : (κ - 1) * (k * ℓ₁) ≤ (κ - 1) * (d * (2 * ε * r + 1) * ℓ₁) := by
      gcongr
      linarith
    have : ((κ - 2 * (ε * d) * (κ - 1) - a) * r - (κ - 1) * d) * ℓ₁ ≤ t * ℓ₁ := by
      rw [ha_def]
      linarith
    exact thue_gap_exponent_contra hd hκ hu huκ ht hxr (le_of_mul_le_mul_right this hℓ₁)
  · -- If the second term is the minimum, then `(κ - 1) t ≤ a r`, contradicting the choice of `r`.
    have : (κ - 1) * t * ℓ₁ ≤ a * r * ℓ₁ := by
      rw [ha_def]
      linarith
    linarith [le_of_mul_le_mul_right this hℓ₁]

/-- **Thue's gap principle** with explicit constants (Evertse, Theorem 6.14). Let `α`
be a complex algebraic number of degree `d ≥ 2`, let `κ > d / 2 + 1`, and let `b ≥ 1` be an
integer with `b α` an algebraic integer. Take `0 < ε ≤ (κ - 1 - d / 2) / ((2 κ + 2) d)` and put
`C₁ = (48 b max(1, house α)) ^ (d (1 + 1 / ε))`,
`C₂ = 2 ^ ((1 / 2 + ε) d) (1 + |α|) ^ (1 + (1 / 2 + ε) d) C₁`,
`C = (2 C₂) ^ (2 / (ε d))` and `λ = 1 + 2 (1 + κ d) / (ε d)`. If the rationals `ξ₁` and `ξ`
satisfy `|ξ₁ - α| ≤ H(ξ₁) ^ (-κ)`, `H(ξ₁) ≥ C` and `|ξ - α| ≤ H(ξ) ^ (-κ)`, then
`H(ξ) ≤ H(ξ₁) ^ λ`.

Evertse takes `ε = (κ - 1 - d / 2) / ((2 κ + 2) d)`, `b` the denominator of `α` and
`C = max(e, (2 C₂) ^ (2 / (ε d)))`; the lower bound `e` is not needed here. The factor `48 b` in
`C₁` is the one of `TauCeti.exists_thue_auxiliary_polynomials`, which bounds the length of
Thue's auxiliary polynomials. -/
theorem thue_gap_principle {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) {ε : ℝ} (hε₀ : 0 < ε)
    (hε : ε ≤ (κ - 1 - (minpoly ℚ α).natDegree / 2) / ((2 * κ + 2) * (minpoly ℚ α).natDegree))
    {b : ℕ} (hb : 0 < b) (hbα : IsIntegral ℤ ((b : ℂ) * α)) {ξ₁ ξ : ℚ}
    (h₁ : ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ))
    (hC : (2 * (2 ^ ((1 / 2 + ε) * (minpoly ℚ α).natDegree) *
        (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * (minpoly ℚ α).natDegree) *
        (48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε)))) ^
          (2 / (ε * (minpoly ℚ α).natDegree)) ≤ mulHeight₁ ξ₁)
    (h : ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ)) :
    mulHeight₁ ξ ≤
      mulHeight₁ ξ₁ ^ (1 + 2 * (1 + κ * (minpoly ℚ α).natDegree) /
        (ε * (minpoly ℚ α).natDegree)) := by
  -- Suppose `H(ξ) > H(ξ₁) ^ λ` and put `t = log H(ξ) / log H(ξ₁)`. The logarithmic key
  -- inequality for every `r ≥ 1` then contradicts `t > λ`.
  set d : ℝ := ((minpoly ℚ α).natDegree : ℝ) with hd_def
  have hd2 : (2 : ℝ) ≤ d := by rw [hd_def]; exact_mod_cast hd
  have hu : 0 < ε * d := by positivity
  have huκ : ε * d * (2 * κ + 2) ≤ κ - 1 - d / 2 := by
    rw [le_div_iff₀ (mul_pos (by linarith) (by linarith))] at hε
    linarith
  have hε : ε < 1 / 2 := by nlinarith [(thue_gap_exponent_gt hd2 hκ hu huκ).1]
  set C₂ := 2 ^ ((1 / 2 + ε) * d) * (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * d) *
    (48 * b * max 1 (house α)) ^ (d * (1 + 1 / ε))
  have hC₂ : 1 ≤ C₂ := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have h48 : (1 : ℝ) ≤ 48 * b * max 1 (house α) := by nlinarith [le_max_left 1 (house α)]
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ?_ ?_) ?_
    · exact one_le_rpow one_le_two (by positivity)
    · exact one_le_rpow (by linarith [norm_nonneg α]) (by positivity)
    · exact one_le_rpow h48 (by positivity)
  by_contra! hlt
  set H₁ := mulHeight₁ ξ₁
  have hH₁ : 0 < H₁ := mulHeight₁_pos ξ₁
  -- `ℓ₁ = log H(ξ₁) ≥ (2 / (ε d)) log (2 C₂) > 0`.
  set ℓ₁ := log H₁
  have hG₀ : 2 / (ε * d) * log (2 * C₂) ≤ ℓ₁ := by
    have := log_le_log (by positivity) hC
    rwa [log_rpow (by positivity)] at this
  have hℓ₁ : 0 < ℓ₁ := lt_of_lt_of_le (mul_pos (by positivity) (log_pos (by linarith))) hG₀
  have hG : log (2 * C₂) ≤ ε * d / 2 * ℓ₁ := by
    have := mul_le_mul_of_nonneg_left hG₀ (by positivity : 0 ≤ ε * d / 2)
    rwa [← mul_assoc, show ε * d / 2 * (2 / (ε * d)) = 1 by field_simp, one_mul] at this
  refine thue_gap_log_contra hd2 hκ hε₀ huκ hℓ₁ hG (t := log (mulHeight₁ ξ) / ℓ₁) ?_
    fun r hr ↦ ?_
  · have := log_lt_log (by positivity) hlt
    rwa [log_rpow hH₁, ← lt_div_iff₀ hℓ₁] at this
  · obtain ⟨k, hk, hkey⟩ := thue_key_inequality_log hd hb hbα hε₀ hε hr (by linarith) h₁ h
    rw [div_mul_cancel₀ _ hℓ₁.ne']
    exact ⟨k, hk, hkey⟩

/-- **Thue's approximation theorem**, for complex `α`. Let `α` be a complex algebraic number of
degree `d ≥ 2` and let `κ > d / 2 + 1`. Then only finitely many rationals `ξ` satisfy
`|ξ - α| ≤ H(ξ) ^ (-κ)`. This is a variant of Evertse, Theorem 6.9, rather than that statement
verbatim: here `α` may be complex and every degree `d ≥ 2` is allowed. -/
theorem thue_approximation {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) :
    {ξ : ℚ | ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ)}.Finite := by
  -- Apply the gap principle with Evertse's `ε` and the denominator of `α`.
  have hα : IsIntegral ℚ α := by
    by_contra h
    rw [minpoly.eq_zero h, natDegree_zero] at hd
    omega
  have hd₀ : (0 : ℝ) < (minpoly ℚ α).natDegree := by positivity
  have hb : 0 < Algebra.natDenominator α := Nat.pos_of_ne_zero <|
    IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 hα.isAlgebraic)
  have hbα : IsIntegral ℤ ((Algebra.natDenominator α : ℂ) * α) := by
    simpa [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul α
  obtain ⟨C, lam, hgap⟩ : ∃ C lam : ℝ, ∀ ξ₁ ξ : ℚ, ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ) →
      C ≤ mulHeight₁ ξ₁ → ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ) →
        mulHeight₁ ξ ≤ mulHeight₁ ξ₁ ^ lam :=
    ⟨_, _, fun _ _ h₁ hC h ↦ thue_gap_principle hd hκ
      (div_pos (by linarith) (mul_pos (by linarith) hd₀)) le_rfl hb hbα h₁ hC h⟩
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
