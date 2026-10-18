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
Only the existence of `C` and `λ` is stated, not Evertse's explicit values.

By Northcott's theorem there are only finitely many rationals of bounded height, so the gap
principle gives **Thue's approximation theorem**: `|ξ - α| ≤ H(ξ) ^ (-κ)` has only finitely many
rational solutions `ξ`.

## Main results

* `TauCeti.thue_gap_principle`: Thue's gap principle, for complex algebraic `α`.
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

/-- The exponent comparison in the second case of the gap principle: if `(κ - 1) t ≤ a (r + 1)`
and `B r - (κ - 1) d ≤ t`, then `t (B (κ - 1) - a) ≤ a (B + (κ - 1) d)`. -/
private theorem thue_gap_exponent_le {κ a B d t r : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hxr : (κ - 1) * t ≤ a * (r + 1)) (hBr : B * r - (κ - 1) * d ≤ t) :
    t * (B * (κ - 1) - a) ≤ a * (B + (κ - 1) * d) := by
  nlinarith [mul_le_mul_of_nonneg_left hBr ha.le, mul_le_mul_of_nonneg_left hxr hB.le]

/-- **Thue's gap principle** (Evertse, Theorem 6.14). Let `α` be a complex algebraic number of
degree `d ≥ 2` and let `κ > d / 2 + 1`. There are constants `C ≥ 1` and `λ ≥ 1` such that for
all rationals `ξ₁` and `ξ` with `|ξ₁ - α| ≤ H(ξ₁) ^ (-κ)`, `H(ξ₁) ≥ C` and
`|ξ - α| ≤ H(ξ) ^ (-κ)`, the heights satisfy `H(ξ) ≤ H(ξ₁) ^ λ`. The degree hypothesis
already forces `α` to be algebraic. -/
theorem thue_gap_principle {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) :
    ∃ C lam : ℝ, 1 ≤ C ∧ 1 ≤ lam ∧ ∀ ξ₁ ξ : ℚ, ‖(ξ₁ : ℂ) - α‖ ≤ mulHeight₁ ξ₁ ^ (-κ) →
      C ≤ mulHeight₁ ξ₁ → ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ) →
        mulHeight₁ ξ ≤ mulHeight₁ ξ₁ ^ lam := by
  -- After fixing the parameters, suppose `H(ξ) > H(ξ₁) ^ λ`. For a suitable `r`, Thue's key
  -- inequality bounds `(H(ξ₁) ^ (N - k) H(ξ))⁻¹` by `(2 C₂) ^ r` times the larger of
  -- `H(ξ₁) ^ (-κ (r - k))` and `H(ξ) ^ (-κ)`. Taking logarithms, each case contradicts the
  -- choice of `r` or of `λ`.
  have hα : IsIntegral ℚ α := by
    by_contra h
    rw [minpoly.eq_zero h, natDegree_zero] at hd
    omega
  set d : ℝ := ((minpoly ℚ α).natDegree : ℝ) with hd_def
  have hd2 : (2 : ℝ) ≤ d := by rw [hd_def]; exact_mod_cast hd
  have hκ1 : 1 < κ := by linarith
  -- The parameter of the auxiliary polynomials and a denominator of `α`.
  set ε := (κ - 1 - d / 2) / (4 * d * κ) with hε_def
  have hε₀ : 0 < ε := div_pos (by linarith) (by positivity)
  have hε : ε < 1 / 2 := by
    rw [hε_def, div_lt_iff₀ (by positivity)]
    nlinarith
  have hu : 4 * (ε * d) * κ = κ - 1 - d / 2 := by
    rw [hε_def]
    field_simp
  have hu₀ : 0 < ε * d := by positivity
  have h4u : 4 * (ε * d) < κ - 1 - d / 2 := by nlinarith
  set b := Algebra.natDenominator α
  have hb : 0 < b := Nat.pos_of_ne_zero <|
    IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 hα.isAlgebraic)
  have hbα : IsIntegral ℤ ((b : ℂ) * α) := by
    simpa [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul α
  set C₂ := 2 ^ ((1 / 2 + ε) * d) * (1 + ‖α‖) ^ (1 + (1 / 2 + ε) * d) *
    (48 * b * max 1 (house α)) ^ (d * (1 + 1 / ε))
  have hC₂ : 0 < C₂ := by positivity
  -- The exponents `a = (1 / 2 + 2 ε) d` and `B = κ - 2 ε d (κ - 1) - a = (κ - d / 2 + 1) / 2`.
  set a := (1 / 2 + ε) * d + ε * d with ha_def
  have ha : 0 < a := by positivity
  set B := κ - 2 * (ε * d) * (κ - 1) - a with hB_def
  have hB_eq : B = (κ - d / 2 + 1) / 2 := by
    rw [hB_def, ha_def]
    linarith
  have hB : 0 < B := by
    rw [hB_eq]
    linarith
  have hBa : 0 < B * (κ - 1) - a := by
    rw [hB_eq, ha_def]
    nlinarith [mul_pos (sub_pos.2 hκ) (sub_pos.2 hκ),
      mul_pos (sub_pos.2 hκ) (by positivity : 0 < d)]
  set lam := max (a / (κ - 1)) (a * (B + (κ - 1) * d) / (B * (κ - 1) - a)) + 1
  have hlam₁ := le_max_left (a / (κ - 1)) (a * (B + (κ - 1) * d) / (B * (κ - 1) - a))
  have hlam₂ := le_max_right (a / (κ - 1)) (a * (B + (κ - 1) * d) / (B * (κ - 1) - a))
  have hlam₀ : 0 < a / (κ - 1) := div_pos ha (by linarith)
  refine ⟨max (exp 1) ((2 * C₂) ^ (ε * d)⁻¹), lam,
    (one_le_exp zero_le_one).trans (le_max_left _ _), by linarith, fun ξ₁ ξ₂ h₁ hC h₂ ↦ ?_⟩
  by_contra! hlt
  set H₁ := mulHeight₁ ξ₁
  set H₂ := mulHeight₁ ξ₂
  have hH₁ : 0 < H₁ := mulHeight₁_pos ξ₁
  have hH₂ : 0 < H₂ := mulHeight₁_pos ξ₂
  -- Pass to logarithms: `ℓ₁ = log H(ξ₁) ≥ 1`, and `t = log H(ξ₂) / ℓ₁ > λ`.
  set ℓ₁ := log H₁
  have hℓ₁ : 1 ≤ ℓ₁ := (le_log_iff_exp_le hH₁).2 ((le_max_left _ _).trans hC)
  have hℓ₁₀ : 0 < ℓ₁ := by linarith
  have hG : log (2 * C₂) ≤ ε * d * ℓ₁ := by
    have := log_le_log (by positivity) ((le_max_right _ _).trans hC)
    rwa [log_rpow (by positivity), inv_mul_le_iff₀ hu₀] at this
  set t := log H₂ / ℓ₁
  have hℓ₂ : log H₂ = t * ℓ₁ := (div_mul_cancel₀ _ hℓ₁₀.ne').symm
  have ht : lam < t := by
    have := log_lt_log (by positivity) hlt
    rw [log_rpow hH₁, hℓ₂] at this
    exact lt_of_mul_lt_mul_right this hℓ₁₀.le
  -- Choose `r = ⌈x⌉ - 1`, where `x = (κ - 1) t / a > 1`.
  set x := (κ - 1) * t / a
  have hx : 1 < x := by
    rw [lt_div_iff₀ ha, one_mul, ← div_lt_iff₀' (by linarith)]
    linarith
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
  have h₁' : ‖(ξ₁ : ℂ) - α‖ ≤ 1 :=
    h₁.trans (rpow_le_one_of_one_le_of_nonpos (one_le_mulHeight₁ ξ₁) (by linarith))
  obtain ⟨k, hkN, hk, hkey⟩ := thue_key_inequality hd hb hbα hε₀ hε hr h₁' ξ₂
  set N := ⌊(1 / 2 + ε) * d * r⌋₊
  have hN : (N : ℝ) * ℓ₁ ≤ (1 / 2 + ε) * d * r * ℓ₁ :=
    mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hℓ₁₀.le
  have hNk : ((N - k : ℕ) : ℝ) = N - k := Nat.cast_sub hkN
  have hkℓ : 0 ≤ (k : ℝ) * ℓ₁ := by positivity
  -- Bound both terms of the key inequality by their maximum `M`.
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
  have hlog : -((N - k) * ℓ₁ + t * ℓ₁) ≤ r * log (2 * C₂) + log (max X Y) := by
    have := log_le_log (by positivity) hle
    rwa [log_inv, log_mul (by positivity) (by positivity), log_mul (by positivity) hM.ne',
      log_pow, log_pow, hNk, hℓ₂] at this
  have hrG : r * log (2 * C₂) ≤ r * (ε * d * ℓ₁) := mul_le_mul_of_nonneg_left hG (by positivity)
  rcases le_total X Y with hXY | hXY
  · -- If `Y` is the maximum, then `(κ - 1) t ≤ a r`, contradicting the choice of `r`.
    rw [max_eq_right hXY, log_rpow hH₂, hℓ₂] at hlog
    have : (κ - 1) * t * ℓ₁ ≤ a * r * ℓ₁ := by
      rw [ha_def]
      linarith
    linarith [le_of_mul_le_mul_right this hℓ₁₀]
  · -- If `X` is the maximum, then `B r - (κ - 1) d ≤ t`, contradicting `t > λ`.
    rw [max_eq_left hXY, log_pow, log_rpow hH₁] at hlog
    have hrk : (r : ℝ) - k ≤ ((r - k : ℕ) : ℝ) := by
      rcases le_total k r with h | h
      · rw [Nat.cast_sub h]
      · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_nonpos]
        exact_mod_cast h
    have hkr : κ * ((r - k) * ℓ₁) ≤ κ * (((r - k : ℕ) : ℝ) * ℓ₁) := by gcongr
    have hkk : (κ - 1) * (k * ℓ₁) ≤ (κ - 1) * (d * (2 * ε * r + 1) * ℓ₁) := by
      gcongr
    have : (B * r - (κ - 1) * d) * ℓ₁ ≤ t * ℓ₁ := by
      rw [hB_def, ha_def]
      linarith
    have hle := thue_gap_exponent_le ha hB hxr (le_of_mul_le_mul_right this hℓ₁₀)
    rw [← le_div_iff₀ hBa] at hle
    linarith

/-- **Thue's approximation theorem**, for complex `α`. Let `α` be a complex algebraic number of
degree `d ≥ 2` and let `κ > d / 2 + 1`. Then only finitely many rationals `ξ` satisfy
`|ξ - α| ≤ H(ξ) ^ (-κ)`. This is a variant of Evertse, Theorem 6.9, rather than that statement
verbatim: here `α` may be complex and every degree `d ≥ 2` is allowed. -/
theorem thue_approximation {α : ℂ} (hd : 2 ≤ (minpoly ℚ α).natDegree) {κ : ℝ}
    (hκ : (minpoly ℚ α).natDegree / 2 + 1 < κ) :
    {ξ : ℚ | ‖(ξ : ℂ) - α‖ ≤ mulHeight₁ ξ ^ (-κ)}.Finite := by
  obtain ⟨C, lam, -, -, hgap⟩ := thue_gap_principle hd hκ
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
