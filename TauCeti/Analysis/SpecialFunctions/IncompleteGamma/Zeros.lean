/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi

/-!
# Zeros of Tricomi's function in the parameter

For a fixed real argument `x`, this file locates the real zeros of `a ↦ γ*(a, x)`, Tricomi's
entire incomplete Gamma function `Complex.tricomiIncompleteGamma`, on the negative real axis
(DLMF §8.13(iii)).

## Main results

* `Complex.existsUnique_mem_Ioo_tricomiIncompleteGamma_eq_zero_of_neg`: for `x < 0`,
  `γ*(·, x)` has exactly one zero in each interval `(−m − 1, −m)`, `m ∈ ℕ`;
* `Complex.tricomiIncompleteGamma_param_zeros_of_neg`: for `x < 0`, `γ*(·, x)` has exactly two
  zeros in each interval `(−m − 2, −m)`, one on each side of `−m − 1`; the case `m = 2n − 2` is
  DLMF §8.13(iii)(a);
* `Complex.tricomiIncompleteGamma_zero_right_eq_zero_iff`: the zeros of `γ*(·, 0)` are exactly
  the integers `a ≤ −1` (DLMF §8.13(iii)(c)).

## Implementation notes

For real `a ∉ −ℕ` and real `x`, the series 8.7.1 gives
`Γ(a) γ*(a, x) = ∑ (−x)ᵏ / (k! (a + k))`
(`Complex.hasSum_tricomiIncompleteGamma_of_ne_neg_natCast`). When `x < 0` every numerator
`(−x)ᵏ` is positive, so on an interval `(−m − 1, −m)` each term is strictly decreasing in `a`,
and the terms `k = m + 1` and `k = m` tend to `+∞` and `−∞` at the two ends. The series is
therefore strictly decreasing from `+∞` to `−∞` there, and it has exactly one zero. At the
integer `−m − 1` itself, `γ*(−m − 1, x) = x^{m + 1} ≠ 0`.

## References

* NIST Digital Library of Mathematical Functions, §8.13(iii), <https://dlmf.nist.gov/8.13>.
* K. S. Kölbig, *On the zeros of the incomplete gamma function*, Math. Comp. 26 (1972),
  751–755.
-/

public section

noncomputable section

open Filter Set
open scoped Nat

namespace Complex

/-- The `k`th term `(−x)ᵏ / (k! (a + k))` of the series of `Γ(a) γ*(a, x)` for real `a` and `x`. -/
private def paramTerm (x a : ℝ) (k : ℕ) : ℝ := (-x) ^ k / (k ! * (a + k))

/-- For real `a ∉ −ℕ` and real `x`, the real series `∑ (−x)ᵏ / (k! (a + k))` sums to
`Γ(a) γ*(a, x)`. -/
private theorem hasSum_ofReal_paramTerm {a : ℝ} (ha : ∀ n : ℕ, a ≠ -n) (x : ℝ) :
    HasSum (fun k => (paramTerm x a k : ℂ)) (Real.Gamma a * tricomiIncompleteGamma a x) := by
  have ha' : ∀ n : ℕ, (a : ℂ) ≠ -n := fun n h => ha n (by exact_mod_cast h)
  have hΓ : Gamma (a : ℂ) ≠ 0 := Gamma_ne_zero ha'
  rw [← Gamma_ofReal]
  refine ((hasSum_tricomiIncompleteGamma_of_ne_neg_natCast ha' x).mul_left
    (Gamma (a : ℂ))).congr_fun fun k => ?_
  rw [mul_inv_cancel_left₀ hΓ, paramTerm]
  push_cast
  ring

private theorem summable_paramTerm {a : ℝ} (ha : ∀ n : ℕ, a ≠ -n) (x : ℝ) :
    Summable (paramTerm x a) :=
  summable_ofReal.1 (hasSum_ofReal_paramTerm ha x).summable

/-- `Γ(a) γ*(a, x)` is the real number `∑ (−x)ᵏ / (k! (a + k))`. -/
private theorem ofReal_tsum_paramTerm {a : ℝ} (ha : ∀ n : ℕ, a ≠ -n) (x : ℝ) :
    ((∑' k, paramTerm x a k : ℝ) : ℂ) = Real.Gamma a * tricomiIncompleteGamma a x :=
  (hasSum_ofReal.2 (summable_paramTerm ha x).hasSum).unique (hasSum_ofReal_paramTerm ha x)

private theorem tricomiIncompleteGamma_eq_zero_iff_tsum {a : ℝ} (ha : ∀ n : ℕ, a ≠ -n)
    (x : ℝ) : tricomiIncompleteGamma a x = 0 ↔ ∑' k, paramTerm x a k = 0 := by
  have hΓ : (Real.Gamma a : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.Gamma_ne_zero ha)
  rw [← ofReal_eq_zero, ofReal_tsum_paramTerm ha, mul_eq_zero, or_iff_right hΓ]

/-- A point of `(−m − 1, −m)` is not a nonpositive integer. -/
private theorem ne_neg_natCast_of_mem_Ioo {m : ℕ} {a : ℝ} (ha : a ∈ Ioo (-(m + 1 : ℝ)) (-m))
    (n : ℕ) : a ≠ -n := by
  rintro rfl
  have h₁ : (n : ℝ) < m + 1 := by linarith [ha.1]
  have h₂ : (m : ℝ) < n := by linarith [ha.2]
  norm_cast at h₁ h₂
  omega

/-- The series `a ↦ ∑ (−x)ᵏ / (k! (a + k))` is continuous on `(−m − 1, −m)`, where it equals
`Γ(a) Re γ*(a, x)`. -/
private theorem continuousOn_tsum_paramTerm (x : ℝ) (m : ℕ) :
    ContinuousOn (fun a => ∑' k, paramTerm x a k) (Ioo (-(m + 1 : ℝ)) (-m)) := by
  have hγ : Continuous fun a : ℝ => (tricomiIncompleteGamma a x).re :=
    continuous_re.comp ((differentiable_tricomiIncompleteGamma_left x).continuous.comp
      continuous_ofReal)
  refine ContinuousOn.congr (f := fun a => Real.Gamma a * (tricomiIncompleteGamma a x).re)
    (fun a ha => ((Real.differentiableAt_Gamma (ne_neg_natCast_of_mem_Ioo ha)).continuousAt.mul
      hγ.continuousAt).continuousWithinAt) fun a ha => ?_
  have h := congr_arg re (ofReal_tsum_paramTerm (ne_neg_natCast_of_mem_Ioo ha) x)
  rwa [ofReal_re, re_ofReal_mul] at h

/-- For `x < 0`, each term `(−x)ᵏ / (k! (a + k))` is strictly decreasing in `a` on
`(−m − 1, −m)`. -/
private theorem paramTerm_lt_paramTerm {x : ℝ} (hx : x < 0) {m : ℕ} {a b : ℝ}
    (ha : a ∈ Ioo (-(m + 1 : ℝ)) (-m)) (hb : b ∈ Ioo (-(m + 1 : ℝ)) (-m)) (hab : a < b)
    (k : ℕ) : paramTerm x b k < paramTerm x a k := by
  have hc : 0 < (-x) ^ k / k ! := by have := neg_pos.2 hx; positivity
  have hprod : 0 < (a + k) * (b + k) := by
    rcases le_or_gt k m with hk | hk
    · have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
      exact mul_pos_of_neg_of_neg (by linarith [hb.2]) (by linarith [hb.2])
    · have hk' : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk
      exact mul_pos (by linarith [ha.1]) (by linarith [ha.1])
  have hak : a + k ≠ 0 := left_ne_zero_of_mul hprod.ne'
  have hbk : b + k ≠ 0 := right_ne_zero_of_mul hprod.ne'
  rw [paramTerm, paramTerm, ← div_div, ← div_div, ← sub_pos, div_sub_div _ _ hak hbk]
  refine div_pos ?_ hprod
  have h : (-x) ^ k / k ! * (b + k) - (a + k) * ((-x) ^ k / k !) =
      (-x) ^ k / k ! * (b - a) := by ring
  rw [h]
  exact mul_pos hc (sub_pos.2 hab)

/-- For `x < 0` and `a < b` in `(−m − 1, −m)`, the series drops by at least as much as any one
of its terms. -/
private theorem paramTerm_sub_le_tsum_sub {x : ℝ} (hx : x < 0) {m : ℕ} {a b : ℝ}
    (ha : a ∈ Ioo (-(m + 1 : ℝ)) (-m)) (hb : b ∈ Ioo (-(m + 1 : ℝ)) (-m)) (hab : a < b)
    (i : ℕ) :
    paramTerm x a i - paramTerm x b i ≤ ∑' k, paramTerm x a k - ∑' k, paramTerm x b k := by
  have hsa := summable_paramTerm (ne_neg_natCast_of_mem_Ioo ha) x
  have hsb := summable_paramTerm (ne_neg_natCast_of_mem_Ioo hb) x
  rw [← hsa.tsum_sub hsb]
  exact (hsa.sub hsb).le_tsum i fun j _ =>
    sub_nonneg.2 (paramTerm_lt_paramTerm hx ha hb hab j).le

/-- For `x < 0`, the series `a ↦ ∑ (−x)ᵏ / (k! (a + k))` is strictly decreasing on
`(−m − 1, −m)`. -/
private theorem strictAntiOn_tsum_paramTerm {x : ℝ} (hx : x < 0) (m : ℕ) :
    StrictAntiOn (fun a => ∑' k, paramTerm x a k) (Ioo (-(m + 1 : ℝ)) (-m)) :=
  fun _ ha _ hb hab => sub_pos.1 <|
    (sub_pos.2 (paramTerm_lt_paramTerm hx ha hb hab 0)).trans_le
      (paramTerm_sub_le_tsum_sub hx ha hb hab 0)

/-- For `x < 0`, the series `a ↦ ∑ (−x)ᵏ / (k! (a + k))` has a zero in `(−m − 1, −m)`. -/
private theorem exists_tsum_paramTerm_eq_zero {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a ∈ Ioo (-(m + 1 : ℝ)) (-m), ∑' k, paramTerm x a k = 0 := by
  set J := Ioo (-(m + 1 : ℝ)) (-m)
  set S := fun a => ∑' k, paramTerm x a k
  -- the midpoint `b₀ = −m − 1/2` is the reference point for both ends
  have hb₀ : -(m : ℝ) - 1 / 2 ∈ J := ⟨by linarith, by linarith⟩
  have hy := neg_pos.2 hx
  -- `c δ⁻¹` exceeds any bound for small `δ > 0`
  have hsmall : ∀ c : ℝ, 0 < c → ∀ C : ℝ, ∃ δ : ℝ, C < c * δ⁻¹ ∧ δ ∈ Ioo (0 : ℝ) (1 / 2) :=
    fun c hc C => (((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hc).eventually_gt_atTop
      C |>.and (Ioo_mem_nhdsGT (by norm_num))).exists
  -- near `−m − 1`, the term `k = m + 1` tends to `+∞`
  obtain ⟨δ₁, hC₁, hδ₁, hδ₁'⟩ := hsmall ((-x) ^ (m + 1) / (m + 1)!) (by positivity)
    (paramTerm x (-(m : ℝ) - 1 / 2) (m + 1) - S (-(m : ℝ) - 1 / 2))
  have ha₁ : -(m + 1 : ℝ) + δ₁ ∈ J := ⟨by linarith, by linarith⟩
  have hS₁ : 0 < S (-(m + 1 : ℝ) + δ₁) := by
    have h := paramTerm_sub_le_tsum_sub hx ha₁ hb₀ (by linarith) (m + 1)
    have he : paramTerm x (-(m + 1 : ℝ) + δ₁) (m + 1) = (-x) ^ (m + 1) / (m + 1)! * δ₁⁻¹ := by
      rw [paramTerm, show -(m + 1 : ℝ) + δ₁ + ((m + 1 : ℕ) : ℝ) = δ₁ by push_cast; ring,
        ← div_div, div_eq_mul_inv]
    simp only [S] at hC₁ ⊢
    linarith
  -- near `−m`, the term `k = m` tends to `−∞`
  obtain ⟨δ₂, hC₂, hδ₂, hδ₂'⟩ := hsmall ((-x) ^ m / m !) (by positivity)
    (S (-(m : ℝ) - 1 / 2) - paramTerm x (-(m : ℝ) - 1 / 2) m)
  have hb₂ : -(m : ℝ) - δ₂ ∈ J := ⟨by linarith, by linarith⟩
  have hS₂ : S (-(m : ℝ) - δ₂) < 0 := by
    have h := paramTerm_sub_le_tsum_sub hx hb₀ hb₂ (by linarith) m
    have he : paramTerm x (-(m : ℝ) - δ₂) m = -((-x) ^ m / m ! * δ₂⁻¹) := by
      rw [paramTerm, show -(m : ℝ) - δ₂ + m = -δ₂ by ring, ← div_div, div_neg, div_eq_mul_inv]
    simp only [S] at hC₂ ⊢
    linarith
  -- the intermediate value theorem on `[−m − 1 + δ₁, −m − δ₂] ⊆ J`
  have hsub : Icc (-(m + 1 : ℝ) + δ₁) (-(m : ℝ) - δ₂) ⊆ J :=
    fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩
  obtain ⟨a, ha, ha0⟩ := intermediate_value_Icc' (by linarith)
    ((continuousOn_tsum_paramTerm x m).mono hsub) ⟨hS₂.le, hS₁.le⟩
  exact ⟨a, hsub ha, ha0⟩

/-- For `x < 0`, Tricomi's function `γ*(·, x)` has exactly one zero in each interval
`(−m − 1, −m)`, `m ∈ ℕ`. -/
theorem existsUnique_mem_Ioo_tricomiIncompleteGamma_eq_zero_of_neg {x : ℝ} (hx : x < 0)
    (m : ℕ) : ∃! a : ℝ, a ∈ Ioo (-(m + 1 : ℝ)) (-m) ∧ tricomiIncompleteGamma a x = 0 := by
  obtain ⟨a, ha, ha0⟩ := exists_tsum_paramTerm_eq_zero hx m
  refine ⟨a, ⟨ha, (tricomiIncompleteGamma_eq_zero_iff_tsum
    (ne_neg_natCast_of_mem_Ioo ha) x).2 ha0⟩, fun b ⟨hb, hb0⟩ => ?_⟩
  rw [tricomiIncompleteGamma_eq_zero_iff_tsum (ne_neg_natCast_of_mem_Ioo hb)] at hb0
  exact (strictAntiOn_tsum_paramTerm hx m).injOn hb ha (hb0.trans ha0.symm)

/-- For `x < 0`, Tricomi's function `γ*(·, x)` has exactly two zeros in each interval
`(−m − 2, −m)`, `m ∈ ℕ`, one on each side of `−m − 1`. For `m = 2n − 2` this is
DLMF §8.13(iii)(a): `γ*(·, x)` has exactly two zeros in `−2n < a < 2 − 2n`. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a₁ ∈ Ioo (-(m + 2 : ℝ)) (-(m + 1)), ∃ a₂ ∈ Ioo (-(m + 1 : ℝ)) (-m),
      {a : ℝ | a ∈ Ioo (-(m + 2 : ℝ)) (-m) ∧ tricomiIncompleteGamma a x = 0} = {a₁, a₂} := by
  have h₁ := existsUnique_mem_Ioo_tricomiIncompleteGamma_eq_zero_of_neg hx (m + 1)
  have e : (((m + 1 : ℕ) : ℝ) + 1) = m + 2 := by push_cast; ring
  rw [e, Nat.cast_succ] at h₁
  obtain ⟨a₁, ⟨ha₁, ha₁0⟩, hu₁⟩ := h₁
  obtain ⟨a₂, ⟨ha₂, ha₂0⟩, hu₂⟩ :=
    existsUnique_mem_Ioo_tricomiIncompleteGamma_eq_zero_of_neg hx m
  refine ⟨a₁, ha₁, a₂, ha₂, Set.ext fun a => ⟨fun ⟨ha, ha0⟩ => ?_, fun ha => ?_⟩⟩
  · rcases lt_trichotomy a (-(m + 1)) with h | rfl | h
    · exact Or.inl (hu₁ a ⟨⟨ha.1, h⟩, ha0⟩)
    · -- at the integer `−m − 1`, `γ*(−m − 1, x) = x^{m + 1}` does not vanish
      have he : ((-(m + 1 : ℝ) : ℝ) : ℂ) = -((m + 1 : ℕ) : ℂ) := by push_cast; rfl
      rw [he, tricomiIncompleteGamma_neg_natCast] at ha0
      exact absurd (pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 ha0)
        (ofReal_ne_zero.2 hx.ne)
    · exact Or.inr (hu₂ a ⟨⟨h, ha.2⟩, ha0⟩)
  · rcases ha with rfl | rfl
    · exact ⟨⟨ha₁.1, by linarith [ha₁.2]⟩, ha₁0⟩
    · exact ⟨⟨by linarith [ha₂.1], ha₂.2⟩, ha₂0⟩

/-- The zeros of `γ*(·, 0) = 1 / Γ(· + 1)` are exactly the integers `a ≤ −1`
(DLMF §8.13(iii)(c)). -/
theorem tricomiIncompleteGamma_zero_right_eq_zero_iff {a : ℂ} :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, a = -(n + 1) := by
  rw [tricomiIncompleteGamma_zero_right, inv_eq_zero, Gamma_eq_zero_iff]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, by linear_combination hn⟩,
    fun ⟨n, hn⟩ => ⟨n, by rw [hn]; ring⟩⟩

end Complex
