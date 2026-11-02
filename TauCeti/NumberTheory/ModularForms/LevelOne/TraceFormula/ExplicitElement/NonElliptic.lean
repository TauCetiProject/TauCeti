/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.ClassNumber
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Contribution
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Total

/-!
# The non-elliptic trace fibres of Popa–Zagier's explicit element

Let `TauCeti.PopaZagier.weight M` be twelve times the coefficient of the integral matrix `M` in
Popa and Zagier's explicit Hecke element, their eq. (15). The elliptic trace fibres, those with
`t² - 4 n < 0`, are evaluated in `ExplicitElement/ClassNumber.lean`. This file evaluates the
remaining fibres, those with `t² - 4 n ≥ 0`: for `n > 0` the weights of the integral matrices of
trace `t` and determinant `n` sum to
* `0` if `t < 0`;
* `0` if `t² - 4 n` is not a square;
* `12 |d - a|` if `t = a + d` and `n = a d` with `a ≠ d` positive (the split hyperbolic fibres);
* `2` if `t = 2 a` and `n = a²` with `a` positive (the parabolic fibres, which contain the scalar
  matrix `a • 1`).

In Popa and Zagier's normalisation the coefficients of their element sum to `|d - a|` over a split
fibre of positive trace and to `1/6` over a parabolic fibre of positive trace. These are the
fibre sums which the trace of the element on binary forms
(`TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_eq_sum_trace_fibres`)
needs besides the class-number sums of the elliptic fibres: in the Eichler–Selberg trace formula
the split fibres give the divisor-sum terms and the parabolic fibres the terms with `H(0) = -1/12`.

## Main results

* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_zero_of_neg`: the fibre sum vanishes when
  `t < 0` and `t² - 4 n ≥ 0`.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_zero_of_not_isSquare`: the fibre sum vanishes
  when `t² - 4 n ≥ 0` is not a square.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_mul_eq_twelve_mul_abs_sub`: the fibre of
  trace `a + d` and determinant `a d`, for `a ≠ d` positive, sums to `12 |d - a|`.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_two_mul_sq_eq_two`: the fibre of trace `2 a` and
  determinant `a²`, for `a` positive, sums to `2`.

## Proof

The translation `M ↦ M + 1` preserves the fibre sums
(`TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_two`) and changes `(t, n)` to
`(t + 2, n + t + 1)`, keeping `t² - 4 n`.

For negative trace, translating upwards decreases `n`, and ends at a fibre with `n ≤ 0`, where
every weight vanishes because every matrix of nonzero weight has positive determinant.

For positive trace, translating downwards decreases `n` and ends at a fibre with `0 < n < t`. There
the sums `T₂`, `T₃` and `T₄` of eq. (15) contribute nothing and the only matrices occurring in
`T₁` are `(1 b; 0 n)` with `0 ≤ b < n`, so every matrix of the fibre has weight zero unless
`t = n + 1`. The weights of these matrices are `6, 12, …, 12, 6` (or `2` when `n = 1`) by
`TauCeti.PopaZagier.weight_upperTriangular`, with sum `12 (n - 1)` (or `2`), twelve times the
coefficient sum `TauCeti.PopaZagier.sum_upperTriangularCoeff`. The
fibre `(n + 1, n)` has discriminant `(n - 1)²`, and translating it upwards reaches the fibre of
trace `a + d` and determinant `a d` with `d - a = n - 1`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, eq. (15).
-/

public section

open Matrix

namespace TauCeti

namespace PopaZagier

variable {t n : ℤ}

/-- A fibre of nonpositive determinant has weight sum zero: every matrix of nonzero weight has
positive determinant. -/
private theorem finsum_weight_traceDetFiber_of_nonpos (hn : n ≤ 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun M ↦ by
    by_contra h
    have := det_pos_of_weight_ne_zero h
    rw [(mem_traceDetFiber.mp M.2).2] at this
    omega

/-- **Negative trace.** If `t < 0` and `t² - 4 n ≥ 0`, then the weights of the integral matrices
of trace `t` and determinant `n` sum to zero. -/
theorem finsum_weight_traceDetFiber_eq_zero_of_neg (ht : t < 0) (hD : 4 * n ≤ t ^ 2) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = 0 := by
  induction hk : n.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
  rcases le_or_gt n 0 with hn | hn
  · exact finsum_weight_traceDetFiber_of_nonpos hn
  -- translate upwards to the fibre `(t + 2, n + t + 1)`, of smaller determinant
  rw [← finsum_weight_traceDetFiber_add_two hn]
  have ht₂ : t ≤ -2 := by nlinarith
  rcases (show t + 2 < 0 ∨ t + 2 = 0 by omega) with ht' | ht'
  · exact ih _ (by omega) ht' (by nlinarith) rfl
  · exact finsum_weight_traceDetFiber_of_nonpos (by nlinarith)

/-! ### Fibres with `0 < n < t` -/

/-- With `n = a d - b c`, `t = a + d`, `0 < n < t` and `0 ≤ c < a`, the first line
`a - d ≤ -b ≤ c` of `T₁` forces `a = 1`. -/
private theorem eq_one_of_le_neg_le {a b c d : ℤ} (htr : a + d = t) (hdet : a * d - b * c = n)
    (hn : 0 < n) (ht : n < t) (hc : 0 ≤ c) (hca : c < a) (h₁ : a - d ≤ -b) (h₂ : -b ≤ c) :
    a = 1 := by
  -- `-b c = a² - a t + n`, and `4 (-b c) = (a - d)² - (t² - 4 n)` with `t² - 4 n ≥ (n - 1)²`
  have hf : -b * c = a ^ 2 - a * t + n := by rw [← htr, ← hdet]; ring
  have hD : (n - 1) ^ 2 ≤ t ^ 2 - 4 * n := by nlinarith
  rcases lt_or_ge a d with had | had
  · -- `-b c ≥ (a - d) c ≥ (a - d) (a - 1)`, so `(a - 1)² ≤ n - t + 1 ≤ 0`
    have h₃ : (a - d) * c ≤ -b * c := mul_le_mul_of_nonneg_right h₁ hc
    have h₄ : (a - d) * (a - 1) ≤ (a - d) * c :=
      mul_le_mul_of_nonpos_left (by omega) (by omega)
    nlinarith [sq_nonneg (a - 1)]
  · -- `(a - d)² ≤ b² ≤ -b c = ((a - d)² - (t² - 4 n)) / 4`, so `t² = 4 n`, `n = 1`
    -- and `a = d`
    have h₃ : (a - d) ^ 2 ≤ (-b) ^ 2 := pow_le_pow_left₀ (by omega) h₁ 2
    have h₄ : (-b) * (-b) ≤ -b * c := mul_le_mul_of_nonneg_left h₂ (by omega)
    have h₅ : t ^ 2 - 4 * n = 0 := by nlinarith
    have h₆ : n = 1 := by nlinarith [sq_nonneg (n - 1)]
    have h₇ : (a - d) ^ 2 = 0 := by nlinarith
    have : a = d := by nlinarith [sq_nonneg (a - d)]
    nlinarith

/-- In a fibre with `0 < n < t`, a matrix has nonzero weight only if it is of the form
`(1 b; 0 d)`. -/
private theorem weight_eq_of_lt {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ traceDetFiber (Fin 2) t n) (hn : 0 < n) (ht : n < t) :
    weight M = if M 0 0 = 1 ∧ M 1 0 = 0 then weight !![1, M 0 1; 0, M 1 1] else 0 := by
  split_ifs with hT
  · conv_lhs => rw [eta_fin_two M, hT.1, hT.2]
  obtain ⟨htr, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
  rw [weight]
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  -- the discriminant of `Q_M` is `(a - d)² + 4 b c = t² - 4 n ≥ (n - 1)² ≥ 0`
  have hdisc : 0 ≤ (a - d) ^ 2 + 4 * b * c := by
    have : (a - d) ^ 2 + 4 * b * c = t ^ 2 - 4 * n := by rw [← htr, ← hdet]; ring
    nlinarith [sq_nonneg (n - 1)]
  -- in `T₁` the first line forces `a = 1`, and then `0 ≤ c < a` forces `c = 0`
  have h₁ : weight₁ a b c d = 0 := by
    unfold weight₁
    split_ifs with hg
    · by_contra hne
      obtain ⟨hx, hy⟩ := le_of_chainWeight₃_ne_zero hne
      have ha := eq_one_of_le_neg_le htr hdet hn ht hg.1 hg.2 hx hy
      exact hT ⟨ha, by omega⟩
    · rfl
  -- in `T₂`, `d ≤ 0` and `n = a d - b c ≥ t + d² - 2 d ≥ t`
  have h₂ : weight₂ a b c d = 0 := by
    unfold weight₂
    split_ifs with hg
    · by_contra hne
      obtain ⟨hx, hy⟩ := le_of_chainWeight₃_ne_zero hne
      have h₃ : (1 - d) * c ≤ -b * c := mul_le_mul_of_nonneg_right (by omega) (by omega)
      have h₄ : (1 - d) * (a - d) ≤ (1 - d) * c := mul_le_mul_of_nonneg_left hy (by omega)
      nlinarith
    · rfl
  -- in `T₃` and `T₄` the first line forces a negative discriminant
  have h₃ : weight₃ a b c d = 0 := by
    unfold weight₃
    split_ifs with hg
    · by_contra hne
      obtain ⟨h0, hy, hz⟩ := le_of_chainWeight₄_ne_zero hne
      nlinarith [mul_le_mul_of_nonneg_left hz hg.2.le, mul_le_mul hy hy h0 hg.2.le]
    · rfl
  have h₄ : weight₄ a b c d = 0 := by
    unfold weight₄
    split_ifs with hg
    · by_contra hne
      obtain ⟨h0, hy, hz⟩ := le_of_chainWeight₄_ne_zero hne
      nlinarith [mul_le_mul_of_nonneg_left hz hg.2.le, mul_le_mul hy hy h0 hg.2.le]
    · rfl
  rw [h₁, h₂, h₃, h₄]
  norm_num

/-- The weights of the matrices `(1 k; 0 N)`, `0 ≤ k < N`, sum to `12 (N - 1)`, or to `2` when
`N = 1`. -/
private theorem sum_range_weight_upperTriangular (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ Finset.range N, weight !![1, (k : ℤ); 0, (N : ℤ)] =
      if N = 1 then 2 else 12 * ((N : ℤ) - 1) := by
  -- each weight is twelve times the coefficient summed in `sum_upperTriangularCoeff`
  have hw : ∀ k ∈ Finset.range N, ((weight !![1, (k : ℤ); 0, (N : ℤ)] : ℤ) : ℚ) =
      12 * upperTriangularCoeff ((1 : ℕ) : ℤ) (k : ℤ) N := by
    intro k _
    rw [weight_upperTriangular _ _ _ one_pos (by omega), upperTriangularCoeff_def]
    push_cast
    split_ifs <;> norm_num
  rw [← Int.cast_inj (α := ℚ), Int.cast_sum, Finset.sum_congr rfl hw, ← Finset.mul_sum,
    sum_upperTriangularCoeff 1 N one_pos]
  obtain rfl | hN₁ := eq_or_ne N 1
  · norm_num
  · simp [hN₁, show 1 < N by omega, Nat.cast_sub (show 1 ≤ N by omega)]

/-- **The fibres with `0 < n < t`.** The weights of the matrices of trace `t` and determinant `n`
sum to `12 (n - 1)`, or to `2` when `n = 1`, if `t = n + 1`, and to zero otherwise. -/
private theorem finsum_weight_traceDetFiber_of_lt (hn : 0 < n) (ht : n < t) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 =
      if t = n + 1 then (if n = 1 then 2 else 12 * (n - 1)) else 0 := by
  classical
  rw [finsum_congr fun M ↦ weight_eq_of_lt M.2 hn ht]
  by_cases ht₁ : t = n + 1
  swap
  · -- a matrix `(1 b; 0 d)` of determinant `n` has trace `n + 1`
    rw [ite_eq_right ht₁]
    refine finsum_eq_zero_of_forall_eq_zero fun M ↦ ite_eq_right fun h ↦ ht₁ ?_
    obtain ⟨htr, hdet⟩ := mem_traceDetFiber_fin_two.mp M.2
    simp only [h.1, h.2, one_mul, mul_zero, sub_zero] at htr hdet
    omega
  rw [ite_eq_left ht₁]
  subst ht₁
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  have hmem (k : ℕ) :
      !![1, (k : ℤ); 0, (N : ℤ)] ∈ traceDetFiber (Fin 2) ((N : ℤ) + 1) N :=
    mem_traceDetFiber_fin_two.mpr ⟨by simp [add_comm], by simp⟩
  set s : Finset (traceDetFiber (Fin 2) ((N : ℤ) + 1) N) :=
    (Finset.range N).image fun k ↦ ⟨_, hmem k⟩ with hs
  -- the matrices of nonzero weight are the `(1 k; 0 N)` with `0 ≤ k < N`
  have hsub : (Function.support fun M : traceDetFiber (Fin 2) ((N : ℤ) + 1) N ↦
      if M.1 0 0 = 1 ∧ M.1 1 0 = 0 then weight !![1, M.1 0 1; 0, M.1 1 1] else 0) ⊆ s := by
    intro M hM
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hM
    obtain ⟨⟨ha, hc⟩, hne⟩ := hM
    obtain ⟨htr, -⟩ := mem_traceDetFiber_fin_two.mp M.2
    rw [weight_upperTriangular _ _ _ one_pos (by omega)] at hne
    have hb : 0 ≤ M.1 0 1 ∧ M.1 0 1 < N := by split_ifs at hne <;> omega
    refine Finset.mem_image.mpr ⟨(M.1 0 1).toNat, Finset.mem_range.mpr (by omega),
      Subtype.ext (Eq.trans ?_ (eta_fin_two M.1).symm)⟩
    simp only [Int.toNat_of_nonneg (show 0 ≤ M.1 0 1 by omega), ha, hc,
      EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
    omega
  rw [finsum_eq_sum_of_support_subset _ hsub, hs, Finset.sum_image fun k _ k' _ h ↦ by
    simpa using congrArg (fun M : traceDetFiber (Fin 2) ((N : ℤ) + 1) N ↦ M.1 0 1) h]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, and_self,
    ite_true]
  rw [sum_range_weight_upperTriangular N (by omega)]
  simp

/-! ### Positive trace -/

/-- The fibre of trace `a + (a + k)` and determinant `a (a + k)`, for `a = m + 1 > 0`, sums to
`12 k`, or to `2` when `k = 0`. -/
private theorem finsum_weight_traceDetFiber_add_mul_add (k m : ℕ) :
    ∑ᶠ M : traceDetFiber (Fin 2) (((m : ℤ) + 1) + (((m : ℤ) + 1) + k))
        (((m : ℤ) + 1) * (((m : ℤ) + 1) + k)), weight M.1 =
      if k = 0 then 2 else 12 * (k : ℤ) := by
  induction m with
  | zero =>
    rw [finsum_weight_traceDetFiber_of_lt]
    · push_cast
      split_ifs <;> omega
    · push_cast; omega
    · push_cast; omega
  | succ m ih =>
    -- the fibre at `m + 1` is the translate by `1` of the fibre at `m`
    have ht : ((((m + 1 : ℕ) : ℤ) + 1) + ((((m + 1 : ℕ) : ℤ) + 1) + k)) =
        (((m : ℤ) + 1) + (((m : ℤ) + 1) + k)) + 2 := by push_cast; ring
    have hn : ((((m + 1 : ℕ) : ℤ) + 1) * ((((m + 1 : ℕ) : ℤ) + 1) + k)) =
        ((m : ℤ) + 1) * (((m : ℤ) + 1) + k) + (((m : ℤ) + 1) + (((m : ℤ) + 1) + k)) +
          1 := by
      push_cast
      ring
    rw [ht, hn, finsum_weight_traceDetFiber_add_two (by positivity), ih]

/-- **The split hyperbolic fibres.** If `a ≠ d` are positive, then the weights of the integral
matrices of trace `a + d` and determinant `a d` sum to `12 |d - a|`: the coefficients of Popa and
Zagier's explicit element sum to `|d - a|` over these matrices. -/
theorem finsum_weight_traceDetFiber_add_mul_eq_twelve_mul_abs_sub {a d : ℤ} (ha : 0 < a)
    (hd : 0 < d) (had : a ≠ d) :
    ∑ᶠ M : traceDetFiber (Fin 2) (a + d) (a * d), weight M.1 = 12 * |d - a| := by
  wlog h : a < d generalizing a d
  · rw [add_comm, mul_comm, abs_sub_comm]
    exact this hd ha had.symm (by omega)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ a - 1 by omega)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d - a by omega)
  obtain rfl : a = (m : ℤ) + 1 := by omega
  obtain rfl : d = (m : ℤ) + 1 + k := by omega
  rw [finsum_weight_traceDetFiber_add_mul_add k m, ite_eq_right (by omega), add_sub_cancel_left,
    abs_of_nonneg (by positivity)]

/-- **The parabolic fibres.** If `a > 0`, then the weights of the integral matrices of trace `2 a`
and determinant `a²` sum to `2`: the coefficients of Popa and Zagier's explicit element sum to
`1/6` over these matrices, which is the coefficient of the scalar matrix `a • 1`. -/
theorem finsum_weight_traceDetFiber_two_mul_sq_eq_two {a : ℤ} (ha : 0 < a) :
    ∑ᶠ M : traceDetFiber (Fin 2) (2 * a) (a ^ 2), weight M.1 = 2 := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ a - 1 by omega)
  obtain rfl : a = (m : ℤ) + 1 := by omega
  have := finsum_weight_traceDetFiber_add_mul_add 0 m
  rw [Nat.cast_zero, add_zero, ← two_mul, ← sq, ite_eq_left rfl] at this
  exact this

/-- **The non-square fibres.** If `t² - 4 n ≥ 0` is not a square, then the weights of the
integral matrices of trace `t` and determinant `n` sum to zero. -/
theorem finsum_weight_traceDetFiber_eq_zero_of_not_isSquare (hD : 4 * n ≤ t ^ 2)
    (hsq : ¬IsSquare (t ^ 2 - 4 * n)) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = 0 := by
  induction hk : n.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
  rcases le_or_gt n 0 with hn | hn
  · exact finsum_weight_traceDetFiber_of_nonpos hn
  rcases lt_or_gt_of_ne (show t ≠ 0 by rintro rfl; omega) with ht | ht
  · exact finsum_weight_traceDetFiber_eq_zero_of_neg ht hD
  rcases lt_or_ge n t with hnt | hnt
  · -- the fibre `(n + 1, n)` has the square discriminant `(n - 1)²`
    rw [finsum_weight_traceDetFiber_of_lt hn hnt, ite_eq_right]
    rintro rfl
    exact hsq ⟨n - 1, by ring⟩
  -- translate downwards to the fibre `(t - 2, n - t + 1)`, of smaller positive determinant
  have hpos : 0 < n - t + 1 := by omega
  have hstep := finsum_weight_traceDetFiber_add_two (t := t - 2) hpos
  rw [sub_add_cancel, show n - t + 1 + (t - 2) + 1 = n by ring] at hstep
  rw [hstep]
  have ht₂ : 2 ≤ t := by nlinarith
  have hD' : (t - 2) ^ 2 - 4 * (n - t + 1) = t ^ 2 - 4 * n := by ring
  exact ih _ (by omega) (by nlinarith) (hD' ▸ hsq) rfl

end PopaZagier

end TauCeti
