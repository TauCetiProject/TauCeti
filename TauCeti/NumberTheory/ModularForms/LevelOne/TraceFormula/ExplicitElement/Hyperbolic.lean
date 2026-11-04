/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.ClassNumber
import Mathlib.Tactic.LinearCombination

/-!
# The hyperbolic trace fibres of Popa–Zagier's element

Let `TauCeti.PopaZagier.weight M` be twelve times the coefficient of the integral matrix `M` in
Popa and Zagier's explicit Hecke element, their eq. (15). This file evaluates the sum of these
weights over the matrices of trace `t` and determinant `n` when the discriminant `t² - 4 n` is
positive. Together with the elliptic fibres
(`TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber`) and the
repeated-root fibres (`TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_zero`), this
evaluates every trace fibre of positive determinant:

* if `t² - 4 n = u²` with `u > 0` and `n > 0`, the weights sum to `12 u` for `t > 0` and to `0` for
  `t < 0`;
* if `t² - 4 n > 0` is not a square, the weights sum to `0`.

Popa and Zagier's coefficients are a twelfth of the weights, so in the split case the two fibres
of traces `±t` together carry coefficient `u`. Weighted by the binary-form trace `P_{w+2}(t, n)`,
the split fibres give the divisor-sum terms of the trace formula, and the nonsplit fibres give
nothing.

## Main results

* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_sq`: the split hyperbolic fibres.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_not_isSquare`: the nonsplit hyperbolic
  fibres.

## Proof

Translation `M ↦ M + 1` preserves the sum over a fibre of positive determinant
(`TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_two`) and shifts both eigenvalues by `1`.
If `t < 0`, translating upwards reaches a fibre of nonpositive determinant, where every weight
vanishes. If `t > 0`, translating downwards reaches a fibre with `n + 1 ≤ t`, that is, with an
eigenvalue in `(0, 1]`. There only the sum `T₁` contributes, and only through the matrices
`(1 b; 0 n)` with `0 ≤ b < n`, which occur exactly when `t = n + 1`, that is when the
eigenvalues are `1` and `n`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, eq. (15).
-/

public section

open Matrix

namespace TauCeti.PopaZagier

variable {t n : ℤ}

/-! ### Fibres of nonpositive determinant and of negative trace -/

/-- Every weight vanishes on a fibre of nonpositive determinant. -/
private theorem finsum_weight_traceDetFiber_of_nonpos (hn : n ≤ 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun M ↦ by
    by_contra hw
    have := det_pos_of_weight_ne_zero hw
    rw [(mem_traceDetFiber.mp M.2).2] at this
    omega

/-- At positive discriminant, the weights of a fibre of negative trace sum to zero. -/
private theorem finsum_weight_traceDetFiber_of_neg (ht : t < 0) (hD : 0 < t ^ 2 - 4 * n) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = 0 := by
  -- translate upwards until the determinant is nonpositive
  induction hk : (-t).toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
    rcases le_or_gt n 0 with hn | hn
    · exact finsum_weight_traceDetFiber_of_nonpos hn
    rw [← finsum_weight_traceDetFiber_add_two hn]
    rcases le_or_gt (n + t + 1) 0 with hn' | hn'
    · exact finsum_weight_traceDetFiber_of_nonpos hn'
    -- both eigenvalues stay negative: a positive determinant forbids a trace `0` or `1`
    have ht' : t + 2 < 0 := by
      by_contra! h
      have : t + 2 = 0 ∨ t + 2 = 1 := by omega
      rcases this with h | h <;> nlinarith
    exact ih _ (by omega) ht' (by linear_combination hD) rfl

/-! ### Fibres with an eigenvalue in `(0, 1]` -/

/-- At positive discriminant, no matrix has nonzero weight in `T₃` or `T₄`: their first lines
force a negative discriminant `(a - d)² + 4 b c`. -/
private theorem weight₃_eq_zero_and_weight₄_eq_zero {a b c d : ℤ}
    (hD : 0 < (a - d) ^ 2 + 4 * b * c) : weight₃ a b c d = 0 ∧ weight₄ a b c d = 0 := by
  constructor
  · unfold weight₃
    split_ifs with h
    · by_contra hw
      obtain ⟨h₁, h₂, h₃⟩ := le_of_chainWeight₄_ne_zero hw
      nlinarith [mul_nonneg h₁ (by omega : (0 : ℤ) ≤ c - (a - d)),
        mul_nonneg h.2.le (by omega : (0 : ℤ) ≤ c - (a - d)),
        mul_nonneg h.2.le (by omega : (0 : ℤ) ≤ -b - c)]
    · rfl
  · unfold weight₄
    split_ifs with h
    · by_contra hw
      obtain ⟨h₁, h₂, h₃⟩ := le_of_chainWeight₄_ne_zero hw
      nlinarith
    · rfl

/-- If `n + 1 ≤ t`, no matrix of trace `t` and determinant `n` has nonzero weight in `T₂`. -/
private theorem weight₂_eq_zero {a b c d : ℤ} (h : a * d - b * c + 1 ≤ a + d) :
    weight₂ a b c d = 0 := by
  unfold weight₂
  split_ifs with hbd
  · by_contra hw
    obtain ⟨h₁, h₂⟩ := le_of_chainWeight₃_ne_zero hw
    -- `-b c ≥ (1 - d) c ≥ (1 - d) (a - d)` forces `n - t + 1 ≥ (d - 1)² > 0`
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -b - (1 - d)) (by omega : (0 : ℤ) ≤ c),
      mul_nonneg (by omega : (0 : ℤ) ≤ 1 - d) (by omega : (0 : ℤ) ≤ c - (a - d))]
  · rfl

/-- If `0 < n` and `n + 1 ≤ t`, a matrix of trace `t` and determinant `n` with nonzero weight in
`T₁` is `(1 b; 0 n)`, and then `t = n + 1`. -/
private theorem eq_of_weight₁_ne_zero {a b c d : ℤ} (hn : 0 < a * d - b * c)
    (h : a * d - b * c + 1 ≤ a + d) (hw : weight₁ a b c d ≠ 0) :
    c = 0 ∧ a = 1 ∧ d = a * d - b * c ∧ a + d = a * d - b * c + 1 := by
  unfold weight₁ at hw
  split_ifs at hw with hca
  · obtain ⟨h₁, h₂⟩ := le_of_chainWeight₃_ne_zero hw
    obtain ⟨hc, hca⟩ := hca
    rcases hc.lt_or_eq with hc | rfl
    · -- `c > 0` is impossible
      exfalso
      rcases le_or_gt 0 b with hb | hb
      · -- here `n ≥ a² - a + d`, so `(a - 1)² ≤ 0` with `a ≥ 2`
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ d - a - b) hc.le,
          mul_nonneg (by omega : (0 : ℤ) ≤ d - a) (by omega : (0 : ℤ) ≤ a - 1 - c)]
      · -- here `-b c = (a - 1) (1 - d) + (n - t + 1) > 0` forces `d ≤ 0`, so `a ≤ c`
        have hd : d ≤ 0 := by
          by_contra! hd
          nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ d - 1),
            mul_pos (by omega : (0 : ℤ) < -b) hc]
        omega
    · -- `c = 0`: the diagonal entries are positive with `(a - 1) (d - 1) = n - t + 1 ≤ 0`
      simp only [mul_zero, sub_zero] at hn h
      have hd : 0 < d := pos_of_mul_pos_right hn hca.le
      have h0 : (a - 1) * (d - 1) = 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ d - 1)]
      obtain rfl : a = 1 := by rcases mul_eq_zero.mp h0 with h0 | h0 <;> omega
      exact ⟨rfl, rfl, by ring, by ring⟩
  · exact absurd rfl hw

/-- If `0 < n`, `n + 1 ≤ t` and `t² - 4 n > 0`, the matrices of trace `t` and determinant `n`
of nonzero weight are the matrices `(1 b; 0 n)`, and they only occur if `t = n + 1`. -/
private theorem eq_of_weight_ne_zero (hn : 0 < n) (h : n + 1 ≤ t) (hD : 0 < t ^ 2 - 4 * n)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ traceDetFiber (Fin 2) t n) (hw : weight M ≠ 0) :
    t = n + 1 ∧ M = !![1, M 0 1; 0, n] := by
  obtain ⟨ht, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
  have hD' : (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = t ^ 2 - 4 * n := by
    rw [← ht, ← hdet]
    ring
  obtain ⟨h₃, h₄⟩ := weight₃_eq_zero_and_weight₄_eq_zero (hD' ▸ hD)
  have h' : M 0 0 * M 1 1 - M 0 1 * M 1 0 + 1 ≤ M 0 0 + M 1 1 := by rw [hdet, ht]; exact h
  unfold weight at hw
  rw [weight₂_eq_zero h', h₃, h₄, sub_zero, sub_zero, sub_zero] at hw
  obtain ⟨hc, ha, hd, ht'⟩ := eq_of_weight₁_ne_zero (hdet ▸ hn) h' hw
  rw [hdet] at hd ht'
  refine ⟨ht ▸ ht', ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]

/-- For `n > 0`, the weight of `(1 b; 0 n)` is its weight in `T₁`. -/
private theorem weight_upperTriangular (hn : 0 < n) (b : ℤ) :
    weight !![1, b; 0, n] = chainWeight₃ (1 - n) (-b) 0 := by
  simp [weight, weight₁, weight₂, weight₃, weight₄, hn.not_ge]

/-- The weights `6, 12, …, 12, 6` of the matrices `(1 b; 0 m + 1)`, `0 ≤ b ≤ m`, in `T₁`. -/
private theorem sum_chainWeight₃_Icc {m : ℤ} (hm : 0 < m) :
    ∑ b ∈ Finset.Icc 0 m, chainWeight₃ (-m) (-b) 0 = 12 * m := by
  have key : ∀ b ∈ Finset.Icc 0 m, chainWeight₃ (-m) (-b) 0 =
      12 - (if b = 0 then 6 else 0) - (if b = m then 6 else 0) := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    unfold chainWeight₃
    split_ifs <;> omega
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_const, Int.card_Icc]
  simp only [Finset.mem_Icc, le_refl, hm.le, and_self, ite_true, nsmul_eq_mul]
  rw [Int.toNat_of_nonneg (by omega)]
  ring

/-- If `0 < n`, `n + 1 ≤ t` and `t² - 4 n > 0`, the weights of the matrices of trace `t` and
determinant `n` sum to `12 (n - 1)` if `t = n + 1`, and to `0` otherwise. -/
private theorem finsum_weight_traceDetFiber_of_le (hn : 0 < n) (h : n + 1 ≤ t)
    (hD : 0 < t ^ 2 - 4 * n) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = if t = n + 1 then 12 * (n - 1) else 0 := by
  classical
  split_ifs with ht
  · subst ht
    have hn1 : 0 < n - 1 := by nlinarith
    let φ (b : ℤ) : traceDetFiber (Fin 2) (n + 1) n :=
      ⟨!![1, b; 0, n], mem_traceDetFiber_fin_two.mpr ⟨by simp [add_comm], by simp⟩⟩
    have hφ : Function.Injective φ := fun b b' hb ↦ by
      simpa [φ] using congrFun (congrFun (congrArg Subtype.val hb) 0) 1
    have hsub : (Function.support fun M : traceDetFiber (Fin 2) (n + 1) n ↦ weight M.1) ⊆
        (Finset.Icc 0 (n - 1)).image φ := by
      intro M hM
      obtain ⟨-, hM'⟩ := eq_of_weight_ne_zero hn h hD M.2 hM
      have hw : chainWeight₃ (1 - n) (-M.1 0 1) 0 ≠ 0 := by
        rw [← weight_upperTriangular hn, ← hM']
        exact hM
      obtain ⟨h₁, h₂⟩ := le_of_chainWeight₃_ne_zero hw
      refine Finset.mem_image.mpr ⟨M.1 0 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      exact Subtype.ext hM'.symm
    rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_image fun b _ b' _ hb ↦ hφ hb,
      ← sum_chainWeight₃_Icc hn1]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [weight_upperTriangular hn, show 1 - n = -(n - 1) by ring]
  · refine finsum_eq_zero_of_forall_eq_zero fun M ↦ ?_
    by_contra hw
    exact ht (eq_of_weight_ne_zero hn h hD M.2 hw).1

/-- At positive trace, determinant and discriminant, the sum of the weights over a fibre equals
the sum over a fibre with the same discriminant and an eigenvalue in `(0, 1]`. -/
private theorem exists_finsum_weight_traceDetFiber_eq (ht : 0 < t) (hn : 0 < n)
    (hD : 0 < t ^ 2 - 4 * n) :
    ∃ t' n' : ℤ, t' ^ 2 - 4 * n' = t ^ 2 - 4 * n ∧ 0 < n' ∧ n' + 1 ≤ t' ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 =
        ∑ᶠ M : traceDetFiber (Fin 2) t' n', weight M.1 := by
  -- translate downwards while the determinant stays positive
  induction hk : t.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
    rcases le_or_gt (n + 1) t with h | h
    · exact ⟨t, n, rfl, hn, h, rfl⟩
    have hn' : 0 < n - t + 1 := by omega
    -- both eigenvalues stay positive: a positive determinant forbids a trace `-1` or `0`
    have ht' : 0 < t - 2 := by
      by_contra! h'
      have : t - 2 = -1 ∨ t - 2 = 0 := by omega
      rcases this with h' | h' <;> nlinarith
    have hstep := finsum_weight_traceDetFiber_add_two (t := t - 2) hn'
    rw [show t - 2 + 2 = t by ring, show n - t + 1 + (t - 2) + 1 = n by ring] at hstep
    obtain ⟨t', n', hD', hn'', h', e⟩ :=
      ih _ (by omega) ht' hn' (by linear_combination hD) rfl
    exact ⟨t', n', by linear_combination hD', hn'', h', hstep.trans e⟩

/-! ### The hyperbolic fibres -/

/-- **The split hyperbolic trace fibres of Popa–Zagier's element.** If `n > 0` and
`t² - 4 n = u²` with `u > 0`, the weights of the integral matrices of trace `t` and determinant
`n` sum to `12 u` if `t > 0`, and to `0` if `t < 0`. -/
theorem finsum_weight_traceDetFiber_of_discrim_eq_sq {u : ℤ} (hn : 0 < n) (hu : 0 < u)
    (h : t ^ 2 - 4 * n = u ^ 2) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = if 0 < t then 12 * u else 0 := by
  have hD : 0 < t ^ 2 - 4 * n := h ▸ pow_pos hu 2
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [ite_eq_right (by omega)]
    exact finsum_weight_traceDetFiber_of_neg ht hD
  · nlinarith
  rw [ite_eq_left ht]
  obtain ⟨t', n', hD', hn', h', e⟩ := exists_finsum_weight_traceDetFiber_eq ht hn hD
  rw [e, finsum_weight_traceDetFiber_of_le hn' h' (hD' ▸ hD)]
  split_ifs with ht'
  · -- the eigenvalues are `1` and `n'`, so `u = n' - 1`
    subst ht'
    have : (u - (n' - 1)) * (u + (n' - 1)) = 0 := by linear_combination -h - hD'
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [show u = n' - 1 by omega]
    · omega
  · -- otherwise `t'² - 4 n'` would be a square with roots `(t' ± u) / 2` on either side of `1`
    exfalso
    have hlt : n' + 1 < t' := lt_of_le_of_ne h' (Ne.symm ht')
    have hprod : (t' - u) * (t' + u) = 4 * n' := by linear_combination hD' + h
    have hpos : 0 < t' - u := by nlinarith
    have hone : t' - u = 1 := by nlinarith
    rw [hone, one_mul] at hprod
    omega

/-- **The nonsplit hyperbolic trace fibres of Popa–Zagier's element.** If `t² - 4 n > 0` is not a
square, the weights of the integral matrices of trace `t` and determinant `n` sum to `0`. -/
theorem finsum_weight_traceDetFiber_of_not_isSquare (hD : 0 < t ^ 2 - 4 * n)
    (h : ¬IsSquare (t ^ 2 - 4 * n)) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = 0 := by
  rcases le_or_gt n 0 with hn | hn
  · exact finsum_weight_traceDetFiber_of_nonpos hn
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exact finsum_weight_traceDetFiber_of_neg ht hD
  · nlinarith
  obtain ⟨t', n', hD', hn', h', e⟩ := exists_finsum_weight_traceDetFiber_eq ht hn hD
  rw [e, finsum_weight_traceDetFiber_of_le hn' h' (hD' ▸ hD)]
  split_ifs with ht'
  · subst ht'
    exact absurd ⟨n' - 1, by linear_combination -hD'⟩ h
  · rfl

end TauCeti.PopaZagier
