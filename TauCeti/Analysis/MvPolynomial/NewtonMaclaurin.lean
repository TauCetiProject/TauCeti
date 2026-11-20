/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.FieldTheory.IsRealClosed.Real
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.FieldTheory.RealClosure.AbstractRolle
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# Newton's and Maclaurin's inequalities

For a multiset `s` of `n` real numbers, let `σ_k = s.esymm k` be its `k`-th elementary symmetric
function and `S_k = σ_k / binom(n, k)` the corresponding elementary symmetric mean, so that
`S_0 = 1`, `S_1` is the arithmetic mean and, for `s` nonnegative, `S_n` is the `n`-th power of the
geometric mean. This file proves:

* **Newton's inequalities** `S_k S_{k+2} ≤ S_{k+1}²`, for every real `s` and every `k`
  (`Multiset.esymm_div_choose_mul_esymm_div_choose_le_sq`). No sign condition is needed. For
  `k + 2 > n` the left side vanishes.
* **Maclaurin's inequalities** `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l`, when
  `σ_1, …, σ_l > 0` (`Multiset.esymm_div_choose_rpow_le_rpow`), in the equivalent form
  `S_l^k ≤ S_k^l` for `k ≤ l` (`Multiset.esymm_div_choose_pow_le_pow`). For the vector of
  values of `s` this positivity hypothesis says that the vector lies in the cone
  `Γ_l = {λ | σ_1(λ) > 0, …, σ_l(λ) > 0}` of the theory of Hessian equations. Off this cone
  Maclaurin's inequalities fail: for `s = {-1, -1, -1}`, `S_1 = -1 < 1 = S_2^{1/2}`.
* Maclaurin's inequalities for nonnegative reals
  (`Multiset.esymm_div_choose_rpow_le_rpow_of_nonneg`): the closed nonnegative orthant lies in
  the closure of the cone, and on its boundary part `σ_l` vanishes.

Through `MvPolynomial.aeval_esymm_eq_multiset_esymm`, these apply to the values
`MvPolynomial.eval μ (MvPolynomial.esymm σ ℝ k)` of the elementary symmetric polynomials at a
vector `μ : σ → ℝ`, with `s = Finset.univ.val.map μ`.

The proof of Newton's inequalities is the classical one through Rolle's theorem. The polynomial
`∏_{x ∈ s} (X + x) = ∑_j σ_j X^{n - j}` splits over `ℝ`; differentiating it `n - k - 2` times,
reflecting the result at degree `k + 2` and differentiating `k` more times gives the quadratic
`(n!/2) S_{k+2} X² + n! S_{k+1} X + (n!/2) S_k`, and each step preserves splitting
(`TauCeti.PolynomialRolle.splits_iterate_derivative`, `Polynomial.Splits.reflect`). A split
real quadratic has a nonnegative discriminant, which is Newton's inequality. Maclaurin's
inequalities follow from Newton's by induction: on the cone, the sequence `S_0 = 1, S_1, …, S_l`
is positive and log-concave.

## References

* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd edition, Cambridge University
  Press, 1952, §2.22 (Theorems 51 and 52).
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2, Amer. Math. Soc., 2005, 283–309,
  Lemma 2.6, Proposition 2.7 and Corollary 2.8.
-/

public section

open Polynomial
open scoped Nat

namespace Multiset

variable (s : Multiset ℝ)

/-- The quadratic of the proof of Newton's inequality at the index `k`: the polynomial
`∏_{x ∈ s} (X + x)` differentiated `card s - k - 2` times, reflected at degree `k + 2` and
differentiated `k` more times. -/
private noncomputable def newtonQuadratic (k : ℕ) : ℝ[X] :=
  derivative^[k] ((derivative^[card s - k - 2] (s.map fun r ↦ X + C r).prod).reflect (k + 2))

private lemma natDegree_iterate_derivative_prod_X_add_C_le (k : ℕ) :
    (derivative^[card s - k - 2] (s.map fun r ↦ X + C r).prod).natDegree ≤ k + 2 := by
  have : ((s.map fun r ↦ X + C r).prod).natDegree ≤ card s :=
    (natDegree_multiset_prod_le _).trans_eq (by simp)
  exact (natDegree_iterate_derivative _ _).trans (by omega)

private lemma splits_newtonQuadratic (k : ℕ) : (s.newtonQuadratic k).Splits := by
  have hrolle := TauCeti.RealClosure.polynomialRolle_of_isRealClosed (R := ℝ)
  have hprod : (s.map fun r ↦ X + C r).prod.Splits :=
    .multisetProd fun q hq ↦ by
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hq
      exact .X_add_C r
  exact hrolle.splits_iterate_derivative ((hrolle.splits_iterate_derivative hprod _).reflect
    (s.natDegree_iterate_derivative_prod_X_add_C_le k)) k

/-- The combinatorial identity behind the coefficients of `newtonQuadratic`: for `m ≤ 2` and
`n = k + 2 + a`, `m! (2 - m)! binom(n, k + m)` times the two descending factorials produced by
the derivatives is `n!`. -/
private lemma factorial_mul_choose_mul_descFactorial {k a m : ℕ} (hm : m ≤ 2) :
    m ! * (2 - m)! * (k + 2 + a).choose (k + m) * (m + k).descFactorial k *
      (2 - m + a).descFactorial a = (k + 2 + a)! := by
  have h₁ := Nat.factorial_mul_descFactorial (n := m + k) (k := k) (by omega)
  have h₂ := Nat.factorial_mul_descFactorial (n := 2 - m + a) (k := a) (by omega)
  have h₃ := Nat.choose_mul_factorial_mul_factorial (n := k + 2 + a) (k := k + m) (by omega)
  rw [Nat.add_sub_cancel] at h₁
  rw [Nat.add_sub_cancel] at h₂
  rw [show k + 2 + a - (k + m) = 2 - m + a by omega, add_comm k m] at h₃
  rw [← h₃, ← h₁, ← h₂, add_comm k m]
  ring

/-- The coefficients of `newtonQuadratic` are, up to explicit positive factors, the elementary
symmetric functions of indices `k`, `k + 1` and `k + 2`. -/
private lemma coeff_newtonQuadratic {k a : ℕ} (hn : card s = k + 2 + a) {m : ℕ} (hm : m ≤ 2) :
    ((m ! * (2 - m)! * (card s).choose (k + m) : ℕ) : ℝ) * (s.newtonQuadratic k).coeff m =
      (card s)! * s.esymm (k + m) := by
  have ha : card s - k - 2 = a := by omega
  rw [newtonQuadratic, ha, coeff_iterate_derivative, coeff_reflect,
    revAt_le (by omega), coeff_iterate_derivative,
    prod_X_add_C_coeff _ (by omega), show card s - (k + 2 - (m + k) + a) = k + m by omega,
    show k + 2 - (m + k) = 2 - m by omega, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc,
    ← mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, hn, factorial_mul_choose_mul_descFactorial hm]

/-- Newton's inequality in the case `k + 2 ≤ card s`, where all binomial coefficients involved are
positive. -/
private lemma esymm_div_choose_mul_esymm_div_choose_le_sq_of_le {k : ℕ} (hk : k + 2 ≤ card s) :
    s.esymm k / (card s).choose k * (s.esymm (k + 2) / (card s).choose (k + 2)) ≤
      (s.esymm (k + 1) / (card s).choose (k + 1)) ^ 2 := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hk
  set q := s.newtonQuadratic k
  have hq : q = C (q.coeff 2) * X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
    have hdeg : q.natDegree < 3 :=
      (natDegree_iterate_derivative _ _).trans_lt (by
        have := natDegree_reflect_le_of_natDegree_le
          (s.natDegree_iterate_derivative_prod_X_add_C_le k)
        omega)
    conv_lhs => rw [as_sum_range' q 3 hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← C_mul_X_pow_eq_monomial]
    ring
  have hdisc : 0 ≤ discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) :=
    (splits_quadratic_iff_isSquare.mp (hq ▸ s.splits_newtonQuadratic k)).nonneg
  have h₀ := s.coeff_newtonQuadratic ha (m := 0) (by norm_num)
  have h₁ := s.coeff_newtonQuadratic ha (m := 1) (by norm_num)
  have h₂ := s.coeff_newtonQuadratic ha (m := 2) (by norm_num)
  have hc (j : ℕ) (hj : j ≤ card s) : (0 : ℝ) < (card s).choose j := by
    exact_mod_cast Nat.choose_pos hj
  have hc₀ := hc k (by omega)
  have hc₁ := hc (k + 1) (by omega)
  have hc₂ := hc (k + 2) (by omega)
  have hfact : (0 : ℝ) < (card s)! := by exact_mod_cast Nat.factorial_pos _
  norm_num at h₀ h₁ h₂
  have e₀ : q.coeff 0 = (card s)! * s.esymm k / (2 * (card s).choose k) := by
    rw [eq_div_iff (by positivity)]; linear_combination h₀
  have e₁ : q.coeff 1 = (card s)! * s.esymm (k + 1) / (card s).choose (k + 1) := by
    rw [eq_div_iff (by positivity)]; linear_combination h₁
  have e₂ : q.coeff 2 = (card s)! * s.esymm (k + 2) / (2 * (card s).choose (k + 2)) := by
    rw [eq_div_iff (by positivity)]; linear_combination h₂
  -- The discriminant of the quadratic is `(n!)² (S_{k+1}² - S_k S_{k+2})`.
  have key : 0 ≤ ((card s)! : ℝ) ^ 2 * ((s.esymm (k + 1) / (card s).choose (k + 1)) ^ 2 -
      s.esymm k / (card s).choose k * (s.esymm (k + 2) / (card s).choose (k + 2))) := by
    rw [discrim, e₀, e₁, e₂] at hdisc
    convert hdisc using 1
    field_simp
    ring
  nlinarith [(mul_nonneg_iff_of_pos_left (by positivity)).mp key]

/-- **Newton's inequalities**: for a multiset `s` of real numbers and every `k`, the elementary
symmetric means `S_j = σ_j(s) / binom(card s, j)` satisfy `S_k S_{k+2} ≤ S_{k+1}²`. No sign
condition on the elements of `s` is needed. -/
theorem esymm_div_choose_mul_esymm_div_choose_le_sq (k : ℕ) :
    s.esymm k / (card s).choose k * (s.esymm (k + 2) / (card s).choose (k + 2)) ≤
      (s.esymm (k + 1) / (card s).choose (k + 1)) ^ 2 := by
  rcases le_or_gt (k + 2) (card s) with hk | hk
  · exact s.esymm_div_choose_mul_esymm_div_choose_le_sq_of_le hk
  · rw [esymm_of_card_lt hk, zero_div, mul_zero]
    positivity

/-- On the cone `σ_1, …, σ_l > 0`, the elementary symmetric means `S_1, …, S_l` are positive. -/
private lemma esymm_div_choose_pos {l : ℕ} (hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j) {j : ℕ}
    (hj : j ≤ l) : 0 < s.esymm j / (card s).choose j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj₀
  · simp
  have hσ := hpos j (Finset.mem_Icc.mpr ⟨hj₀, hj⟩)
  have hjn : j ≤ card s := by
    by_contra h
    exact hσ.ne' (esymm_of_card_lt (not_le.mp h))
  exact div_pos hσ (by exact_mod_cast Nat.choose_pos hjn)

/-- Consecutive Maclaurin inequality `S_{j+1}^j ≤ S_j^{j+1}` on the cone `σ_1, …, σ_l > 0`, for
`j + 1 ≤ l`. -/
private lemma esymm_div_choose_pow_le_pow_succ {l : ℕ}
    (hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j) {j : ℕ} (hj : j + 1 ≤ l) :
    (s.esymm (j + 1) / (card s).choose (j + 1)) ^ j ≤
      (s.esymm j / (card s).choose j) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    set S : ℕ → ℝ := fun i ↦ s.esymm i / (card s).choose i
    have h₀ := s.esymm_div_choose_pos hpos (j := j) (by omega)
    have h₁ := s.esymm_div_choose_pos hpos (j := j + 1) (by omega)
    have h₂ := s.esymm_div_choose_pos hpos (j := j + 2) (by omega)
    have hnewton : S j * S (j + 2) ≤ S (j + 1) ^ 2 :=
      s.esymm_div_choose_mul_esymm_div_choose_le_sq j
    -- Raise Newton's inequality to the power `j + 1` and combine it with the previous step.
    have hstep : S (j + 1) ^ j * S (j + 2) ^ (j + 1) ≤ S (j + 1) ^ j * S (j + 1) ^ (j + 2) :=
      calc S (j + 1) ^ j * S (j + 2) ^ (j + 1)
          ≤ S j ^ (j + 1) * S (j + 2) ^ (j + 1) := by gcongr; exact ih (by omega)
        _ = (S j * S (j + 2)) ^ (j + 1) := (mul_pow _ _ _).symm
        _ ≤ (S (j + 1) ^ 2) ^ (j + 1) := by gcongr
        _ = S (j + 1) ^ j * S (j + 1) ^ (j + 2) := by ring
    exact le_of_mul_le_mul_left hstep (by positivity)

/-- **Maclaurin's inequalities**, power form: if `σ_1(s), …, σ_l(s) > 0`, then the elementary
symmetric means `S_j = σ_j(s) / binom(card s, j)` satisfy `S_l^k ≤ S_k^l` for every `k ≤ l`. -/
theorem esymm_div_choose_pow_le_pow {k l : ℕ} (hkl : k ≤ l)
    (hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j) :
    (s.esymm l / (card s).choose l) ^ k ≤ (s.esymm k / (card s).choose k) ^ l := by
  set S : ℕ → ℝ := fun i ↦ s.esymm i / (card s).choose i
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih =>
    have hpos' : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j := fun j hj ↦
      hpos j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans
        (Nat.le_succ l)⟩)
    have hk₀ := s.esymm_div_choose_pos hpos (j := k) (by omega)
    have hl₀ := s.esymm_div_choose_pos hpos (j := l) (by omega)
    have hl₁ := s.esymm_div_choose_pos hpos (j := l + 1) le_rfl
    have hcons : S (l + 1) ^ l ≤ S l ^ (l + 1) :=
      s.esymm_div_choose_pow_le_pow_succ hpos le_rfl
    -- Both sides of the goal are nonnegative; compare their `l`-th powers.
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : l ≠ 0)).mp ?_
    calc (S (l + 1) ^ k) ^ l = (S (l + 1) ^ l) ^ k := by ring
      _ ≤ (S l ^ (l + 1)) ^ k := by gcongr
      _ = (S l ^ k) ^ (l + 1) := by ring
      _ ≤ (S k ^ l) ^ (l + 1) := by gcongr; exact ih hpos'
      _ = (S k ^ (l + 1)) ^ l := by ring

/-- **Maclaurin's inequalities**: if `σ_1(s), …, σ_l(s) > 0`, then the elementary symmetric means
`S_j = σ_j(s) / binom(card s, j)` satisfy `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l`. -/
theorem esymm_div_choose_rpow_le_rpow {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    (hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j) :
    (s.esymm l / (card s).choose l) ^ (1 / (l : ℝ)) ≤
      (s.esymm k / (card s).choose k) ^ (1 / (k : ℝ)) := by
  have hk₀ := s.esymm_div_choose_pos hpos (j := k) hkl
  have hl₀ := s.esymm_div_choose_pos hpos (j := l) le_rfl
  have hpow := s.esymm_div_choose_pow_le_pow hkl hpos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hk.trans hkl
  -- Take the `(k l)`-th root of `S_l^k ≤ S_k^l`.
  have hroot := Real.rpow_le_rpow (by positivity) hpow (by positivity : 0 ≤ 1 / ((k : ℝ) * l))
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hl₀.le,
    ← Real.rpow_mul hk₀.le] at hroot
  convert hroot using 2 <;> field_simp

/-- **Maclaurin's inequalities** for nonnegative reals: if every element of `s` is nonnegative,
then the elementary symmetric means `S_j = σ_j(s) / binom(card s, j)` satisfy
`S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l`. At `k = 1` and `l = card s` this is the inequality of
arithmetic and geometric means. -/
theorem esymm_div_choose_rpow_le_rpow_of_nonneg {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    (hs : ∀ a ∈ s, 0 ≤ a) :
    (s.esymm l / (card s).choose l) ^ (1 / (l : ℝ)) ≤
      (s.esymm k / (card s).choose k) ^ (1 / (k : ℝ)) := by
  by_cases hpos : ∀ j ∈ Finset.Icc 1 l, 0 < s.esymm j
  · exact s.esymm_div_choose_rpow_le_rpow hk hkl hpos
  push Not at hpos
  obtain ⟨j, hj, hj₀⟩ := hpos
  have hl : s.esymm l = 0 :=
    esymm_eq_zero_of_le hs (hj₀.antisymm (esymm_nonneg hs j)) (Finset.mem_Icc.mp hj).2
  have hlR : (1 / (l : ℝ)) ≠ 0 := one_div_ne_zero (by have := hk.trans hkl; positivity)
  rw [hl, zero_div, Real.zero_rpow hlR]
  exact Real.rpow_nonneg (div_nonneg (esymm_nonneg hs k) (Nat.cast_nonneg _)) _

end Multiset
