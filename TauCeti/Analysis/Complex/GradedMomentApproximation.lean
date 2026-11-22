/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Normed.Field.MomentBound

/-!
# Polynomial approximation of graded moments

Fix a real number `p > 1` and a finite graded family of complex numbers: in each degree
`0 ≤ i ≤ r` finitely many numbers `α i k`, all of absolute value `p ^ (i / 2)`. Their alternating
moments `∑ i, (-1) ^ i ∑ k, α i k ^ n` are the shape of the point counts `#X(𝔽_{pⁿ})` of a smooth
proper variety by the Grothendieck–Lefschetz trace formula and Deligne's purity theorem, the
numbers `α i k` being the Frobenius eigenvalues on `H^i`.

Suppose the moments are approximated by `P(pⁿ)` for a polynomial `P ∈ ℚ[T]`, with an error that is
`o(p ^ (s n / 2))` for a natural number `s`. Then, at and above the cutoff `s`,

* every odd degree `i ≥ s` is empty;
* in every even degree `i = 2 j ≥ s`, every `α i k` equals the positive real `p ^ j`, and the
  number of them is the coefficient of `T ^ j` in `P`;
* every coefficient of `T ^ j` in `P` with `2 j ≥ s` and `2 j > r` vanishes.

Nothing is asserted about degrees or coefficients below the cutoff, and no range is imposed on `s`.
This is `TauCeti.graded_polynomial_approximation`, the numerical step that turns approximate
polynomial point counts into the vanishing of odd cohomology and Tate-type Frobenius eigenvalues.

The proof regards the moments together with the terms `P_m (p ^ m) ^ n` of `P(pⁿ)` as the weighted
moments of one finite spectrum, with weights `(-1) ^ i` and `-P_m`. By the strict little-o root
bound `TauCeti.norm_lt_of_grouped_moment_isLittleO`, every root of absolute value at least
`p ^ (s / 2)` carries total weight zero. Roots of different degrees have different absolute
values, so only roots of one degree, and in even degree `2 j` the single polynomial root `p ^ j`,
can cancel: odd degrees have weights of one sign, and an even-degree root other than `p ^ j` has
nothing to cancel against.

## References

* Jeroen van den Bogaart, Bas Edixhoven, *Algebraic stacks whose number of points over finite
  fields is a polynomial*, in: Number fields and function fields, Progr. Math. 239 (2005),
  Lemma 4.1 and its proof, pp. 6–7, for `s ≤ r ≤ 2 s`.
* Jonas Bergström, Carel Faber, Sam Payne, *Polynomial point counts and odd cohomology vanishing
  on moduli spaces of stable curves*, Ann. of Math. 199 (2024), proof of Proposition 3.1.
-/

public section

namespace TauCeti

open Asymptotics Filter Finset Polynomial
open scoped Topology

/-- The real powers `p ^ (x / 2)` of a real number `p > 1` at distinct natural numbers `x` are
distinct. -/
private theorem eq_of_rpow_div_two_eq {p : ℝ} (hp : 1 < p) {x y : ℕ}
    (h : p ^ ((x : ℝ) / 2) = p ^ ((y : ℝ) / 2)) : x = y := by
  simpa using (Real.rpow_right_inj (zero_lt_one.trans hp) hp.ne').1 h

/-- The power `p ^ m` has absolute value `p ^ (2 m / 2)`, that of a number of degree `2 m`. -/
private theorem norm_ofReal_pow_eq_rpow {p : ℝ} (hp : 0 ≤ p) (m : ℕ) :
    ‖((p ^ m : ℝ) : ℂ)‖ = p ^ (((2 * m : ℕ) : ℝ) / 2) := by
  rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hp m), Nat.cast_mul, Nat.cast_two,
    mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_natCast]

/-- **Roots above the cutoff cancel.** If the alternating moments of a graded family `α` differ
from `P(pⁿ)` by `o(p ^ (s n / 2))`, then for every complex number `z` of absolute value at least
`p ^ (s / 2)` the signs `(-1) ^ i` of the indices with `α i k = z` add up to the coefficient
`P_m` of the power `p ^ m = z`, if any. No absolute values of the `α i k` are assumed. -/
private theorem sum_sum_ite_eq_sum_ite_of_tendsto {p : ℝ} (hp : 1 < p) {r s : ℕ}
    {b : Fin (r + 1) → ℕ} {α : (i : Fin (r + 1)) → Fin (b i) → ℂ} {P : ℚ[X]}
    (hlimit : Tendsto (fun n : ℕ ↦ ‖(∑ i : Fin (r + 1), (-1 : ℂ) ^ (i : ℕ) * ∑ k, α i k ^ n) -
        P.eval₂ (algebraMap ℚ ℂ) ((p ^ n : ℝ) : ℂ)‖ / p ^ ((s : ℝ) * n / 2)) atTop (𝓝 0))
    {z : ℂ} (hz : p ^ ((s : ℝ) / 2) ≤ ‖z‖) :
    (∑ i, ∑ k, if α i k = z then (-1 : ℂ) ^ (i : ℕ) else 0) =
      ∑ m ∈ P.support, if ((p ^ m : ℝ) : ℂ) = z then (P.coeff m : ℂ) else 0 := by
  classical
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  -- The combined spectrum: the roots `α i k` with weights `(-1) ^ i`, and the powers `p ^ m` with
  -- weights `-P_m`, whose weighted moments are the approximation errors.
  let root : (Σ i, Fin (b i)) ⊕ P.support → ℂ :=
    Sum.elim (fun x ↦ α x.1 x.2) fun m ↦ ((p ^ (m : ℕ) : ℝ) : ℂ)
  let wt : (Σ i, Fin (b i)) ⊕ P.support → ℂ :=
    Sum.elim (fun x ↦ (-1) ^ (x.1 : ℕ)) fun m ↦ -(P.coeff m : ℂ)
  have hmoment : ∀ n : ℕ, ∑ t, wt t * root t ^ n =
      (∑ i : Fin (r + 1), (-1 : ℂ) ^ (i : ℕ) * ∑ k, α i k ^ n) -
        P.eval₂ (algebraMap ℚ ℂ) ((p ^ n : ℝ) : ℂ) := fun n ↦ by
    simp only [Fintype.sum_sum_type, Fintype.sum_sigma, root, wt, Sum.elim_inl, Sum.elim_inr,
      mul_sum, eval₂_eq_sum, Polynomial.sum_def, ← sum_coe_sort P.support, neg_mul,
      sum_neg_distrib, ← sub_eq_add_neg, eq_ratCast]
    congr 1
    refine sum_congr rfl fun m _ ↦ ?_
    push_cast
    ring
  -- The error is `o(R ^ n)` for `R = p ^ (s / 2)`.
  have hR : 0 < p ^ ((s : ℝ) / 2) := Real.rpow_pos_of_pos (zero_lt_one.trans hp) _
  have ho : (fun n ↦ ∑ t, wt t * root t ^ n) =o[atTop] fun n ↦ (p ^ ((s : ℝ) / 2)) ^ n := by
    refine isLittleO_norm_left.1 ((isLittleO_iff_tendsto fun n h ↦ absurd h
      (pow_ne_zero n hR.ne')).2 ?_)
    convert hlimit using 3 with n
    · rw [hmoment]
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_div_right_comm]
  -- By the strict root bound, the total weight of `z` vanishes; split it over the two parts.
  have hzero : ∑ t with root t = z, wt t = 0 := by
    by_contra h
    obtain ⟨t, ht, -⟩ := exists_ne_zero_of_sum_ne_zero h
    exact (norm_lt_of_grouped_moment_isLittleO hR ho (j := t)
      (by rwa [(mem_filter.1 ht).2])).not_ge ((mem_filter.1 ht).2 ▸ hz)
  rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_sigma] at hzero
  rw [← sum_coe_sort P.support, ← add_neg_eq_zero, ← sum_neg_distrib]
  simpa [root, wt, apply_ite] using hzero

/-- In a graded family whose numbers in degree `i` have absolute value `p ^ (i / 2)`, only the
degree `i₀` contributes to the signed count of the indices carrying a number of degree `i₀`. -/
private theorem sum_sum_ite_eq_sum_ite_of_norm_eq {p : ℝ} (hp : 1 < p) {r : ℕ}
    {b : Fin (r + 1) → ℕ} {α : (i : Fin (r + 1)) → Fin (b i) → ℂ}
    (hweight : ∀ i k, ‖α i k‖ = p ^ ((i : ℝ) / 2)) (i₀ : Fin (r + 1)) {z : ℂ}
    (hz : ‖z‖ = p ^ ((i₀ : ℝ) / 2)) :
    (∑ i, ∑ k, if α i k = z then (-1 : ℂ) ^ (i : ℕ) else 0) =
      ∑ k, if α i₀ k = z then (-1 : ℂ) ^ (i₀ : ℕ) else 0 :=
  sum_eq_single i₀ (fun i _ hi ↦ sum_eq_zero fun k _ ↦ ite_eq_right fun h ↦ hi <| Fin.ext <|
    eq_of_rpow_div_two_eq hp (by rw [← hweight i k, h, hz])) (by simp)

/-- Among the powers `p ^ m`, `m` in the support of `P`, only `p ^ j` equals `p ^ j`, so the
coefficients carried by the powers equal to `p ^ j` add up to `P_j`. -/
private theorem sum_ite_ofReal_pow_eq_coeff {p : ℝ} (hp : 1 < p) (P : ℚ[X]) (j : ℕ) :
    (∑ m ∈ P.support, if ((p ^ m : ℝ) : ℂ) = ((p ^ j : ℝ) : ℂ) then (P.coeff m : ℂ) else 0) =
      P.coeff j := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hinj : ∀ m, ((p ^ m : ℝ) : ℂ) = ((p ^ j : ℝ) : ℂ) ↔ m = j := fun m ↦
    ⟨fun h ↦ by simpa using eq_of_rpow_div_two_eq hp (x := 2 * m) (y := 2 * j) (by
      rw [← norm_ofReal_pow_eq_rpow hp0, ← norm_ofReal_pow_eq_rpow hp0, h]), fun h ↦ h ▸ rfl⟩
  simp only [hinj, sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> simp [h]

/-- **Polynomial approximation of graded moments.** Let `p > 1`, and in each degree `0 ≤ i ≤ r`
let `α i k`, for `k < b i`, be complex numbers of absolute value `p ^ (i / 2)`. Suppose that the
alternating moments `∑ i, (-1) ^ i ∑ k, α i k ^ n` differ from `P(pⁿ)`, for a polynomial
`P ∈ ℚ[T]`, by `o(p ^ (s n / 2))`. Then

* every odd degree `i ≥ s` is empty;
* in every even degree `i = 2 j ≥ s`, the coefficient of `T ^ j` in `P` is the number `b i` of
  numbers in degree `i`, and each of them equals `p ^ j`;
* the coefficient of `T ^ j` in `P` vanishes whenever `2 j ≥ s` and `2 j > r`.

Nothing is asserted below the cutoff `s`, which is an arbitrary natural number. -/
theorem graded_polynomial_approximation {p : ℝ} (hp : 1 < p) {r s : ℕ}
    {b : Fin (r + 1) → ℕ} {α : (i : Fin (r + 1)) → Fin (b i) → ℂ} {P : ℚ[X]}
    (hweight : ∀ i k, ‖α i k‖ = p ^ ((i : ℝ) / 2))
    (hlimit : Tendsto (fun n : ℕ ↦ ‖(∑ i : Fin (r + 1), (-1 : ℂ) ^ (i : ℕ) * ∑ k, α i k ^ n) -
        P.eval₂ (algebraMap ℚ ℂ) ((p ^ n : ℝ) : ℂ)‖ / p ^ ((s : ℝ) * n / 2)) atTop (𝓝 0)) :
    (∀ i : Fin (r + 1), s ≤ i → Odd (i : ℕ) → b i = 0) ∧
    (∀ i : Fin (r + 1), s ≤ i → ∀ j : ℕ, (i : ℕ) = 2 * j →
      P.coeff j = b i ∧ ∀ k, α i k = (p ^ j : ℝ)) ∧
    (∀ j : ℕ, s ≤ 2 * j → r < 2 * j → P.coeff j = 0) := by
  classical
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  -- A number of absolute value at least `p ^ (s / 2)` carries total weight zero.
  have hcancel := fun {z : ℂ} ↦ sum_sum_ite_eq_sum_ite_of_tendsto (z := z) hp hlimit
  have hle : ∀ {a : ℕ}, s ≤ a → p ^ ((s : ℝ) / 2) ≤ p ^ ((a : ℝ) / 2) := fun h ↦
    Real.rpow_le_rpow_of_exponent_le hp.le (by gcongr)
  -- The only possible power `p ^ m` of degree `2 j` is `p ^ j`.
  have hpow : ∀ {m : ℕ} {i : Fin (r + 1)} {k}, α i k = ((p ^ m : ℝ) : ℂ) → (i : ℕ) = 2 * m :=
    fun h ↦ eq_of_rpow_div_two_eq hp (by rw [← hweight, h, norm_ofReal_pow_eq_rpow hp0])
  -- A number of degree `i ≥ s` is a power of `p`: otherwise it has nothing to cancel against.
  have hnotpow : ∀ (i : Fin (r + 1)) k, s ≤ (i : ℕ) → ∃ m : ℕ, α i k = ((p ^ m : ℝ) : ℂ) := by
    intro i k hi
    by_contra! hk
    have h := hcancel (z := α i k) (hweight i k ▸ hle hi)
    rw [sum_sum_ite_eq_sum_ite_of_norm_eq hp hweight i (hweight i k),
      sum_eq_zero fun m _ ↦ ite_eq_right (Ne.symm (hk m)), ← sum_filter, sum_const,
      nsmul_eq_mul] at h
    simp only [mul_eq_zero, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_univ,
      forall_const, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, or_false] at h
    exact h rfl
  refine ⟨fun i hi hodd ↦ ?_, fun i hi j hij ↦ ?_, fun j hj hr ↦ ?_⟩
  · -- An odd degree has no power of `p` of its absolute value.
    by_contra hb
    obtain ⟨m, hm⟩ := hnotpow i ⟨0, Nat.pos_of_ne_zero hb⟩ hi
    exact Nat.not_even_iff_odd.2 hodd ⟨m, by rw [hpow hm]; ring⟩
  · -- In degree `2 j` every number is `p ^ j`, and their count cancels the coefficient `P_j`.
    have hall : ∀ k, α i k = ((p ^ j : ℝ) : ℂ) := fun k ↦ by
      obtain ⟨m, hm⟩ := hnotpow i k hi
      obtain rfl : m = j := by have := hpow hm; omega
      exact hm
    refine ⟨?_, hall⟩
    have h := hcancel (z := ((p ^ j : ℝ) : ℂ))
      (by rw [norm_ofReal_pow_eq_rpow hp0, ← hij]; exact hle hi)
    rw [sum_sum_ite_eq_sum_ite_of_norm_eq hp hweight i
      (by rw [norm_ofReal_pow_eq_rpow hp0, hij]), sum_ite_ofReal_pow_eq_coeff hp] at h
    simp only [hall, ite_true, sum_const, card_univ, Fintype.card_fin, hij, pow_mul, neg_one_sq,
      one_pow, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h.symm
  · -- Above degree `r` there is nothing to cancel the coefficient `P_j`.
    have h := hcancel (z := ((p ^ j : ℝ) : ℂ))
      (by rw [norm_ofReal_pow_eq_rpow hp0]; exact hle hj)
    have h0 : (∑ i, ∑ k, if α i k = ((p ^ j : ℝ) : ℂ) then (-1 : ℂ) ^ (i : ℕ) else 0) = 0 :=
      sum_eq_zero fun i _ ↦ sum_eq_zero fun k _ ↦ ite_eq_right fun h ↦ by
        have := hpow h; have := i.isLt; omega
    rw [sum_ite_ofReal_pow_eq_coeff hp, h0] at h
    exact_mod_cast h.symm

end TauCeti
