/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Sequence
public import TauCeti.Data.List.PermanencesMinusVariations
public import TauCeti.RingTheory.Polynomial.Subresultant.Euclidean
public import TauCeti.RingTheory.Polynomial.Subresultant.Signed
import TauCeti.Data.Nat.Choose.Basic

/-! # Cauchy indices from signed subresultant coefficients

Let `p` and `q` be polynomials over an ordered real closed field with
`q.natDegree < p.natDegree = m`, and let `s_j = signedPsc p q m q.natDegree j` be their signed
principal subresultant coefficients at the actual degrees. The permanences minus variations of
the list `[s_m, …, s_0]` is the Cauchy index of `q / p` on the whole line. Since that index
counts roots and computes Tarski queries, the number of distinct roots of `p` and the Tarski
query of `q` at the roots of `p` are determined by the signs of principal subresultant
coefficients alone, which are polynomials in the coefficients of `p` and `q`.

The proof follows the signed remainder sequence `p, q, -(p % q), …`. One Euclidean step
multiplies the signed coefficients of index at most `(p % q).natDegree` by a common nonzero
constant, and the coefficients of larger index below `q.natDegree` vanish. On the Cauchy-index
side, the same step changes the whole-line index by the contribution of the leading pair.

## Main declarations

* `Polynomial.signedPsc_eq_mul_signedPsc_neg_mod`: the signed coefficients of `(p, q)` and of
  `(q, -(p % q))` differ by a factor independent of the index.
* `Polynomial.signedPsc_eq_zero_of_natDegree_mod_lt`: vanishing strictly between the degrees of
  the remainder and of `q`.
* `Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc`: the Cauchy index of
  `q / p` is permanences minus variations of the signed principal coefficients.
* `Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc_mod`: the same for an
  arbitrary numerator, reduced modulo `p`.
* `Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc`,
  `Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc`: Tarski queries and
  the number of distinct roots from principal coefficients.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 4 (signed subresultants and the Cauchy index).
-/

public section

namespace TauCeti

open Polynomial Set SignType

section Field

variable {K : Type*} [Field K]

/-- One step of the signed remainder sequence multiplies the signed principal coefficients by a
common factor. For indices at most a bound `r` for the remainder, the signed coefficients of
`(p, q)` are those of `(q, -(p % q))` times `(-1) ^ (m - q.natDegree).choose 2 *
q.leadingCoeff ^ (m - r)`, which does not depend on the index. -/
theorem _root_.Polynomial.signedPsc_eq_mul_signedPsc_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hqm : q.natDegree ≤ m) (hr : (p % q).natDegree ≤ r)
    (hrm : r ≤ m) (hjr : j ≤ r) (hjq : j ≤ q.natDegree) :
    signedPsc p q m q.natDegree j =
      (-1) ^ (m - q.natDegree).choose 2 * q.leadingCoeff ^ (m - r) *
        signedPsc q (-(p % q)) q.natDegree r j := by
  rw [signedPsc_of_le p q (le_min (hjq.trans hqm) hjq), signedPsc_of_le _ _ (le_min hjq hjr),
    psc_eq_sign_mul_leadingCoeff_pow_mul_psc_neg_mod hp hr hrm hjr hjq]
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self (q.natDegree - j)
  have hexp : (m - j).choose 2 + (m - j + 1) * (q.natDegree - j) =
      (m - q.natDegree).choose 2 + (q.natDegree - j).choose 2 +
        2 * ((m - q.natDegree) * (q.natDegree - j) + t) := by
    rw [show m - j = (m - q.natDegree) + (q.natDegree - j) by omega, Nat.add_choose_two]
    nlinarith [ht]
  have hsign : (-1 : K) ^ (m - j).choose 2 * (-1) ^ ((m - j + 1) * (q.natDegree - j)) =
      (-1) ^ (m - q.natDegree).choose 2 * (-1) ^ (q.natDegree - j).choose 2 := by
    rw [← pow_add, hexp, pow_add, pow_add, pow_mul]
    simp
  linear_combination (q.leadingCoeff ^ (m - r) * psc q (-(p % q)) q.natDegree r j) * hsign

/-- The signed principal coefficients vanish at the indices strictly between the degree of the
remainder `p % q` and the degree of `q`. -/
theorem _root_.Polynomial.signedPsc_eq_zero_of_natDegree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hrj : (p % q).natDegree < j) (hjq : j < q.natDegree)
    (hjm : j ≤ m) :
    signedPsc p q m q.natDegree j = 0 := by
  rw [signedPsc_of_le p q (le_min hjm hjq.le), psc_eq_zero_of_natDegree_mod_lt hp hrj hjq hjm,
    mul_zero]

end Field

/-- Mapping a function along the reversed range `[b - 1, …, 0]`, where it vanishes on
`[a, b)`. -/
private theorem map_reverse_range_eq_replicate_append {α : Type*} [Zero α] (f : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) (h : ∀ j, a ≤ j → j < b → f j = 0) :
    (List.range b).reverse.map f = List.replicate (b - a) 0 ++ (List.range a).reverse.map f := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, h b hab (by omega), ih fun j h1 h2 => h j h1 (by omega),
      show b + 1 - a = (b - a) + 1 by omega, List.replicate_succ, List.cons_append]

/-- The reversed range `[k, …, 0]` begins with `k`. -/
private theorem map_reverse_range_succ {α : Type*} (f : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).reverse.map f = f k :: (List.range k).reverse.map f := by
  simp [List.range_succ]

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The leading pair `[s_m, 0, …, 0, s_n]` contributes the sign of `p * q` at infinity when
the degrees have opposite parities. -/
private theorem permanencesMinusVariations_signedPsc_eq_add {p q : K[X]} (hq : q ≠ 0)
    (h : q.natDegree < p.natDegree) :
    ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations =
      (if Odd (p.natDegree + q.natDegree) then
        (sign p.leadingCoeff : ℤ) * sign q.leadingCoeff else 0) +
      ((List.range (q.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations := by
  set m := p.natDegree with hm
  set n := q.natDegree with hn
  set s := signedPsc p q m n
  have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hsm : s m = p.leadingCoeff := by
    simp [s, hm, show ¬ p.natDegree ≤ n by omega]
  have hsn : s n = (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - n) := by
    simp [s, hn, show q.natDegree ≤ m by omega]
  have hsn0 : s n ≠ 0 := by simp [hsn, hq']
  rw [map_reverse_range_succ,
    map_reverse_range_eq_replicate_append s (a := n + 1) (b := m) h fun j hj hjm => by
      simp [s, signedPsc_of_lt p q (show min m n < j by omega), hjm.ne, show j ≠ n by omega],
    map_reverse_range_succ, List.permanencesMinusVariations_cons_replicate_zero_append hsn0]
  congr 1
  obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
  have hk' : m - (n + 1) = k := by omega
  have hodd : Odd (m + n) ↔ Even k := by
    simp only [Nat.odd_iff, Nat.even_iff]
    omega
  rw [hk']
  by_cases hke : Even k
  · simp only [hke, hodd.2 hke, ↓reduceIte, hsm, hsn, hk]
    have hc : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    simp only [sign_mul, sign_pow, Left.sign_neg, sign_one,
      SignType.pow_even _ hke (sign_ne_zero.mpr hq'),
      hc, pow_add, SignType.coe_mul, SignType.coe_pow, SignType.coe_neg, SignType.coe_one]
    rw [hke.neg_one_pow]
    have h2 : ((-1 : ℤ) ^ k.choose 2) * (-1) ^ k.choose 2 = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (sign p.leadingCoeff * sign q.leadingCoeff : ℤ) * h2
  · simp only [hke, mt hodd.1 hke, ↓reduceIte]

/-- After the leading entry, the signed coefficients of `(p, q)` and of `(q, -(p % q))` have the
same permanences minus variations. -/
private theorem permanencesMinusVariations_signedPsc_neg_mod {p q : K[X]}
    (h : q.natDegree < p.natDegree) (hn : q.natDegree ≠ 0) :
    ((List.range (q.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations =
      ((List.range (q.natDegree + 1)).reverse.map (signedPsc q (-(p % q)) q.natDegree
        (-(p % q)).natDegree)).permanencesMinusVariations := by
  set m := p.natDegree
  set n := q.natDegree with hn'
  set ρ := (-(p % q)).natDegree with hρ'
  have hq : q ≠ 0 := by rintro rfl; simp [n] at hn
  have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hρr : (p % q).natDegree = ρ := (natDegree_neg _).symm
  have hρ : ρ < n := hρr ▸ natDegree_mod_lt p hn
  set s := signedPsc p q m n
  set t := signedPsc q (-(p % q)) n ρ
  set c : K := (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - ρ) with hcdef
  have hc : c ≠ 0 := by simp [c, hq']
  -- Below the remainder degree the two coefficient lists are proportional.
  have hst : (List.range (ρ + 1)).reverse.map s =
      ((List.range (ρ + 1)).reverse.map t).map (c * ·) := by
    simp only [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj : j ≤ ρ := by
      rw [List.mem_reverse, List.mem_range] at hj
      omega
    exact signedPsc_eq_mul_signedPsc_neg_mod le_rfl h.le hρr.le (by omega) hj (by omega)
  have hsn : s n = (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - n) := by
    simp [s, hn', show q.natDegree ≤ m by omega]
  have htn : t n = q.leadingCoeff := by simp [t, hn', show ¬ q.natDegree ≤ ρ by omega]
  have htρ : t ρ = (-1) ^ (n - ρ).choose 2 * (-(p % q)).coeff ρ ^ (n - ρ) := by
    simp [t, hρ.le]
  rw [map_reverse_range_succ s n,
    map_reverse_range_eq_replicate_append s (a := ρ + 1) (b := n) hρ fun j hj hjn =>
      signedPsc_eq_zero_of_natDegree_mod_lt le_rfl (by omega) hjn (by omega), hst,
    map_reverse_range_succ t n,
    map_reverse_range_eq_replicate_append t (a := ρ + 1) (b := n) hρ fun j hj hjn => by
      simp [t, signedPsc_of_lt q _ (show min n ρ < j by omega), hjn.ne, show j ≠ ρ by omega],
    htn, map_reverse_range_succ t ρ]
  by_cases hr : p % q = 0
  · -- A zero remainder leaves no nonzero entry after the first one.
    have hρ0 : ρ = 0 := by simp [ρ, hr]
    have ht0 : t ρ = 0 := by simp [htρ, hr, show n - ρ ≠ 0 by omega]
    rw [hρ0] at ht0
    simp [ht0, hρ0, ← List.replicate_succ']
  · have hlc : (-(p % q)).coeff ρ ≠ 0 := by
      rw [hρ', coeff_natDegree]
      simpa using hr
    have htρ0 : t ρ ≠ 0 := by
      rw [htρ]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hlc)
    rw [List.map_cons, List.permanencesMinusVariations_cons_replicate_zero_append
        (mul_ne_zero hc htρ0), ← List.map_cons, List.permanencesMinusVariations_map_mul_left hc,
      List.permanencesMinusVariations_cons_replicate_zero_append htρ0]
    congr 1
    split_ifs with hk
    · -- Across an even gap, `s n * c` has the sign of `q.leadingCoeff ^ (odd)`.
      have hodd : Odd ((m - n) + (m - ρ)) := by
        obtain ⟨i, hi⟩ := hk
        exact ⟨m - n + i, by omega⟩
      have h1 : ((-1 : K) ^ (m - n).choose 2) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        simp
      have key : (sign (s n) : ℤ) * sign c = sign q.leadingCoeff := by
        rw [← SignType.coe_mul, ← sign_mul, hsn, hcdef,
          show (-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - n) *
              ((-1) ^ (m - n).choose 2 * q.leadingCoeff ^ (m - ρ)) =
            q.leadingCoeff ^ ((m - n) + (m - ρ)) by
            linear_combination (q.leadingCoeff ^ (m - n) * q.leadingCoeff ^ (m - ρ)) * h1]
        simp [sign_pow, SignType.pow_odd _ hodd]
      simp only [sign_mul, SignType.coe_mul]
      linear_combination ((-1) ^ (n - (ρ + 1)).choose 2 * (sign (t ρ) : ℤ)) * key
    · rfl

end Ordered

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Cauchy index by signed subresultants.** For `q.natDegree < p.natDegree = m`, the
whole-line Cauchy index of `q / p` is the permanences minus variations of the signed principal
subresultant coefficients `[s_m, …, s_0]` of `p` and `q` at their actual degrees. The numerator
may be zero, and `p` and `q` may have common factors and multiple roots. -/
theorem _root_.Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc {p q : R[X]}
    (h : q.natDegree < p.natDegree) :
    cauchyIndex p q univ =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p q p.natDegree q.natDegree)).permanencesMinusVariations := by
  induction hn : q.natDegree using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
  subst hn
  by_cases hq : q = 0
  · -- Only the leading entry `p.leadingCoeff` is nonzero.
    subst hq
    rw [cauchyIndex_zero_right, map_reverse_range_succ,
      map_reverse_range_eq_replicate_append _ (Nat.zero_le _) fun j _ hj => ?_]
    · simp
    · rcases eq_or_ne j 0 with rfl | hj0
      · exact signedPsc_zero_right p (by simp) (by simpa using h)
      · rw [signedPsc_of_lt _ _ (by simp only [natDegree_zero]; omega)]
        simp [hj.ne, hj0]
  have hp : p ≠ 0 := by rintro rfl; simp at h
  rw [cauchyIndex_univ_eq_add_cauchyIndex_neg_mod hp hq,
    permanencesMinusVariations_signedPsc_eq_add hq h]
  congr 1
  by_cases hn : q.natDegree = 0
  · -- A constant `q` has no poles, and the remaining list is a singleton.
    have hq0 : cauchyIndex q (-(p % q)) univ = 0 := by
      rw [eq_C_of_natDegree_eq_zero hn, cauchyIndex_C]
    rw [hq0, hn]
    simp
  rw [permanencesMinusVariations_signedPsc_neg_mod h hn]
  have hr : (-(p % q)).natDegree < q.natDegree := by
    rw [natDegree_neg]
    exact natDegree_mod_lt p hn
  exact ih _ hr hr rfl

/-- **Cauchy index by signed subresultants, general numerator.** Reducing `q` modulo `p` does not
change the Cauchy index of `q / p`, so it is the permanences minus variations of the signed
principal subresultant coefficients of `p` and `q % p`. For constant `p` both sides vanish. -/
theorem _root_.Polynomial.cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc_mod
    (p q : R[X]) :
    cauchyIndex p q univ =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p (q % p) p.natDegree (q % p).natDegree)).permanencesMinusVariations := by
  rcases eq_or_ne p.natDegree 0 with hp | hp
  · rw [eq_C_of_natDegree_eq_zero hp, cauchyIndex_C, natDegree_C]
    simp
  rw [← cauchyIndex_mod]
  exact cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc (natDegree_mod_lt q hp)

/-- The Tarski query of `q` at the roots of `p` is the permanences minus variations of the signed
principal subresultant coefficients of `p` and `p' * q % p`. -/
theorem _root_.Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc (p q : R[X]) :
    tarskiQuery p q =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p (derivative p * q % p) p.natDegree
          (derivative p * q % p).natDegree)).permanencesMinusVariations := by
  rw [← cauchyIndex_derivative_mul_univ,
    cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc_mod]

/-- The number of distinct roots of `p` is the permanences minus variations of the signed
principal subresultant coefficients of `p` and its derivative. -/
theorem _root_.Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc
    (p : R[X]) :
    (p.roots.toFinset.card : ℤ) =
      ((List.range (p.natDegree + 1)).reverse.map
        (signedPsc p (derivative p) p.natDegree
          (derivative p).natDegree)).permanencesMinusVariations := by
  classical
  rcases eq_or_ne p.natDegree 0 with hp | hp
  · rw [eq_C_of_natDegree_eq_zero hp]
    simp
  rw [← cauchyIndex_univ_eq_permanencesMinusVariations_signedPsc
    (natDegree_derivative_lt hp), cauchyIndex_derivative]
  simp

end TauCeti
