/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.OfFn
public import TauCeti.Analysis.Polynomial.L1Norm
public import TauCeti.NumberTheory.Height.House
public import TauCeti.NumberTheory.NumberField.SiegelsLemma
public import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Thue's auxiliary polynomials

Let `α` be an algebraic number of degree `d`, let `b ≥ 1` be an integer with `b α` integral, and
let `0 < ε < 1 / 2`. For every `r ≥ 1` there are integer polynomials `P` and `Q`, not both zero,
of degree at most `⌊(1 / 2 + ε) d r⌋` such that `(X - α) ^ r` divides `P - α Q`, and whose
coefficient lengths are at most `C₁ ^ r`, where `C₁ = (48 b max(1, ⌈α⌉)) ^ (d (1 + 1 / ε))` and
`⌈α⌉` is the house of `α`.

These polynomials are the auxiliary construction in Thue's proof that an algebraic number of
degree `d ≥ 3` has only finitely many rational approximations `ξ` with
`|ξ - α| ≤ H(ξ) ^ (-κ)` for `κ > d / 2 + 1`: the polynomial `P - α Q` vanishes to high order at
`α`, so it is small near `α`, while its coefficients stay small because of the length bound.

The vanishing conditions are `r` linear equations over the number field `ℚ(α)` for the `2 (m + 1)`
integer coefficients of `P` and `Q`, where `m = ⌊(1 / 2 + ε) d r⌋`. Since `d r < 2 (m + 1)`,
Siegel's lemma (`NumberField.exists_ne_zero_int_vec_abs_le_of_house_le`) gives a small nonzero
integer solution.

## Main results

* `TauCeti.exists_thue_auxiliary_polynomials`: Thue's auxiliary polynomials, for an element `α`
  of any field of characteristic zero.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Lemma 6.10.
-/

public section

open Polynomial Finset Module NumberField

namespace TauCeti

variable {K : Type*} [Field K]

/-- Thue's auxiliary polynomials over a number field `K` of degree `d`, for any `m` with
`d r < 2 (m + 1)`, with the coefficient bound of Siegel's lemma. -/
private theorem exists_thue_auxiliary_polynomials_of_numberField [NumberField K] (α : K)
    {b : ℕ} (hb : 0 < b) (hbα : IsIntegral ℤ ((b : K) * α)) {r m : ℕ}
    (hm : finrank ℚ K * r < 2 * (m + 1)) :
    ∃ P Q : ℤ[X], (P ≠ 0 ∨ Q ≠ 0) ∧ P.natDegree ≤ m ∧ Q.natDegree ≤ m ∧
      (X - C α) ^ r ∣ P.map (Int.castRingHom K) - C α * Q.map (Int.castRingHom K) ∧
      ∀ i, |(P.coeff i : ℝ)| ≤
          (3 * (2 * (m + 1)) * (2 * b * max 1 (NumberField.house α)) ^ (m + 1)) ^
            ((finrank ℚ K * r : ℝ) / (2 * (m + 1) - finrank ℚ K * r)) ∧
        |(Q.coeff i : ℝ)| ≤
          (3 * (2 * (m + 1)) * (2 * b * max 1 (NumberField.house α)) ^ (m + 1)) ^
            ((finrank ℚ K * r : ℝ) / (2 * (m + 1) - finrank ℚ K * r)) := by
  classical
  set H := max 1 (NumberField.house α)
  -- The `k`-th equation, multiplied by `b ^ (m + 1)`, has coefficient `e k (inl i)` at the
  -- coefficient of `X ^ i` in `P` and `e k (inr i)` at that of `X ^ i` in `-Q`.
  let e : Fin r → Fin (m + 1) ⊕ Fin (m + 1) → K := fun k ↦ Sum.elim
    (fun i ↦ ((i : ℕ).choose k : K) * ((b : K) ^ (m + 1) * α ^ ((i : ℕ) - k)))
    (fun i ↦ ((i : ℕ).choose k : K) * ((b : K) ^ (m + 1) * α ^ ((i : ℕ) - k + 1)))
  have he (k j) : IsIntegral ℤ (e k j) := by
    rcases j with i | i <;> have := i.is_lt
    · exact (isIntegral_natCast _).mul (isIntegral_natCast_pow_mul_pow hbα (by omega))
    · exact (isIntegral_natCast _).mul (isIntegral_natCast_pow_mul_pow hbα (by omega))
  let a : Matrix (Fin r) (Fin (m + 1) ⊕ Fin (m + 1)) (𝓞 K) :=
    fun k j ↦ (⟨e k j, he k j⟩ : 𝓞 K)
  have hH : 1 ≤ H := le_max_left _ _
  have hA : 1 ≤ (2 * b * H : ℝ) ^ (m + 1) :=
    one_le_pow₀ (by nlinarith [show (1 : ℝ) ≤ b by exact_mod_cast hb])
  have ha (k j) : NumberField.house (a k j : K) ≤ (2 * b * H : ℝ) ^ (m + 1) := by
    rcases j with i | i <;> have := i.is_lt <;>
      refine house_natCast_mul_pow_mul_pow_le α ((Nat.choose_le_two_pow _ _).trans
        (Nat.pow_le_pow_right two_pos (by omega))) (by omega)
  have hcard :
      finrank ℚ K * Fintype.card (Fin r) < Fintype.card (Fin (m + 1) ⊕ Fin (m + 1)) := by
    simp only [Fintype.card_fin, Fintype.card_sum]
    omega
  obtain ⟨x, hx0, hax, hxle⟩ := exists_ne_zero_int_vec_abs_le_of_house_le a hA hcard ha
  set P : ℤ[X] := ofFn (m + 1) fun i ↦ x (.inl i)
  set Q : ℤ[X] := ofFn (m + 1) fun i ↦ -x (.inr i)
  have hdeg (f : Fin (m + 1) → ℤ) : (ofFn (m + 1) f).natDegree ≤ m :=
    Nat.lt_succ_iff.mp (ofFn_natDegree_lt m.succ_pos f)
  refine ⟨P, Q, ?_, hdeg _, hdeg _, ?_, fun n ↦ ?_⟩
  · -- A nonzero coordinate of `x` is a coefficient of `P` or of `-Q`.
    by_contra! h
    refine hx0 (funext fun j ↦ ?_)
    rcases j with i | i
    · simpa [P, ofFn_coeff_eq_val_of_lt _ i.is_lt] using congrArg (coeff · i) h.1
    · simpa [Q, ofFn_coeff_eq_val_of_lt _ i.is_lt] using congrArg (coeff · i) h.2
  · have hmap : P.map (Int.castRingHom K) - C α * Q.map (Int.castRingHom K) =
        ofFn (m + 1) fun i ↦ (x (.inl i) : K) + α * x (.inr i) := by
      ext n
      by_cases hn : n < m + 1
      · simp [P, Q, hn]
      · simp [P, Q, not_lt.mp hn]
    rw [hmap, X_sub_C_pow_dvd_ofFn_iff]
    intro k hk
    -- `(a k j : K)` is `e k j` by `RingOfIntegers.map_mk`, which holds by `rfl`.
    have hk' : ∑ j, e ⟨k, hk⟩ j * (x j : K) = 0 :=
      sum_mul_intCast_eq_zero_of_mulVec_eq_zero hax ⟨k, hk⟩
    simp only [Fintype.sum_sum_type, e, Sum.elim_inl, Sum.elim_inr] at hk'
    have hb' : (b : K) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
    refine (mul_eq_zero.mp ?_).resolve_left hb'
    rw [← hk', mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  · -- Coefficients outside `Fin (m + 1)` vanish; the others are coordinates of `x`.
    have hN : (Fintype.card (Fin (m + 1) ⊕ Fin (m + 1)) : ℝ) = 2 * (m + 1) := by
      simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      ring
    have hx (j) := hxle j
    simp only [hN, Fintype.card_fin] at hx
    by_cases hn : n < m + 1
    · simpa [P, Q, hn] using ⟨hx _, hx _⟩
    · simpa [P, Q, not_lt.mp hn] using (abs_nonneg _).trans (hx (.inl 0))

/-- The coefficient bound of Siegel's lemma for Thue's linear system, multiplied by the number
`m + 1` of coefficients, is at most `C₁ ^ r` for `C₁ = (48 b H) ^ (d (1 + 1 / ε))`. -/
private theorem thue_length_bound_le {d r b : ℕ} {ε H : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    (hd : 0 < d) (hr : 0 < r) (hb : 0 < b) (hH : 1 ≤ H) :
    (⌊(1 / 2 + ε) * d * r⌋₊ + 1 : ℝ) *
        (3 * (2 * (⌊(1 / 2 + ε) * d * r⌋₊ + 1)) * (2 * b * H) ^ (⌊(1 / 2 + ε) * d * r⌋₊ + 1)) ^
          ((d * r : ℝ) / (2 * (⌊(1 / 2 + ε) * d * r⌋₊ + 1) - d * r)) ≤
      ((48 * b * H) ^ (d * (1 + 1 / ε))) ^ r := by
  set m := ⌊(1 / 2 + ε) * d * r⌋₊
  set c : ℝ := 2 * b * H
  set p : ℝ := 1 / (2 * ε)
  have hD : (1 : ℝ) ≤ d * r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm₁ : (1 / 2 + ε) * d * r < m + 1 := by exact_mod_cast Nat.lt_floor_add_one _
  -- Since `1 / 2 + ε < 1`, the degree bound `m` is less than `d r`.
  have hm₂ : (m + 1 : ℝ) ≤ d * r := by
    have : m < d * r := (Nat.floor_lt (by positivity)).mpr (by push_cast; nlinarith)
    exact_mod_cast this
  have hc : 1 ≤ c := by nlinarith [show (1 : ℝ) ≤ b by exact_mod_cast hb]
  have hp : 1 ≤ p := by rw [le_div_iff₀ (by positivity)]; linarith
  -- The exponent of Siegel's lemma is at most `p = 1 / (2 ε)`.
  have he : (d * r : ℝ) / (2 * (m + 1) - d * r) ≤ p := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have h12 : (6 * (m + 1) : ℝ) ≤ 12 ^ (m + 1) := by
    have h2 : (m + 1 : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc (6 * (m + 1) : ℝ) ≤ 6 * 2 ^ (m + 1) := by gcongr
      _ = 12 * 2 ^ m := by ring
      _ ≤ 12 * 12 ^ m := by gcongr; norm_num
      _ = 12 ^ (m + 1) := by ring
  have hβ : 3 * (2 * (m + 1)) * c ^ (m + 1) ≤ (12 * c) ^ (m + 1) :=
    calc 3 * (2 * (m + 1)) * c ^ (m + 1) = 6 * (m + 1) * c ^ (m + 1) := by ring
      _ ≤ 12 ^ (m + 1) * c ^ (m + 1) := by gcongr
      _ = (12 * c) ^ (m + 1) := (mul_pow _ _ _).symm
  have hβ₁ : (1 : ℝ) ≤ 3 * (2 * (m + 1)) * c ^ (m + 1) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hc)
  calc (m + 1 : ℝ) * (3 * (2 * (m + 1)) * c ^ (m + 1)) ^ ((d * r : ℝ) / (2 * (m + 1) - d * r))
      ≤ (2 ^ (m + 1)) ^ p * ((12 * c) ^ (m + 1)) ^ p := by
        gcongr
        · exact (show (m + 1 : ℝ) ≤ 2 ^ (m + 1) by exact_mod_cast (Nat.lt_two_pow_self).le).trans
            (Real.self_le_rpow_of_one_le (one_le_pow₀ one_le_two) hp)
        · exact (Real.rpow_le_rpow_of_exponent_le hβ₁ he).trans
            (Real.rpow_le_rpow (by positivity) hβ (by positivity))
    _ = (48 * b * H) ^ (((m + 1 : ℕ) : ℝ) * p) := by
        rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_pow, Real.rpow_mul
          (by positivity), Real.rpow_natCast]
        congr 2
        ring
    _ ≤ (48 * b * H) ^ (d * (1 + 1 / ε) * r) := by
        refine Real.rpow_le_rpow_of_exponent_le (by nlinarith) ?_
        have : ((m + 1 : ℕ) : ℝ) * p ≤ d * r * p := by push_cast; gcongr
        have : (d * r : ℝ) * p ≤ d * (1 + 1 / ε) * r := by
          simp only [p]
          field_simp
          nlinarith
        linarith
    _ = ((48 * b * H) ^ (d * (1 + 1 / ε))) ^ r := Real.rpow_mul_natCast (by positivity) _ _

/-- **Thue's auxiliary polynomials** (Evertse, Lemma 6.10). Let `α` be an algebraic number of
degree `d` in a field of characteristic zero, and let `b ≥ 1` be an integer such that `b α` is
integral over `ℤ`. For `0 < ε < 1 / 2` and `r ≥ 1` there are integer polynomials `P` and `Q`, not
both zero, of degree at most `⌊(1 / 2 + ε) d r⌋`, such that `(X - α) ^ r` divides `P - α Q` and
both coefficient lengths are at most `C₁ ^ r`, where `C₁ = (48 b max(1, ⌈α⌉)) ^ (d (1 + 1 / ε))`
and `⌈α⌉` is the house of `α`. -/
theorem exists_thue_auxiliary_polynomials {F : Type*} [Field F] [CharZero F] {α : F} {b : ℕ}
    (hb : 0 < b) (hbα : IsIntegral ℤ ((b : F) * α)) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    {r : ℕ} (hr : 0 < r) :
    ∃ P Q : ℤ[X], (P ≠ 0 ∨ Q ≠ 0) ∧
      P.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ ∧
      Q.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ ∧
      (X - C α) ^ r ∣ P.map (Int.castRingHom F) - C α * Q.map (Int.castRingHom F) ∧
      P.l1Norm ≤ ((48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε))) ^ r ∧
      Q.l1Norm ≤ ((48 * b * max 1 (house α)) ^ ((minpoly ℚ α).natDegree * (1 + 1 / ε))) ^ r := by
  classical
  -- Work in the number field `K = ℚ(α)`, of degree `d`.
  obtain ⟨K, _, α', hα', hdK, hbα', hhouse⟩ :=
    exists_numberField_of_isIntegral_natCast_mul hb.ne' hbα
  set d := (minpoly ℚ α).natDegree
  set m := ⌊(1 / 2 + ε) * d * r⌋₊
  have hd : 0 < d := hdK ▸ finrank_pos
  have hm : finrank ℚ K * r < 2 * (m + 1) := by
    have h : (1 / 2 + ε) * d * r < m + 1 := Nat.lt_floor_add_one _
    have : (d * r : ℝ) < 2 * (m + 1) := by nlinarith [show (0 : ℝ) ≤ d * r by positivity]
    rw [hdK]
    exact_mod_cast this
  obtain ⟨P, Q, hPQ, hP, hQ, hdvd, hcoeff⟩ :=
    exists_thue_auxiliary_polynomials_of_numberField α' hb hbα' hm
  rw [hhouse, hdK] at hcoeff
  -- The coefficient bound and the degree bound give the length bound.
  have hlen {R : ℤ[X]} (hR : R.natDegree ≤ m) (hRc : ∀ i, |(R.coeff i : ℝ)| ≤
      (3 * (2 * (m + 1)) * (2 * b * max 1 (house α)) ^ (m + 1)) ^
        ((d * r : ℝ) / (2 * (m + 1) - d * r))) :
      R.l1Norm ≤ ((48 * b * max 1 (house α)) ^ (d * (1 + 1 / ε))) ^ r := by
    refine le_trans ?_ (thue_length_bound_le hε₀ hε hd hr hb (le_max_left _ _))
    rw [R.l1Norm_eq_sum_of_support_subset (supp_subset_range_natDegree_succ.trans
      (range_subset_range.mpr (Nat.succ_le_succ hR)))]
    refine (sum_le_card_nsmul _ _ _ fun i _ ↦ (Int.norm_eq_abs _).trans_le (hRc i)).trans_eq ?_
    rw [card_range, nsmul_eq_mul, Nat.cast_add_one]
  refine ⟨P, Q, hPQ, hP, hQ, ?_, hlen hP fun i ↦ (hcoeff i).1, hlen hQ fun i ↦ (hcoeff i).2⟩
  -- Map the divisibility from `K[X]` to `F[X]`; both integer casts into `F` agree.
  have := Polynomial.map_dvd (algebraMap K F) hdvd
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, hα',
    Polynomial.map_map] at this
  rwa [RingHom.ext_int ((algebraMap K F).comp (Int.castRingHom K)) (Int.castRingHom F)] at this

end TauCeti
