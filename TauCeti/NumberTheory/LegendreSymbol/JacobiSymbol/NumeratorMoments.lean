/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Moments of Jacobi symbols with varying numerator

For an odd nonsquare denominator, the Jacobi character is nonprincipal, so Pólya–Vinogradov
bounds its partial sums. In a second moment of weighted Jacobi sums, this gives cancellation for
pairs of denominators whose product is not square. Pairs with square product retain the trivial
bound; in particular they can be estimated separately when the weights are Gaussian.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2007), Chapter 9.
* The numerator average in `New.sum_sq_thetaSeries_jacobiSym_le`, in `Lib/Analytic/QuadraticTwist`
  of [grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Finset

namespace TauCeti

/-- A Jacobi symbol of odd nonsquare denominator takes the value `-1`. -/
theorem exists_jacobiSym_eq_neg_one_of_odd_of_not_isSquare {b : ℕ} (hb : Odd b)
    (hs : ¬ IsSquare b) : ∃ a : ℕ, jacobiSym a b = -1 := by
  rw [Nat.isSquare_iff_even_factorization] at hs
  push Not at hs
  obtain ⟨p, hp, he⟩ := hs
  let m := b / p ^ b.factorization p
  have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hb.pos.ne'
  have hb' : p ^ b.factorization p * m = b := Nat.ordProj_mul_ordCompl_eq_self b p
  have hp₂ : p ≠ 2 := by
    intro h
    exact hb.not_two_dvd_nat (h ▸ Nat.dvd_of_factorization_pos he.pos.ne')
  obtain ⟨a, ha, hJ⟩ := exists_modEq_one_jacobiSym_eq_neg_one_of_prime hp hp₂
    (hp.coprime_iff_not_dvd.mpr hm)
  let : NeZero m := ⟨fun hz ↦ hm (hz ▸ dvd_zero p)⟩
  have h₁ : jacobiSym a m = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast ha), jacobiSym.one_left]
  let : NeZero (p ^ b.factorization p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨a, ?_⟩
  calc jacobiSym a b = jacobiSym a (p ^ b.factorization p * m) := congrArg (jacobiSym a) hb'.symm
    _ = -1 := by rw [jacobiSym.mul_right, jacobiSym.pow_right, hJ, h₁, mul_one, he.neg_one_pow]

/-- For odd denominator the Jacobi character is principal exactly at square levels, provided
`1` and `-1` are distinct in the coefficient ring. -/
theorem jacobiChar_eq_one_iff_isSquare_of_odd {R : Type*} [CommRing R] [NeZero (2 : R)]
    {b : ℕ} [NeZero b] (hb : Odd b) : jacobiChar R b = 1 ↔ IsSquare b := by
  constructor
  · intro h
    by_contra hs
    obtain ⟨a, ha⟩ := exists_jacobiSym_eq_neg_one_of_odd_of_not_isSquare hb hs
    have hc : a.Coprime b := by
      by_contra hnc
      have hz : jacobiSym a b = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr
        (by simpa only [Int.gcd_natCast_natCast, Nat.Coprime] using hnc)
      rw [ha] at hz
      norm_num at hz
    have hval := DFunLike.congr_fun h (a : ZMod b)
    rw [jacobiChar_natCast, ha, Int.cast_neg, Int.cast_one,
      MulChar.one_apply ((ZMod.isUnit_iff_coprime a b).mpr hc)] at hval
    apply two_ne_zero (α := R)
    calc (2 : R) = -1 + 1 := by rw [hval, one_add_one_eq_two]
      _ = 0 := neg_add_cancel 1
  · rintro ⟨d, hd⟩
    refine MulChar.ext fun u ↦ ?_
    let a := (u : ZMod b).val
    have hc : a.Coprime b := (ZMod.isUnit_iff_coprime _ _).mp (by simp [a])
    have hdvd : d ∣ b := hd ▸ dvd_mul_right d d
    have hg : (a : ℤ).gcd d = 1 := by
      simpa only [Int.gcd_natCast_natCast, Nat.Coprime] using hc.coprime_dvd_right hdvd
    have hj : jacobiSym a b = 1 := calc
      jacobiSym a b = jacobiSym a (d ^ 2) := congrArg (jacobiSym (a : ℤ)) (hd.trans (sq d).symm)
      _ = 1 := by rw [jacobiSym.pow_right, jacobiSym.sq_one hg]
    rw [jacobiChar_apply, MulChar.one_apply_coe, ← Int.cast_one (R := R)]
    exact congrArg (fun z : ℤ ↦ (z : R)) hj

/-- Pólya–Vinogradov for sums over the negative numerators `-1, …, -K` of the Jacobi symbol
with fixed odd nonsquare denominator. -/
theorem norm_sum_Icc_jacobiSym_neg_le {b : ℕ} (hb : Odd b) (hs : ¬ IsSquare b) (K : ℕ) :
    ‖∑ v ∈ Icc 1 K, (jacobiSym (-(v : ℤ)) b : ℂ)‖ ≤ 2 * Real.sqrt b * (1 + Real.log b) := by
  let : NeZero b := ⟨hb.pos.ne'⟩
  have hχ : jacobiChar ℂ b ≠ 1 := mt (jacobiChar_eq_one_iff_isSquare_of_odd hb).mp hs
  have hterm (v : ℕ) : (jacobiSym (-(v : ℤ)) b : ℂ) = jacobiChar ℂ b (-1) * jacobiChar ℂ b v := by
    rw [← jacobiChar_intCast, Int.cast_neg, Int.cast_natCast, ← neg_one_mul, map_mul]
  simp_rw [hterm]
  rw [← mul_sum, norm_mul, DirichletCharacter.norm_neg_one, one_mul]
  exact (jacobiChar ℂ b).norm_sum_Icc_le_of_ne_one hχ K

/-- In the numerator second moment, each pair of weights costs at most `K` when the
product of its odd denominators is square, and at most the smaller of `K` and the
Pólya–Vinogradov bound otherwise. The indices need not have distinct denominators. -/
theorem sum_norm_sq_jacobiSym_neg_le {ι : Type*} (S : Finset ι) (m : ι → ℕ) (c : ι → ℂ)
    (hm : ∀ i ∈ S, Odd (m i)) (K : ℕ) :
    ∑ v ∈ Icc 1 K, ‖∑ i ∈ S, c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)‖ ^ 2 ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ *
        (if IsSquare (m i * m j) then (K : ℝ)
          else min K (2 * Real.sqrt (m i * m j : ℕ) * (1 + Real.log (m i * m j : ℕ)))) := by
  -- Keep the signed correlations inside the norm until the numerator sum has been taken.
  let J (v b : ℕ) : ℂ := jacobiSym (-(v : ℤ)) b
  have hexpand (v : ℕ) :
      ‖∑ i ∈ S, c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)‖ ^ 2 =
        (∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) * J v (m i * m j)).re := by
    rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _),
      Complex.normSq_eq_conj_mul_self, mul_comm, map_sum, sum_mul]
    simp_rw [mul_sum]
    congr 1
    refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
    let : NeZero (m i) := ⟨(hm i hi).pos.ne'⟩
    let : NeZero (m j) := ⟨(hm j hj).pos.ne'⟩
    simp [J, jacobiSym.mul_right, mul_assoc, mul_left_comm]
  simp_rw [hexpand]
  rw [← Complex.re_sum, sum_comm (s := Icc 1 K)]
  simp_rw [sum_comm (s := Icc 1 K), ← mul_sum, Complex.re_sum]
  refine sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ ?_
  set b := m i * m j
  have hb : Odd b := (hm i hi).mul (hm j hj)
  let : NeZero b := ⟨hb.pos.ne'⟩
  have hK : ‖∑ v ∈ Icc 1 K, J v b‖ ≤ (K : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ v ∈ Icc 1 K, ‖J v b‖ ≤ ∑ _v ∈ Icc 1 K, (1 : ℝ) := by
          refine sum_le_sum fun v _ ↦ ?_
          simpa only [J, ← jacobiChar_intCast] using
            (jacobiChar ℂ b).norm_le_one ((-(v : ℤ) : ℤ) : ZMod b)
      _ = K := by simp
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_star]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases hs : IsSquare b
  · simpa [hs] using hK
  · simpa [hs] using le_min hK (norm_sum_Icc_jacobiSym_neg_le hb hs K)

/-- The numerator second-moment bound for absolutely summable weights. The product-indexed
majorant is summable because each correlation is bounded by `K`. -/
theorem sum_norm_sq_tsum_jacobiSym_neg_le {ι : Type*} (m : ι → ℕ) (c : ι → ℂ)
    (hm : ∀ i, Odd (m i)) (hc : Summable (fun i ↦ ‖c i‖)) (K : ℕ) :
    ∑ v ∈ Icc 1 K, ‖∑' i, c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)‖ ^ 2 ≤
      ∑' p : ι × ι, ‖c p.1‖ * ‖c p.2‖ *
        (if IsSquare (m p.1 * m p.2) then (K : ℝ)
          else min K (2 * Real.sqrt (m p.1 * m p.2 : ℕ) * (1 + Real.log (m p.1 * m p.2 : ℕ)))) := by
  let F (v : ℕ) (i : ι) := c i * (jacobiSym (-(v : ℤ)) (m i) : ℂ)
  set B : ι × ι → ℝ := fun p ↦ ‖c p.1‖ * ‖c p.2‖ *
    (if IsSquare (m p.1 * m p.2) then (K : ℝ)
      else min K (2 * Real.sqrt (m p.1 * m p.2 : ℕ) * (1 + Real.log (m p.1 * m p.2 : ℕ))))
  have hB₀ (p) : 0 ≤ B p := by
    have hp : (1 : ℝ) ≤ (m p.1 * m p.2 : ℕ) := by exact_mod_cast ((hm p.1).mul (hm p.2)).pos
    dsimp only [B]
    split_ifs <;> positivity [Real.log_nonneg hp]
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le hB₀ (fun p ↦ ?_)
      ((hc.mul_of_nonneg hc (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_right (K : ℝ))
    dsimp only [B]
    split_ifs
    · rfl
    · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  have hF (v : ℕ) : Summable (F v) := by
    refine hc.of_norm_bounded fun i ↦ ?_
    let : NeZero (m i) := ⟨(hm i).pos.ne'⟩
    dsimp only [F]
    rw [norm_mul, ← jacobiChar_intCast]
    exact mul_le_of_le_one_right (norm_nonneg _) ((jacobiChar ℂ (m i)).norm_le_one _)
  have hlim : Filter.Tendsto
      (fun S : Finset ι ↦ ∑ v ∈ Icc 1 K, ‖∑ i ∈ S, F v i‖ ^ 2) Filter.atTop
      (nhds (∑ v ∈ Icc 1 K, ‖∑' i, F v i‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun v _ ↦ ?_
    have hv : Filter.Tendsto (fun S : Finset ι ↦ ∑ i ∈ S, F v i) Filter.atTop
      (nhds (∑' i, F v i)) := (hF v).hasSum
    exact hv.norm.pow 2
  refine le_of_tendsto' hlim fun S ↦ ?_
  refine (sum_norm_sq_jacobiSym_neg_le S m c (fun i _ ↦ hm i) K).trans ?_
  rw [← Finset.sum_product S S B]
  exact hB.sum_le_tsum _ fun p _ ↦ hB₀ p

end TauCeti
