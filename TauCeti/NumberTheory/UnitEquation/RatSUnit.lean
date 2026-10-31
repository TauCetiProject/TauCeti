/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SUnits.Rat.Structure

import TauCeti.Analysis.SpecialFunctions.Log.AddMulLog

/-!
# The exponent bound for the rational `S`-unit equation

Let `S` be a finite set of primes and `U_S` the rational `S`-units. This file bounds the
`p`-adic valuations of the solutions `(x, y) ∈ U_S × U_S` of the `S`-unit equation `x + y = 1`,
assuming a `p`-adic lower bound for linear forms in logarithms.

The lower bound is the hypothesis that there is `C ≥ 0` such that for every `p ∈ S`, every sign
`ε` and every exponent vector `b : S → ℤ` with `b p = 0`, the `p`-adic unit
`z = ε ∏_{q ∈ S} q ^ b q` satisfies
`|z - 1|_p ≥ (e · max(1, max_q |b q|)) ^ (-C)` unless `z = 1`.
Yu's theorem supplies such a constant `C`.

Under this hypothesis every solution satisfies
`|v_p(x)|, |v_p(y)| ≤ max(1, (2C / log 2) log(2C / log 2))` for every prime `p`
(`TauCeti.abs_padicValRat_le_of_add_eq_one`). For an explicit constant `C`, this places the
solutions in an explicit finite box of rational `S`-units.

The proof follows Evertse. Let `N` be the largest of the `|v_q(x)|` and `|v_q(y)|` for `q ∈ S`,
attained at the prime `p`. By the ultrametric inequality applied to `x + y = 1`, one of `y`,
`x` and `-x / y` is a `p`-adic unit `z` whose exponents are bounded by `N` and which satisfies
`|z - 1|_p = p ^ (-N)`. The lower bound then gives `N log p ≤ C (1 + log N)`.

## Main results

* `TauCeti.abs_padicValRat_le_of_add_eq_one`: the explicit bound for the valuations of the
  solutions of `x + y = 1` in rational `S`-units.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes for the Leiden/Mastermath course,
  2019 edition, Chapter 5, Theorem 5.17 and its proof, pp. 101–102.
-/

public section

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace TauCeti

variable {S : Finset ℕ}

/-- The lower bound for an `S`-unit `z ≠ 1` with `v_p(z) = 0` and all exponents bounded by `N`,
obtained by writing `z` as a signed product of powers of the primes of `S`. -/
private theorem rpow_neg_le_padicNorm_sub_one (hS : ∀ p ∈ S, p.Prime) {C : ℝ} (hC : 0 ≤ C)
    (hLB : ∀ p : S, ∀ (ε : ℤˣ) (b : S → ℤ), b p = 0 →
      (ε : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ b q ≠ 1 →
      (Real.exp 1 * max 1 ((Finset.univ.sup fun q ↦ (b q).natAbs : ℕ) : ℝ)) ^ (-C) ≤
        (padicNorm p ((ε : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ b q - 1) : ℝ))
    (p : S) {z : ℚˣ} (hz : z ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ)
    (hzp : padicValRat p (z : ℚ) = 0) (hz1 : (z : ℚ) ≠ 1) {N : ℕ}
    (hN : ∀ q ∈ S, (padicValRat q (z : ℚ)).natAbs ≤ N) :
    (Real.exp 1 * max 1 (N : ℝ)) ^ (-C) ≤ (padicNorm p ((z : ℚ) - 1) : ℝ) := by
  set w := sUnitsRatMulEquiv hS ⟨z, hz⟩
  have hzw : (z : ℚ) = (w.1 : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ w.2.toAdd q := by
    rw [← coe_sUnitsRatMulEquiv_symm_apply hS w, MulEquiv.symm_apply_apply]
  have hb (q : S) : w.2.toAdd q = padicValRat q (z : ℚ) :=
    toAdd_sUnitsRatMulEquiv_apply_snd hS _ q
  have h := hLB p w.1 w.2.toAdd (by rw [hb, hzp]) (hzw ▸ hz1)
  rw [← hzw] at h
  refine le_trans (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.2 hC)) h
  gcongr
  exact Finset.sup_le fun q _ ↦ hb q ▸ hN q q.2

/-- The key step: if `N` bounds all valuations of `x` and `y` at the primes of `S` and is
attained by `|v_p(x)|` with `N ≠ 0`, then `(e · max(1, N)) ^ (-C) ≤ p ^ (-N)`. -/
private theorem rpow_neg_le_zpow_neg (hS : ∀ p ∈ S, p.Prime) {C : ℝ} (hC : 0 ≤ C)
    (hLB : ∀ p : S, ∀ (ε : ℤˣ) (b : S → ℤ), b p = 0 →
      (ε : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ b q ≠ 1 →
      (Real.exp 1 * max 1 ((Finset.univ.sup fun q ↦ (b q).natAbs : ℕ) : ℝ)) ^ (-C) ≤
        (padicNorm p ((ε : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ b q - 1) : ℝ))
    {x y : ℚˣ} (hx : x ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ)
    (hy : y ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ)
    (hxy : (x : ℚ) + y = 1) {N : ℕ}
    (hNx : ∀ q ∈ S, (padicValRat q (x : ℚ)).natAbs ≤ N)
    (hNy : ∀ q ∈ S, (padicValRat q (y : ℚ)).natAbs ≤ N)
    (p : S) (hpN : (padicValRat p (x : ℚ)).natAbs = N) (hN : N ≠ 0) :
    (Real.exp 1 * max 1 (N : ℝ)) ^ (-C) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  have : Fact (p : ℕ).Prime := ⟨hS p p.2⟩
  have hx0 : (x : ℚ) ≠ 0 := x.ne_zero
  have hy0 : (y : ℚ) ≠ 0 := y.ne_zero
  have hv0 : padicValRat p (x : ℚ) ≠ 0 := by omega
  rcases lt_or_gt_of_ne hv0 with hneg | hpos
  · -- `v_p(x) < 0`: then `v_p(y) = v_p(x)`, and `z = -x / y` has `z - 1 = -1 / y`
    have hyx := padicValRat.eq_of_add_eq_one_of_neg hxy hneg
    have hdiv : ∀ q : ℕ, q.Prime →
        padicValRat q ((-x / y : ℚˣ) : ℚ) = padicValRat q (x : ℚ) - padicValRat q (y : ℚ) :=
      fun q hq ↦ by
        have : Fact q.Prime := ⟨hq⟩
        rw [Units.val_div_eq_div_val, Units.val_neg, padicValRat.div (neg_ne_zero.2 hx0) hy0,
          padicValRat.neg]
    have hz : -x / y ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ := by
      have hx' := (mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).1 hx
      have hy' := (mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).1 hy
      refine (mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).2
        fun q hq hqS ↦ ?_
      rw [hdiv q hq, hx' q hq hqS, hy' q hq hqS, sub_zero]
    have hz1 : ((-x / y : ℚˣ) : ℚ) ≠ 1 := by
      rw [Units.val_div_eq_div_val, Units.val_neg]
      refine div_ne_one_of_ne fun h ↦ ?_
      rw [← h, add_neg_cancel] at hxy
      exact zero_ne_one hxy
    have hbound : ∀ q ∈ S, (padicValRat q ((-x / y : ℚˣ) : ℚ)).natAbs ≤ N := by
      intro q hq
      have : Fact q.Prime := ⟨hS q hq⟩
      have h₁ := padicValRat.eq_zero_of_add_eq_one_of_pos (p := q) hxy
      have h₂ := padicValRat.eq_of_add_eq_one_of_neg (p := q) hxy
      have h₃ := padicValRat.eq_zero_of_add_eq_one_of_pos (p := q) ((add_comm _ _).trans hxy)
      have h₄ := padicValRat.eq_of_add_eq_one_of_neg (p := q) ((add_comm _ _).trans hxy)
      have := hNx q hq
      have := hNy q hq
      rw [hdiv q (hS q hq)]
      omega
    have h := rpow_neg_le_padicNorm_sub_one hS hC hLB p hz (by rw [hdiv p (hS p p.2)]; omega)
      hz1 hbound
    have hsub : ((-x / y : ℚˣ) : ℚ) - 1 = -(y : ℚ)⁻¹ := by
      rw [Units.val_div_eq_div_val, Units.val_neg]
      field_simp
      linarith
    have hvN : padicValRat p (x : ℚ) = -(N : ℤ) := by omega
    rwa [hsub, padicNorm.neg, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hy0), padicValRat.inv,
      neg_neg, hyx, hvN, Rat.cast_zpow, Rat.cast_natCast] at h
  · -- `v_p(x) > 0`: then `v_p(y) = 0`, and `z = y` has `z - 1 = -x`
    have hy1 : (y : ℚ) ≠ 1 := fun h ↦ hx0 (by linarith)
    have h := rpow_neg_le_padicNorm_sub_one hS hC hLB p hy
      (padicValRat.eq_zero_of_add_eq_one_of_pos hxy hpos) hy1 hNy
    have hsub : (y : ℚ) - 1 = -x := by linarith
    have hvN : padicValRat p (x : ℚ) = (N : ℤ) := by omega
    rwa [hsub, padicNorm.neg, padicNorm.eq_zpow_of_nonzero hx0, hvN, Rat.cast_zpow,
      Rat.cast_natCast] at h

/-- **The exponent bound for the rational `S`-unit equation** (Evertse, Theorem 5.17). Let `S` be
a finite set of primes and `C ≥ 0` a constant such that for every `p ∈ S`, every sign `ε` and every
`b : S → ℤ` with `b p = 0` and `z = ε ∏_{q ∈ S} q ^ b q ≠ 1`,
`|z - 1|_p ≥ (e · max(1, max_q |b q|)) ^ (-C)`. If `x` and `y` are rational `S`-units with
`x + y = 1`, then `|v_p(x)| ≤ max(1, (2C / log 2) log(2C / log 2))` for every prime `p`. The
same bound holds for `y`, by symmetry. -/
theorem abs_padicValRat_le_of_add_eq_one (hS : ∀ p ∈ S, p.Prime) {C : ℝ} (hC : 0 ≤ C)
    (hLB : ∀ p : S, ∀ (ε : ℤˣ) (b : S → ℤ), b p = 0 →
      (ε : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ b q ≠ 1 →
      (Real.exp 1 * max 1 ((Finset.univ.sup fun q ↦ (b q).natAbs : ℕ) : ℝ)) ^ (-C) ≤
        (padicNorm p ((ε : ℚ) * ∏ q : S, ((q : ℕ) : ℚ) ^ b q - 1) : ℝ))
    {x y : ℚˣ} (hx : x ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ)
    (hy : y ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ)
    (hxy : (x : ℚ) + y = 1) {p : ℕ} (hp : p.Prime) :
    (|padicValRat p (x : ℚ)| : ℝ) ≤ max 1 (2 * C / Real.log 2 * Real.log (2 * C / Real.log 2)) := by
  set N := S.sup fun q ↦ max (padicValRat q (x : ℚ)).natAbs (padicValRat q (y : ℚ)).natAbs
  have hNx (q : ℕ) (hq : q ∈ S) : (padicValRat q (x : ℚ)).natAbs ≤ N :=
    (le_max_left _ _).trans (Finset.le_sup (f := fun q ↦ max (padicValRat q (x : ℚ)).natAbs
      (padicValRat q (y : ℚ)).natAbs) hq)
  have hNy (q : ℕ) (hq : q ∈ S) : (padicValRat q (y : ℚ)).natAbs ≤ N :=
    (le_max_right _ _).trans (Finset.le_sup (f := fun q ↦ max (padicValRat q (x : ℚ)).natAbs
      (padicValRat q (y : ℚ)).natAbs) hq)
  -- every valuation of `x` is bounded by `N`
  have hpx : (|padicValRat p (x : ℚ)| : ℝ) ≤ N := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.cast_le]
    by_cases hpS : p ∈ S
    · exact hNx p hpS
    · rw [(mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).1 hx p hp hpS]
      exact Nat.zero_le _
  refine hpx.trans ?_
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0, Nat.cast_zero]
    exact le_max_of_le_left zero_le_one
  -- `N` is attained at some prime `q ∈ S`, by `x` or by `y`
  obtain ⟨q, hqS, hq⟩ := Finset.exists_mem_eq_sup S
    (Finset.nonempty_iff_ne_empty.2 fun h ↦ by simp [N, h] at hNpos)
    fun q ↦ max (padicValRat q (x : ℚ)).natAbs (padicValRat q (y : ℚ)).natAbs
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hS q hqS).two_le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have key : (Real.exp 1 * max 1 (N : ℝ)) ^ (-C) ≤ (q : ℝ) ^ (-(N : ℤ)) := by
    rcases le_total (padicValRat q (y : ℚ)).natAbs (padicValRat q (x : ℚ)).natAbs with h | h
    · exact rpow_neg_le_zpow_neg hS hC hLB hx hy hxy hNx hNy ⟨q, hqS⟩
        (hq.trans (max_eq_left h)).symm hNpos.ne'
    · exact rpow_neg_le_zpow_neg hS hC hLB hy hx ((add_comm _ _).trans hxy) hNy hNx ⟨q, hqS⟩
        (hq.trans (max_eq_right h)).symm hNpos.ne'
  rw [max_eq_right hN1, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast] at key
  -- `q ^ (-N) ≤ 2 ^ (-N)`, since `q ≥ 2`
  exact le_max_of_le_right (Real.le_mul_log_of_rpow_neg_le_rpow_neg hC one_lt_two
    (zero_lt_one.trans_le hN1)
    (key.trans (Real.rpow_le_rpow_of_nonpos two_pos hq2 (by linarith))))

end TauCeti
