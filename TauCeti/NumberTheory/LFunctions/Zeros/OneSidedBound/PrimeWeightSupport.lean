/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder

/-!
# Unit support of the quadratic prime weights

If all prime divisors of a modulus split in the quadratic field, the signed von Mangoldt
weights are supported on units modulo that modulus. At the cyclotomic level `q₁` this lets
one sum a place-dependent kernel using only the canonical unit labels, independently of
any total extension used at nonunits.

This is the support argument for `New.Data.primeSum` in `grh/src/New/Reduction/Data/AdmissibleData`
of [grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open ArithmeticFunction Finset

namespace TauCeti.OneSidedBound

/-- If every prime dividing `M` has Legendre symbol `1` at `d`, the signed von Mangoldt
weight vanishes on nonunits modulo `M`, regardless of the progression modulus `q`. -/
theorem primeWeight_eq_zero_of_not_coprime {d M q n : ℕ} [Fact d.Prime]
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ M → legendreSym d p = 1) (hn : ¬n.Coprime M) :
    primeWeight d q n = 0 := by
  rw [primeWeight_def]
  split_ifs
  · by_cases hpow : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
      have hdvd : p ∣ M := by
        rwa [Nat.coprime_pow_left_iff hk, hp.coprime_iff_not_dvd, not_not] at hn
      have hpow : legendreSym d (p ^ k : ℕ) = legendreSym d p ^ k := by
        simpa only [Nat.cast_pow, legendreSym.hom_apply] using map_pow (legendreSym.hom d) (p : ℤ) k
      rw [hpow, hsplit p hp hdvd, one_pow]
      simp
    · simp [vonMangoldt_eq_zero_iff.mpr hpow]
  · rfl

/-- The signed prime weights are supported on the unit classes of the cyclotomic level. -/
theorem Parameters.primeWeight_eq_zero_of_not_coprime_q₁ (P : Parameters) {q s n : ℕ}
    (hn : ¬n.Coprime (P.q₁ s)) : primeWeight P.d q n = 0 :=
  primeWeight_eq_zero_of_not_coprime (fun _ _ hp ↦ P.legendreSym_eq_one_of_dvd_q₁ hp) hn

/-- Sum a kernel against the signed prime weight using genuine cyclotomic unit labels only.
A total label `label` agreeing with the canonical class at coprime inputs gives the same sum
as restricting the indices first; in particular the value of the label at nonunits is immaterial. -/
theorem Parameters.sum_primeWeight_mul_eq_sum_subtype_coprime (P : Parameters) (q s : ℕ)
    (A : Finset ℕ) (f : ℕ → (ZMod (P.q₁ s))ˣ → ℝ) (label : ℕ → (ZMod (P.q₁ s))ˣ)
    (hlabel : ∀ n ∈ A, ∀ hn : n.Coprime (P.q₁ s), label n = ZMod.unitOfCoprime n hn) :
    ∑ n ∈ A, primeWeight P.d q n * f n (label n) =
      ∑ n ∈ A.subtype (fun n ↦ n.Coprime (P.q₁ s)),
        primeWeight P.d q n * f n (ZMod.unitOfCoprime n n.property) := by
  calc
    _ = ∑ n ∈ A.filter (fun n ↦ n.Coprime (P.q₁ s)),
        primeWeight P.d q n * f n (label n) := by
      symm
      refine sum_subset (filter_subset ..) fun n hn hnot ↦ ?_
      rw [P.primeWeight_eq_zero_of_not_coprime_q₁ (fun hn' ↦ hnot (mem_filter.mpr ⟨hn, hn'⟩)),
        zero_mul]
    _ = ∑ n ∈ A.subtype (fun n ↦ n.Coprime (P.q₁ s)),
        primeWeight P.d q n * f n (label n) := by
      exact (sum_subtype_eq_sum_filter (s := A) (fun n ↦ primeWeight P.d q n * f n (label n))).symm
    _ = _ := sum_congr rfl fun n hn ↦ by rw [hlabel n (mem_subtype.mp hn) n.property]

end TauCeti.OneSidedBound
