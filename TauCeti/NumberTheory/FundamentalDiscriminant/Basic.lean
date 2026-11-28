/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.Data.Nat.Squarefree
import TauCeti.Algebra.Squarefree
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Fundamental discriminants: basic API

Generic facts about Mathlib's `Int.IsFundamentalDiscr`, independent of any quadratic-field or
prime-discriminant theory.

## Main results

* `Int.decidablePredIsFundamentalDiscr`: being a fundamental discriminant is decidable, through
  congruences mod `4` and squarefreeness of natural numbers, so the kernel can check it.
* `Int.isFundamentalDiscr_one`, `Int.IsFundamentalDiscr.natAbs_eq_one_iff`: `1` is the unique
  fundamental discriminant of absolute value `1`.
* `Int.IsFundamentalDiscr.not_sixteen_dvd`: a fundamental discriminant is not divisible by `16`.
* `Int.IsFundamentalDiscr.mul`: coprime fundamental discriminants have fundamental product.
* `Int.IsFundamentalDiscr.not_isSquare_rat`: a fundamental discriminant other than `1` is not a
  rational square, so `ℚ(√D)` is a genuine quadratic field.
* `Int.exists_isFundamentalDiscr_eq_sq_mul`: every nonzero discriminant `D ≡ 0, 1 (mod 4)` is
  `f² D₀` for a fundamental discriminant `D₀`.
* `Int.IsFundamentalDiscr.eq_neg_four_or_eq_neg_eight_or_exists_prime_of_card_primeFactors_eq_one`:
  a negative fundamental discriminant with a single prime factor is `-4`, `-8` or `-p` for a prime
  `p ≡ 3 (mod 4)`.
-/

public section

namespace Int

/-- Being a fundamental discriminant is decidable: by `Int.isFundamentalDiscr_iff_squarefree` it
comes down to congruences mod `4` and the squarefreeness of natural numbers. -/
instance decidablePredIsFundamentalDiscr : DecidablePred IsFundamentalDiscr := fun D =>
  decidable_of_iff ((D % 4 = 1 ∧ Squarefree D.natAbs) ∨
      (D % 4 = 0 ∧ Squarefree (D / 4).natAbs ∧ (D / 4 % 4 = 2 ∨ D / 4 % 4 = 3))) <| by
    rw [isFundamentalDiscr_iff_squarefree, squarefree_natAbs, squarefree_natAbs]

/-- `1` is a fundamental discriminant, corresponding to the trivial quadratic extension. -/
@[simp]
theorem isFundamentalDiscr_one : IsFundamentalDiscr 1 :=
  isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨rfl, squarefree_one⟩)

/-- Among fundamental discriminants, `1` is the only one of absolute value `1`, since `-1 ≡ 3`
modulo `4`. -/
theorem IsFundamentalDiscr.natAbs_eq_one_iff {D : ℤ} (hD : IsFundamentalDiscr D) :
    D.natAbs = 1 ↔ D = 1 := by
  refine ⟨fun h ↦ (Int.natAbs_eq_iff.mp h).resolve_right fun hneg ↦ ?_, fun h ↦ by simp [h]⟩
  have := hD.emod_four_eq_zero_or_one
  omega

/-- The absolute value of a fundamental discriminant is a nonzero Dirichlet-character level. -/
theorem IsFundamentalDiscr.neZero_natAbs {D : ℤ} (hD : IsFundamentalDiscr D) :
    NeZero D.natAbs :=
  ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩

/-- A fundamental discriminant is not divisible by `16`: it is odd, or `4 * x` with `4 ∤ x`. -/
theorem IsFundamentalDiscr.not_sixteen_dvd {D : ℤ} (hD : IsFundamentalDiscr D) :
    ¬ (16 : ℤ) ∣ D := by
  rintro ⟨k, hk⟩
  exact (hD.2.1 (4 * k) (by omega)).1 ⟨k, rfl⟩

/-- A product of coprime fundamental discriminants is a fundamental discriminant. -/
theorem IsFundamentalDiscr.mul {D E : ℤ} (hD : IsFundamentalDiscr D)
    (hE : IsFundamentalDiscr E) (hcop : IsCoprime D E) : IsFundamentalDiscr (D * E) := by
  wlog hDodd : D % 4 = 1 generalizing D E
  · have hEodd : E % 4 = 1 := by
      by_contra hEodd
      have hD4 : (4 : ℤ) ∣ D :=
        Int.dvd_of_emod_eq_zero (hD.emod_four_eq_zero_or_one.resolve_right hDodd)
      have hE4 : (4 : ℤ) ∣ E :=
        Int.dvd_of_emod_eq_zero (hE.emod_four_eq_zero_or_one.resolve_right hEodd)
      have := hcop.isUnit_of_dvd' hD4 hE4
      norm_num [Int.isUnit_iff] at this
    simpa only [mul_comm] using this hE hD hcop.symm hEodd
  have hDsf : Squarefree D :=
    (isFundamentalDiscr_iff_squarefree.mp hD).resolve_right (by omega) |>.2
  rcases isFundamentalDiscr_iff_squarefree.mp hE with ⟨hEodd, hEsf⟩ | ⟨hE4, hEsf, hEmod⟩
  · exact isFundamentalDiscr_iff_squarefree.mpr <| Or.inl
      ⟨by rw [Int.mul_emod, hDodd, hEodd]; norm_num,
        squarefree_mul_iff.mpr ⟨hcop.isRelPrime, hDsf, hEsf⟩⟩
  · obtain ⟨e, rfl⟩ : (4 : ℤ) ∣ E := Int.dvd_of_emod_eq_zero hE4
    simp only [Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)] at hEsf hEmod
    rw [mul_left_comm D 4 e, isFundamentalDiscr_four_mul]
    refine ⟨squarefree_mul_iff.mpr
      ⟨(hcop.of_isCoprime_of_dvd_right (dvd_mul_left e 4)).isRelPrime, hDsf, hEsf⟩, ?_⟩
    simpa only [Int.mul_emod, hDodd, one_mul, Int.emod_emod] using hEmod

/-- A fundamental discriminant other than `1` is not a rational square. Consequently `ℚ(√D)` is a
genuine quadratic field: this is what keeps the genus-field constructions non-degenerate. -/
theorem IsFundamentalDiscr.not_isSquare_rat {D : ℤ} (hD : IsFundamentalDiscr D)
    (h1 : D ≠ 1) : ¬ IsSquare ((D : ℤ) : ℚ) := by
  rcases isFundamentalDiscr_iff_squarefree.mp hD with ⟨-, hsf⟩ | ⟨h0, hmsf, hm4⟩
  · exact not_isSquare_intCast_of_squarefree_of_ne_one hsf h1
  · obtain ⟨m, rfl⟩ : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero h0
    rw [Int.mul_ediv_cancel_left m four_ne_zero] at hmsf hm4
    have hm1 : m ≠ 1 := by rcases hm4 with h | h <;> omega
    have hcast : ((4 * m : ℤ) : ℚ) = 4 * ((m : ℤ) : ℚ) := by push_cast; ring
    rw [hcast]
    exact fun h => not_isSquare_intCast_of_squarefree_of_ne_one hmsf hm1
      (by simpa using h.div (⟨2, by norm_num⟩ : IsSquare (4 : ℚ)))

/-- **Every nonzero discriminant is a square times a fundamental discriminant.** If
`D ≡ 0, 1 (mod 4)` and `D ≠ 0`, then `D = f² D₀` for a natural number `f` and a fundamental
discriminant `D₀`. Write `D = a b²` with `a` squarefree: if `a ≡ 1 (mod 4)` take `D₀ = a`;
otherwise `a ≡ 2, 3 (mod 4)` forces `b` to be even, and `D₀ = 4 a`. -/
theorem exists_isFundamentalDiscr_eq_sq_mul {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hD₀ : D ≠ 0) : ∃ (f : ℕ) (D₀ : ℤ), IsFundamentalDiscr D₀ ∧ D = f ^ 2 * D₀ := by
  obtain ⟨a, b, ha, -, rfl⟩ := Int.exists_squarefree_mul_sq hD₀
  by_cases ha1 : a % 4 = 1
  · exact ⟨b.natAbs, a, isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨ha1, ha⟩),
      by rw [Int.natAbs_sq, mul_comm]⟩
  have ha23 := TauCeti.Int.emod_four_eq_two_or_three_of_squarefree ha ha1
  obtain ⟨c, rfl⟩ : 2 ∣ b := by
    by_contra hb
    have hsq := Int.sq_emod_four b
    have hb2 : b % 2 = 1 := by omega
    rw [Int.mul_emod, hsq, hb2, mul_one, Int.emod_emod] at hD
    omega
  exact ⟨c.natAbs, 4 * a, isFundamentalDiscr_four_mul.mpr ⟨ha, ha23⟩,
    by rw [Int.natAbs_sq]; ring⟩

/-- **Negative fundamental discriminants with one prime factor.** A negative fundamental
discriminant divisible by exactly one prime is `-4`, `-8`, or `-p` for a prime `p ≡ 3 (mod 4)`:
in the odd case `D` is squarefree, so `|D|` is that prime, and `D ≡ 1 (mod 4)` forces
`p ≡ 3 (mod 4)`; in the even case `D = 4m` with `m` squarefree and `2` the only prime dividing it,
so `m ∈ {-1, -2}`. -/
theorem IsFundamentalDiscr.eq_neg_four_or_eq_neg_eight_or_exists_prime_of_card_primeFactors_eq_one
    {D : ℤ} (hD : IsFundamentalDiscr D) (hneg : D < 0) (ht : D.natAbs.primeFactors.card = 1) :
    D = -4 ∨ D = -8 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ D = -p := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp ht
  rcases isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, hsf⟩ | ⟨h0, hsf, -⟩
  · -- `D ≡ 1 (mod 4)` is squarefree, so `|D|` is the product of its single prime factor.
    have habs : D.natAbs = p := by
      rw [← Nat.prod_primeFactors_of_squarefree (squarefree_natAbs.mpr hsf), hp,
        Finset.prod_singleton]
    exact Or.inr (Or.inr ⟨p, Nat.prime_of_mem_primeFactors (hp ▸ Finset.mem_singleton_self p),
      by omega, by omega⟩)
  · -- `D = 4m` with `m` squarefree: the prime factors of `|m|` lie among those of `|D|`, that is
    -- `{2}`, so the squarefree `|m|` is `1` or `2`.
    have h2 : 2 ∈ D.natAbs.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, by omega⟩
    rw [hp, Finset.mem_singleton] at h2
    have hsub : (D / 4).natAbs.primeFactors ⊆ {2} := by
      rw [h2, ← hp]
      exact Nat.primeFactors_mono ⟨4, by omega⟩ (by omega)
    have habs := Nat.prod_primeFactors_of_squarefree (squarefree_natAbs.mpr hsf)
    rcases Finset.subset_singleton_iff.mp hsub with h | h <;>
      rw [h] at habs <;> simp only [Finset.prod_empty, Finset.prod_singleton] at habs <;> omega

end Int
