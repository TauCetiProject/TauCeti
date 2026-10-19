/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.Data.ZMod.Count
import TauCeti.Data.ZMod.LocalRing
import TauCeti.Data.ZMod.PrincipalUnits
import TauCeti.NumberTheory.LegendreSymbol.NegThree

/-!
# Counting solutions of the congruences `x² + 1 ≡ 0` and `x² - x + 1 ≡ 0`

For an odd prime `p` and an integer `a` prime to `p`, reduction modulo `p` is a bijection from the
square roots of `a` modulo `p ^ k` (`k ≥ 1`) to those modulo `p`, by Hensel's lemma. So their
number is `1 + (a | p)` at every level `p ^ k`.

Combined with the Chinese remainder theorem this counts the solutions of `x² + 1 ≡ 0 (mod N)` and
of `x² - x + 1 ≡ 0 (mod N)`. Away from `2`, the first congruence asks for a square root of `-1`;
completing the square, `4 (x² - x + 1) = (2 x - 1)² + 3`, the second asks away from `2` for a
square root of `-3`, and `(-3 | p) = (p | 3)`. The primes `2` and `3`, where the discriminants
`-4` and `-3` are not prime to `p`, are computed directly: `x² + 1 ≡ 0` has one solution modulo
`2` and none modulo `4`, and `x² - x + 1 ≡ 0` has none modulo `2`, one modulo `3` and none modulo
`9`. The resulting counts are

* `#{x mod N | x² + 1 = 0} = 0` if `4 ∣ N`, and `∏_{p ∣ N} (1 + χ₄(p))` otherwise;
* `#{x mod N | x² - x + 1 = 0} = 0` if `9 ∣ N`, and `∏_{p ∣ N} (1 + (p | 3))` otherwise,

where `χ₄` is the character of `ℤ/4ℤ`, so that `χ₄(p) = (-1 | p)` for odd `p` and `χ₄(2) = 0`.
They hold also for `N = 0`, as neither polynomial has an integer root. These are the numbers of
elliptic points of order two and three of `Γ₀(N)`.

## Main results

* `TauCeti.ZMod.exists_sq_eq_and_castHom_eq`: Hensel's lemma for square roots of a unit modulo
  an odd prime power.
* `TauCeti.ZMod.natCard_sq_eq_prime_pow_eq_natCard_sq_eq_prime`: the same, as an equality of
  counts.
* `TauCeti.ZMod.natCard_sq_eq_prime_pow_eq_legendreSym_add_one`: the count `1 + (a | p)` of
  square roots of a unit `a` modulo `p ^ k`.
* `TauCeti.ZMod.natCard_sq_add_one_eq_zero`: the number of roots of `x² + 1` modulo `N`.
* `TauCeti.ZMod.natCard_sq_sub_self_add_one_eq_zero`: the number of roots of `x² - x + 1` modulo
  `N`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Corollary 3.7.2.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Proposition 1.43.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 4, §2.
-/

public section

namespace TauCeti.ZMod

variable {p : ℕ} [Fact p.Prime]

/-! ### Square roots modulo odd prime powers -/

/-- **Hensel's lemma for square roots.** For an odd prime `p`, a square root `z` modulo `p` of an
integer `a` prime to `p` lifts to a square root of `a` modulo `p ^ k`, for every `k ≠ 0`. -/
theorem exists_sq_eq_and_castHom_eq (hp : p ≠ 2) {k : ℕ} (hk : k ≠ 0) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) {z : ZMod p} (hz : z ^ 2 = a) :
    ∃ x : ZMod (p ^ k), x ^ 2 = a ∧ ZMod.castHom (dvd_pow_self p hk) (ZMod p) x = z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hdvd : p ∣ p ^ (k + 1) := dvd_pow_self p hk
  set π := ZMod.castHom hdvd (ZMod p)
  have hunit (x : ZMod (p ^ (k + 1))) : IsUnit x ↔ π x ≠ 0 :=
    ZMod.isUnit_prime_pow_iff_castHom_ne_zero p (k + 1) k.succ_pos x
  have hπa : π a = a := map_intCast π a
  have hz0 : z ≠ 0 := fun h0 ↦ ha (by rw [← hz, h0, zero_pow two_ne_zero])
  -- Lift `z` to a unit `x₀`. Then `u = a / x₀²` is a unit congruent to one, so it has a square
  -- root `v` congruent to one, and `x₀ v` is a square root of `a` lifting `z`.
  set x₀ : ZMod (p ^ (k + 1)) := (z.val : ZMod (p ^ (k + 1))) with hx₀
  have hπx₀ : π x₀ = z := by rw [hx₀, map_natCast, ZMod.natCast_zmod_val]
  have hux₀ : IsUnit x₀ := (hunit x₀).mpr (hπx₀ ▸ hz0)
  have hua : IsUnit (a : ZMod (p ^ (k + 1))) := (hunit _).mpr (hπa ▸ ha)
  set u : (ZMod (p ^ (k + 1)))ˣ := hua.unit * (hux₀.unit⁻¹) ^ 2 with hu
  have hunitsMap (w : (ZMod (p ^ (k + 1)))ˣ) : (ZMod.unitsMap hdvd w : ZMod p) = π w := by
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_ofClass]
  have hu1 : ZMod.unitsMap hdvd u = 1 := by
    have hinv : π (↑hux₀.unit⁻¹ : ZMod (p ^ (k + 1))) * z = 1 := by
      rw [← hπx₀, ← map_mul, hux₀.val_inv_mul, map_one]
    ext
    rw [hunitsMap, Units.val_one, hu, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
      IsUnit.unit_spec, hπa, ← hz]
    linear_combination (π (↑hux₀.unit⁻¹ : ZMod (p ^ (k + 1))) * z + 1) * hinv
  obtain ⟨v, ⟨hv1, hv⟩, -⟩ := ZMod.existsUnique_pow_eq_of_unitsMap_eq_one (Fact.out : p.Prime)
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp)) hu1
  refine ⟨x₀ * v, ?_, ?_⟩
  · have := congrArg Units.val hv
    rw [Units.val_pow_eq_pow_val, hu, Units.val_mul, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec] at this
    rw [mul_pow, this]
    linear_combination (a : ZMod (p ^ (k + 1))) * (↑hux₀.unit⁻¹ * x₀ + 1) * hux₀.val_inv_mul
  · have := congrArg Units.val hv1
    rw [hunitsMap, Units.val_one] at this
    rw [map_mul, hπx₀, this, mul_one]

/-- **Hensel's lemma for square roots, as a count.** For an odd prime `p`, an integer `a` prime to
`p` and `k ≠ 0`, reduction modulo `p` is a bijection from the square roots of `a` modulo `p ^ k`
to those modulo `p`; so there are equally many. -/
theorem natCard_sq_eq_prime_pow_eq_natCard_sq_eq_prime (hp : p ≠ 2) {k : ℕ} (hk : k ≠ 0) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    Nat.card {x : ZMod (p ^ k) // x ^ 2 = a} = Nat.card {x : ZMod p // x ^ 2 = a} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  set π := ZMod.castHom (dvd_pow_self p hk) (ZMod p)
  have hπa : π a = a := map_intCast π a
  refine Finset.card_bij (fun x _ ↦ π x) (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_) (fun z hz ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← map_pow, hx, hπa]
  · -- Two square roots of `a` with the same reduction differ by a factor of `x + y ≡ 2 x`, a unit.
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hsum : IsUnit (x + y) := by
      rw [ZMod.isUnit_prime_pow_iff_castHom_ne_zero p k (Nat.pos_of_ne_zero hk), map_add, ← hxy,
        ← two_mul]
      refine mul_ne_zero (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])) fun h0 ↦ ha ?_
      rw [← hπa, ← hx, map_pow, h0, zero_pow two_ne_zero]
    have hprod : (x - y) * (x + y) = 0 := by linear_combination hx - hy
    exact sub_eq_zero.mp ((hsum.mul_left_eq_zero).mp hprod)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨x, hx, hxz⟩ := exists_sq_eq_and_castHom_eq hp hk ha hz
    exact ⟨x, by simpa using hx, hxz⟩

/-- **Square roots modulo odd prime powers.** For an odd prime `p`, an integer `a` prime to `p`
and `k ≠ 0`, the number of square roots of `a` modulo `p ^ k` is `1 + (a | p)`. -/
theorem natCard_sq_eq_prime_pow_eq_legendreSym_add_one (hp : p ≠ 2) {k : ℕ} (hk : k ≠ 0) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    (Nat.card {x : ZMod (p ^ k) // x ^ 2 = a} : ℤ) = legendreSym p a + 1 := by
  classical
  rw [natCard_sq_eq_prime_pow_eq_natCard_sq_eq_prime hp hk ha, legendreSym,
    ← quadraticChar_card_sqrts (by rwa [ZMod.ringChar_zmod_n]), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Set.toFinset_ofPred]

/-! ### The congruence `x² + 1 ≡ 0` -/

/-- Modulo an odd prime power `p ^ k`, `k ≠ 0`, the polynomial `x² + 1` has `1 + χ₄(p)` roots. -/
theorem natCard_sq_add_one_eq_zero_prime_pow (hp : p ≠ 2) {k : ℕ} (hk : k ≠ 0) :
    (Nat.card {x : ZMod (p ^ k) // x ^ 2 + 1 = 0} : ℤ) = 1 + ZMod.χ₄ p := by
  have hneg : Nat.card {x : ZMod (p ^ k) // x ^ 2 + 1 = 0} =
      Nat.card {x : ZMod (p ^ k) // x ^ 2 = ((-1 : ℤ) : ZMod (p ^ k))} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by push_cast; exact add_eq_zero_iff_eq_neg)
  rw [hneg, natCard_sq_eq_prime_pow_eq_legendreSym_add_one hp hk
    (by push_cast; exact neg_ne_zero.mpr one_ne_zero), _root_.legendreSym.at_neg_one hp, add_comm]

/-- **Square roots of `-1` modulo `N`.** The polynomial `x² + 1` has no roots modulo `N` if
`4 ∣ N`, and otherwise `∏_{p ∣ N} (1 + χ₄(p))` roots, where `χ₄(p) = (-1 | p)` for odd `p` and
`χ₄(2) = 0`. -/
theorem natCard_sq_add_one_eq_zero (N : ℕ) :
    (Nat.card {x : ZMod N // x ^ 2 + 1 = 0} : ℤ) =
      if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p) := by
  have h4' : ∀ y : ZMod 4, y ^ 2 + 1 ≠ 0 := by decide
  rcases eq_or_ne N 0 with rfl | hN
  · have : IsEmpty {x : ZMod 0 // x ^ 2 + 1 = 0} :=
      ⟨fun ⟨x, hx⟩ ↦ (fun y : ℤ ↦ by positivity : ∀ y : ℤ, y ^ 2 + 1 ≠ 0) x hx⟩
    simp [Nat.card_of_isEmpty]
  have hcrt := ZMod.natCard_aeval_eq_zero_eq_prod_primeFactors hN (.X ^ 2 + 1)
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one] at hcrt
  have h4 : 4 ∣ N ↔ 2 ≤ N.factorization 2 := by
    rw [show 4 = 2 ^ 2 by norm_num]
    exact Nat.prime_two.pow_dvd_iff_le_factorization hN
  rw [hcrt, Nat.cast_prod]
  split_ifs with hN4
  · -- Modulo `4`, and hence modulo `2 ^ v₂(N)`, the polynomial `x² + 1` has no roots.
    refine Finset.prod_eq_zero (i := 2)
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, (by norm_num : 2 ∣ 4).trans hN4, hN⟩) ?_
    have hdvd : 4 ∣ 2 ^ N.factorization 2 := pow_dvd_pow 2 (h4.mp hN4)
    have : IsEmpty {x : ZMod (2 ^ N.factorization 2) // x ^ 2 + 1 = 0} :=
      ⟨fun ⟨x, hx⟩ ↦ h4' (ZMod.castHom hdvd _ x) (by
        rw [← map_pow, ← map_one (ZMod.castHom hdvd _), ← map_add, hx, map_zero])⟩
    simp
  · refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hk : N.factorization p ≠ 0 :=
      (hpp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp)).ne'
    rcases eq_or_ne p 2 with rfl | hp2
    · rw [show N.factorization 2 = 1 by omega, pow_one, Nat.card_eq_fintype_card]
      decide
    · exact natCard_sq_add_one_eq_zero_prime_pow hp2 hk

/-! ### The congruence `x² - x + 1 ≡ 0` -/

/-- Modulo a power `p ^ k`, `k ≠ 0`, of a prime `p ≠ 2, 3`, the polynomial `x² - x + 1` has
`1 + (p | 3)` roots. -/
theorem natCard_sq_sub_self_add_one_eq_zero_prime_pow (hp2 : p ≠ 2) (hp3 : p ≠ 3) {k : ℕ}
    (hk : k ≠ 0) :
    (Nat.card {x : ZMod (p ^ k) // x ^ 2 - x + 1 = 0} : ℤ) = 1 + legendreSym 3 p := by
  have h2 : IsUnit (2 : ZMod (p ^ k)) := by
    rw [ZMod.isUnit_prime_pow_iff_castHom_ne_zero p k (Nat.pos_of_ne_zero hk), map_ofNat]
    exact Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  -- Completing the square: `x ↦ 2 x - 1` carries the roots of `x² - x + 1` to the square roots
  -- of `-3`, since `(2 x - 1)² + 3 = 4 (x² - x + 1)`.
  have hsq : Nat.card {x : ZMod (p ^ k) // x ^ 2 - x + 1 = 0} =
      Nat.card {y : ZMod (p ^ k) // y ^ 2 = ((-3 : ℤ) : ZMod (p ^ k))} := by
    refine Nat.card_congr (((Units.mulLeft h2.unit).trans (Equiv.subRight 1)).subtypeEquiv
      fun x ↦ ?_)
    simp only [Equiv.trans_apply, Units.mulLeft_apply, IsUnit.unit_spec, Equiv.subRight_apply]
    push_cast
    refine ⟨fun h ↦ by linear_combination 4 * h, fun h ↦ ?_⟩
    exact ((h2.mul h2).mul_right_eq_zero).mp (by linear_combination h)
  have ha : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_neg]
    exact_mod_cast fun h ↦ hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h)
  rw [hsq, natCard_sq_eq_prime_pow_eq_legendreSym_add_one hp2 hk ha,
    TauCeti.legendreSym.at_neg_three hp2, add_comm]

/-- **Primitive cube roots of unity modulo `N`.** The polynomial `x² - x + 1` has no roots modulo
`N` if `9 ∣ N`, and otherwise `∏_{p ∣ N} (1 + (p | 3))` roots. The factor `1 + (p | 3)` is `0` at
`p = 2`, `1` at `p = 3`, and `1 + (-3 | p)` at every other prime. -/
theorem natCard_sq_sub_self_add_one_eq_zero (N : ℕ) :
    (Nat.card {x : ZMod N // x ^ 2 - x + 1 = 0} : ℤ) =
      if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p) := by
  have h2 : ∀ y : ZMod 2, y ^ 2 - y + 1 ≠ 0 := by decide
  have h9 : ∀ y : ZMod 9, y ^ 2 - y + 1 ≠ 0 := by decide
  rcases eq_or_ne N 0 with rfl | hN
  · have : IsEmpty {x : ZMod 0 // x ^ 2 - x + 1 = 0} :=
      ⟨fun ⟨x, hx⟩ ↦ (fun y : ℤ ↦ by nlinarith [sq_nonneg (2 * y - 1)] :
        ∀ y : ℤ, y ^ 2 - y + 1 ≠ 0) x hx⟩
    simp [Nat.card_of_isEmpty]
  have hcrt := ZMod.natCard_aeval_eq_zero_eq_prod_primeFactors hN (.X ^ 2 - .X + 1)
  simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, map_one] at hcrt
  have h9N : 9 ∣ N ↔ 2 ≤ N.factorization 3 := by
    rw [show 9 = 3 ^ 2 by norm_num]
    exact Nat.prime_three.pow_dvd_iff_le_factorization hN
  rw [hcrt, Nat.cast_prod]
  split_ifs with hN9
  · -- Modulo `9`, and hence modulo `3 ^ v₃(N)`, the polynomial `x² - x + 1` has no roots.
    refine Finset.prod_eq_zero (i := 3)
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, (by norm_num : 3 ∣ 9).trans hN9, hN⟩) ?_
    have hdvd : 9 ∣ 3 ^ N.factorization 3 := pow_dvd_pow 3 (h9N.mp hN9)
    have : IsEmpty {x : ZMod (3 ^ N.factorization 3) // x ^ 2 - x + 1 = 0} :=
      ⟨fun ⟨x, hx⟩ ↦ h9 (ZMod.castHom hdvd _ x) (by
        rw [← map_pow, ← map_one (ZMod.castHom hdvd _), ← map_sub, ← map_add, hx, map_zero])⟩
    simp
  · refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hk : N.factorization p ≠ 0 :=
      (hpp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp)).ne'
    rcases eq_or_ne p 2 with rfl | hp2
    · -- Modulo `2`, and hence modulo `2 ^ v₂(N)`, the polynomial `x² - x + 1` has no roots.
      have hdvd : 2 ∣ 2 ^ N.factorization 2 := dvd_pow_self 2 hk
      have : IsEmpty {x : ZMod (2 ^ N.factorization 2) // x ^ 2 - x + 1 = 0} :=
        ⟨fun ⟨x, hx⟩ ↦ h2 (ZMod.castHom hdvd _ x) (by
          rw [← map_pow, ← map_one (ZMod.castHom hdvd _), ← map_sub, ← map_add, hx, map_zero])⟩
      rw [Nat.card_of_isEmpty, Nat.cast_zero, Nat.cast_ofNat,
        _root_.legendreSym.at_two (p := 3) (by norm_num)]
      decide
    rcases eq_or_ne p 3 with rfl | hp3
    · rw [show N.factorization 3 = 1 by omega, pow_one, Nat.card_eq_fintype_card]
      decide
    · exact natCard_sq_sub_self_add_one_eq_zero_prime_pow hp2 hp3 hk

end TauCeti.ZMod
