/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Auxiliary prime pairs for cyclic CM hosts

The primes `q` and `d` used to build a cyclic CM host are chosen so that `q` and the primes
up to a cutoff `B` split in `ℚ(√−d)`. We express splitting by the value of the Kronecker
symbol. The dyadic bounds on `q + 1` and `d + 1` control how far up the cyclotomic tower one
must go. For `q ≡ 3 (mod 8)` and dyadic bound `3`, the possible second primes form one
reduced residue class. Its modulus uses an lcm so that `q ≤ B` does not impose divisibility
by `q²`.

The congruence conditions for the sharp pair are those of Levent Alpöge's formalization of the
Riemann hypothesis for Dirichlet L-functions, `GlobalTheory.EX.PairRow`.
-/

public section

namespace TauCeti

/-- A `(B, a)`-admissible auxiliary pair consists of primes `q ≡ 3 (mod 4)` and
`d ≡ 7 (mod 8)` with dyadic valuations of `q + 1` and `d + 1` at most `a`. Both `q` and each
odd prime at most `B` divide `d + 1`. -/
structure IsAdmissibleAuxiliaryPair (B : ℝ) (a q d : ℕ) : Prop where
  q_prime : q.Prime
  d_prime : d.Prime
  q_mod_four : q % 4 = 3
  d_mod_eight : d % 8 = 7
  q_multiplicity_le : multiplicity 2 (q + 1) ≤ a
  d_multiplicity_le : multiplicity 2 (d + 1) ≤ a
  q_dvd : q ∣ d + 1
  prime_dvd : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ B → p ∣ d + 1

namespace IsAdmissibleAuxiliaryPair

variable {B : ℝ} {a q d : ℕ}

/-- The second prime of an admissible pair is odd. -/
theorem d_ne_two (h : IsAdmissibleAuxiliaryPair B a q d) : d ≠ 2 := by
  have := h.d_mod_eight
  omega

/-- The prime `d` is larger than the cutoff of an admissible pair. -/
theorem lt_d (h : IsAdmissibleAuxiliaryPair B a q d) : B < (d : ℝ) := by
  by_contra! hd
  exact h.d_prime.not_dvd_one
    ((Nat.dvd_add_right dvd_rfl).mp (h.prime_dvd d h.d_prime h.d_ne_two hd))

/-- The second prime is at least `23`, independently of the cutoff. -/
theorem twenty_three_le_d (h : IsAdmissibleAuxiliaryPair B a q d) : 23 ≤ d := by
  have hq4 := h.q_mod_four
  have h8 : 8 ∣ d + 1 := by have := h.d_mod_eight; omega
  have hq : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have hcop : Nat.Coprime 8 q := (Nat.coprime_pow_left_iff (by decide : 0 < 3) _ _).mpr hq
  have := Nat.le_of_dvd (Nat.succ_pos d) (hcop.mul_dvd_of_dvd_of_dvd h8 h.q_dvd)
  omega

/-- The second prime does not divide a level all of whose odd prime factors are at most `B`. -/
theorem not_d_dvd (h : IsAdmissibleAuxiliaryPair B a q d) {f : ℕ}
    (hf : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ f → (p : ℝ) ≤ B) : ¬ d ∣ f :=
  fun hd ↦ h.lt_d.not_ge (hf d h.d_prime h.d_ne_two hd)

/-- The two primes of an admissible pair are distinct. -/
theorem q_ne_d (h : IsAdmissibleAuxiliaryPair B a q d) : q ≠ d := by
  rintro rfl
  exact h.q_prime.not_dvd_one ((Nat.dvd_add_right dvd_rfl).mp h.q_dvd)

/-- The odd prime `q` and each prime up to `B` have Kronecker symbol `1` for the
quadratic discriminant `−d`. -/
theorem kroneckerSym_eq_one (h : IsAdmissibleAuxiliaryPair B a q d) {p : ℕ}
    (hp : p.Prime) (hpq : p = q ∨ (p : ℝ) ≤ B) : kroneckerSym (-(d : ℤ)) p = 1 := by
  by_cases hp2 : p = 2
  · subst p
    have hmod : (-(d : ℤ)) % 8 = 1 := by have := h.d_mod_eight; omega
    rw [Nat.cast_ofNat, kroneckerSym_two_right, ZMod.χ₈_int_mod_eight (-(d : ℤ)), hmod]
    decide
  · have hdiv : p ∣ d + 1 := hpq.elim (fun he ↦ he.symm ▸ h.q_dvd) (h.prime_dvd p hp hp2)
    have hmod : -(d : ℤ) ≡ 1 [ZMOD (p : ℤ)] := by
      rw [Int.modEq_iff_dvd, sub_neg_eq_add, add_comm]
      exact_mod_cast hdiv
    rw [kroneckerSym_eq_jacobiSym _ (hp.odd_of_ne_two hp2), jacobiSym.mod_left' hmod,
      jacobiSym.one_left]

/-- The dyadic valuation of `q + 1` is at least two. -/
theorem two_le_q_multiplicity (h : IsAdmissibleAuxiliaryPair B a q d) :
    2 ≤ multiplicity 2 (q + 1) := by
  apply (Nat.pow_dvd_iff_le_multiplicity (by decide) (Nat.succ_ne_zero q)).mp
  have := h.q_mod_four
  omega

/-- The dyadic valuation of `d + 1` is at least three. -/
theorem three_le_d_multiplicity (h : IsAdmissibleAuxiliaryPair B a q d) :
    3 ≤ multiplicity 2 (d + 1) := by
  apply (Nat.pow_dvd_iff_le_multiplicity (by decide) (Nat.succ_ne_zero d)).mp
  have := h.d_mod_eight
  omega

/-- At dyadic bound `3`, the dyadic valuation of `d + 1` is exactly three. -/
theorem d_multiplicity_eq_three (h : IsAdmissibleAuxiliaryPair B 3 q d) :
    multiplicity 2 (d + 1) = 3 :=
  le_antisymm h.d_multiplicity_le h.three_le_d_multiplicity

end IsAdmissibleAuxiliaryPair

/-- If `n ≡ 3 (mod 8)`, then the dyadic valuation of `n + 1` is exactly two. This applies to
the first prime `q` of a sharp admissible pair. -/
theorem multiplicity_two_add_one_eq_two_of_mod_eight {n : ℕ} (hn : n % 8 = 3) :
    multiplicity 2 (n + 1) = 2 :=
  multiplicity_eq_of_dvd_of_not_dvd (by omega) (by omega)

/-- At dyadic bound `3`, if `q ≡ 3 (mod 8)`, the admissible second primes are precisely those
congruent to `7` modulo `16` with the prescribed odd divisors of `d + 1`. -/
theorem isAdmissibleAuxiliaryPair_iff_of_mod_eight {B : ℝ} {q d : ℕ}
    (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) :
    IsAdmissibleAuxiliaryPair B 3 q d ↔
      d % 16 = 7 ∧ q ∣ d + 1 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ B → p ∣ d + 1 := by
  have hmul (n : ℕ) : 2 ^ 4 ∣ n + 1 ↔ 4 ≤ multiplicity 2 (n + 1) :=
    Nat.pow_dvd_iff_le_multiplicity (by decide) (Nat.succ_ne_zero n)
  constructor
  · intro h
    have h16 : ¬ 16 ∣ d + 1 := fun h' ↦
      (not_le_of_gt (Nat.lt_succ_of_le h.d_multiplicity_le)) ((hmul d).mp h')
    have := h.d_mod_eight
    exact ⟨by omega, h.q_dvd, h.prime_dvd⟩
  · rintro ⟨hd16, hqd, hp⟩
    refine ⟨hq, hd, by omega, by omega, ?_, ?_, hqd, hp⟩
    · by_contra! h
      have := (hmul q).mpr h
      omega
    · by_contra! h
      have := (hmul d).mpr h
      omega

/-- The modulus of the progression of sharp admissible second primes: `16` times the lcm of `q`
and the product of the odd primes at most `B`. -/
noncomputable def admissiblePairModulus (B : ℝ) (q : ℕ) : ℕ :=
  16 * q.lcm (∏ p ∈ (Nat.primesLE ⌊B⌋₊).erase 2, p)

/-- An odd prime `p` lies in the product defining `admissiblePairModulus` iff `p ≤ B`. -/
private theorem mem_primesLE_erase_two_iff {B : ℝ} {p : ℕ} :
    p ∈ (Nat.primesLE ⌊B⌋₊).erase 2 ↔ p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ B := by
  by_cases hp : p.Prime
  · simp [Nat.mem_primesLE, hp, Nat.le_floor_iff' hp.ne_zero]
  · simp [Nat.mem_primesLE, hp]

/-- The progression modulus is positive. -/
theorem admissiblePairModulus_pos (B : ℝ) {q : ℕ} (hq : q ≠ 0) : 0 < admissiblePairModulus B q :=
  Nat.mul_pos (by decide) (Nat.lcm_pos (Nat.pos_of_ne_zero hq)
    (Finset.prod_pos fun _ hp ↦ (mem_primesLE_erase_two_iff.mp hp).1.pos))

/-- The progression modulus is divisible by `16`. -/
theorem sixteen_dvd_admissiblePairModulus (B : ℝ) (q : ℕ) : 16 ∣ admissiblePairModulus B q :=
  dvd_mul_right _ _

/-- The first prime `q` divides the progression modulus. -/
theorem dvd_admissiblePairModulus (B : ℝ) (q : ℕ) : q ∣ admissiblePairModulus B q :=
  (Nat.dvd_lcm_left _ _).trans (dvd_mul_left _ _)

/-- Every odd prime at most `B` divides the progression modulus. -/
theorem prime_dvd_admissiblePairModulus {B : ℝ} (q : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpB : (p : ℝ) ≤ B) : p ∣ admissiblePairModulus B q :=
  (Finset.dvd_prod_of_mem id (mem_primesLE_erase_two_iff.mpr ⟨hp, hp2, hpB⟩)).trans
    ((Nat.dvd_lcm_right _ _).trans (dvd_mul_left _ _))

/-- Modulo `M > 0`, the residue class of `M - 1` consists of the `n` with `M ∣ n + 1`. -/
private theorem modEq_sub_one_iff_dvd_add_one {n M : ℕ} (hM : 0 < M) :
    n ≡ M - 1 [MOD M] ↔ M ∣ n + 1 := by
  have hpred : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hz : M ≡ 0 [MOD M] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
  rw [← Nat.modEq_zero_iff_dvd]
  constructor
  · intro h
    have h1 := h.add_right 1
    rw [hpred] at h1
    exact h1.trans hz
  · intro h
    apply Nat.ModEq.add_right_cancel' 1
    rw [hpred]
    exact h.trans hz.symm

/-- At fixed `q ≡ 3 (mod 8)`, admissibility at dyadic bound `3` cuts out one reduced
residue class modulo `admissiblePairModulus B q`, which is `16` times the lcm of `q` and the
product of the odd primes up to `B`.
The prime-selection estimates can therefore be applied to a single progression. -/
theorem exists_coprime_modEq_iff_isAdmissibleAuxiliaryPair (B : ℝ) {q : ℕ}
    (hq : q.Prime) (hq8 : q % 8 = 3) :
    ∃ r < admissiblePairModulus B q, r.Coprime (admissiblePairModulus B q) ∧
      ∀ d : ℕ, d.Prime →
        (d ≡ r [MOD admissiblePairModulus B q] ↔ IsAdmissibleAuxiliaryPair B 3 q d) := by
  let S := (Nat.primesLE ⌊B⌋₊).erase 2
  have hS (p : ℕ) : p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ B := mem_primesLE_erase_two_iff
  let P := ∏ p ∈ S, p
  let M := q.lcm P
  have hM : 0 < M := Nat.lcm_pos hq.pos (Finset.prod_pos fun p hp ↦ ((hS p).mp hp).1.pos)
  have htwo : Nat.Coprime 2 M := by
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul q P)
    refine (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).mul_right (Nat.Coprime.prod_right ?_)
    intro p hp
    obtain ⟨hp', hp2, _⟩ := (hS p).mp hp
    exact Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp h).symm)
  have hcop : Nat.Coprime 16 M := (Nat.coprime_pow_left_iff (by decide : 0 < 4) _ _).mpr htwo
  let r := Nat.chineseRemainder hcop 7 (M - 1)
  have hm (n : ℕ) : n ≡ M - 1 [MOD M] ↔ M ∣ n + 1 := modEq_sub_one_iff_dvd_add_one hM
  have hr16 : r.val.Coprime 16 :=
    Nat.coprime_of_mul_modEq_one 7 ((r.property.1.mul_right 7).trans (by decide))
  have hrM : r.val.Coprime M :=
    Nat.Coprime.of_dvd_right ((hm _).mp r.property.2) (by simp [Nat.coprime_self_add_right])
  refine ⟨r, Nat.chineseRemainder_lt_mul hcop _ _ (by decide) hM.ne', hr16.mul_right hrM, ?_⟩
  intro d hd
  rw [isAdmissibleAuxiliaryPair_iff_of_mod_eight hq hd hq8]
  constructor
  · intro h
    have h16 := (h.of_dvd (dvd_mul_right 16 M)).trans r.property.1
    have ham := (hm _).mp ((h.of_dvd (dvd_mul_left M 16)).trans r.property.2)
    refine ⟨h16, (Nat.dvd_lcm_left q P).trans ham, fun p hp hp2 hpB ↦ ?_⟩
    exact (Finset.dvd_prod_of_mem id ((hS p).mpr ⟨hp, hp2, hpB⟩)).trans
      ((Nat.dvd_lcm_right q P).trans ham)
  · rintro ⟨hd16, hqd, hp⟩
    have hP : P ∣ d + 1 := Finset.prod_primes_dvd (d + 1)
      (fun p hp ↦ ((hS p).mp hp).1.prime) fun p hp' ↦ by
        obtain ⟨hp', hp2, hpB⟩ := (hS p).mp hp'
        exact hp p hp' hp2 hpB
    exact Nat.chineseRemainder_modEq_unique hcop hd16 ((hm _).mpr (Nat.lcm_dvd hqd hP))

end TauCeti
