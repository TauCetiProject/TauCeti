/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.Data.Nat.Factorization.OddExponentPart

/-!
# Jacobi symbols over a residue class modulo a multiple of `8`

Let `8 ∣ m₀`. On the natural numbers `q` prime to `n` in one residue class of odd numbers modulo
`m₀`, the Jacobi symbol `J(n | q)` is `J(q | s)` up to a sign that depends only on the class, where
`n = s t² A` and every prime factor of `A` divides `m₀`. The canonical choice of `s` is the
odd-exponent part `Nat.oddExpPart m₀ n`, the product of the primes `p ∤ m₀` that divide `n` to an
odd power, for which such `t` and `A` exist by `Nat.exists_eq_oddExpPart_mul_sq_mul`.

The proof splits `J(n | q)` into three factors. The square `t²` contributes `1`. For a prime
`p ∣ m₀` the symbol `J(p | q)` depends only on `q` modulo `4p` (Mathlib's `jacobiSym.mod_right`),
and `4p ∣ m₀`. Finally `J(s | q) J(q | s)` depends only on `q` modulo `8`, for every `s` prime to
`q`: by quadratic reciprocity for odd prime factors of `s`, and through `J(2 | q) = χ₈ q` and
`J(q | 2) = 1` for the factor `2`.

## Main statements

* `TauCeti.jacobiSym_mul_jacobiSym_eq_of_modEq_eight`: for `s` prime to `q`, `J(s | q) J(q | s)`
  depends only on the odd number `q` modulo `8`.
* `TauCeti.jacobiSym_eq_of_modEq_of_forall_prime_dvd`: if every prime factor of `A` divides `m₀`
  and `8 ∣ m₀`, then `J(A | q)` depends only on the odd number `q` modulo `m₀`.
* `TauCeti.exists_jacobiSym_eq_mul_jacobiSym`: reciprocity on a residue class. For `8 ∣ m₀`, odd
  `a₀` and `n = s t² A` with every prime factor of `A` dividing `m₀`, there is `ε = ±1` with
  `J(n | q) = ε J(q | s)` for every `q ≡ a₀ (mod m₀)` prime to `n`.
* `TauCeti.exists_jacobiSym_eq_mul_jacobiSym_oddExpPart`: the same with `s = Nat.oddExpPart m₀ n`,
  the product of the primes `p ∤ m₀` dividing `n` to an odd power.

## References

* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>: the source of the statement, for
  the primes `q > n` of the class.
-/

public section

namespace TauCeti

/-- For odd `q` and `q ≡ q' (mod 8)`, the product `J(s | q) J(q | s)` takes the same value at `q`
and at `q'`, for every `s` prime to both. -/
theorem jacobiSym_mul_jacobiSym_eq_of_modEq_eight {s q q' : ℕ} (hq : Odd q)
    (hqq' : q ≡ q' [MOD 8]) (hs : s.Coprime q) (hs' : s.Coprime q') :
    jacobiSym s q * jacobiSym q s = jacobiSym s q' * jacobiSym q' s := by
  -- `q ≡ q' [MOD 8]` is by definition the equation `q % 8 = q' % 8`, which `▸` rewrites with.
  have hq' : Odd q' := (Odd.mod_even_iff (by decide)).1 (hqq' ▸ hq.mod_even (by decide))
  induction s using Nat.recOnMul with
  | zero => rw [(Nat.coprime_zero_left _).1 hs, (Nat.coprime_zero_left _).1 hs']
  | one => simp only [Nat.cast_one, jacobiSym.one_left, jacobiSym.one_right]
  | prime p hp =>
    rcases hp.eq_two_or_odd' with rfl | hpo
    · -- `J(2 | q) = χ₈ q` depends on `q` modulo `8`, and `J(q | 2) = 1` for odd `q`.
      have h2 : ∀ r : ℕ, Odd r → jacobiSym r 2 = 1 := fun r hr => by
        rw [jacobiSym.mod_left, Nat.cast_ofNat, Int.odd_iff.1 (hr.natCast (R := ℤ)),
          jacobiSym.one_left]
      rw [Nat.cast_ofNat, jacobiSym.at_two hq, jacobiSym.at_two hq',
        (ZMod.natCast_eq_natCast_iff _ _ _).2 hqq', h2 q hq, h2 q' hq']
    · -- Reciprocity: `J(p | q) J(q | p) = J(χ₄ q | p)`, and `χ₄ q` depends on `q` modulo `4`.
      have hgcd : ∀ r : ℕ, p.Coprime r → (r : ℤ).gcd p = 1 := fun r hr => by
        rw [Int.gcd_natCast_natCast]
        exact hr.symm
      rw [jacobiSym.quadratic_reciprocity' hpo hq, jacobiSym.quadratic_reciprocity' hpo hq',
        mul_assoc, mul_assoc, ← sq, ← sq, jacobiSym.sq_one (hgcd q hs),
        jacobiSym.sq_one (hgcd q' hs'), qrSign, qrSign,
        (ZMod.natCast_eq_natCast_iff _ _ _).2 (hqq'.of_dvd (by norm_num : 4 ∣ 8))]
  | mul a b iha ihb =>
    rcases eq_or_ne (a * b) 0 with h0 | h0
    · rw [h0] at hs hs' ⊢
      rw [(Nat.coprime_zero_left _).1 hs, (Nat.coprime_zero_left _).1 hs']
    have ha := Nat.coprime_mul_iff_left.1 hs
    have ha' := Nat.coprime_mul_iff_left.1 hs'
    rw [Nat.cast_mul, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.mul_right' _ (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0),
      jacobiSym.mul_right' _ (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)]
    linear_combination (jacobiSym b q * jacobiSym q b) * iha ha.1 ha'.1 +
      (jacobiSym a q' * jacobiSym q' a) * ihb ha.2 ha'.2

/-- If `8 ∣ m₀` and every prime factor of `A` divides `m₀`, then the Jacobi symbol `J(A | q)`
depends only on the odd number `q` modulo `m₀`. -/
theorem jacobiSym_eq_of_modEq_of_forall_prime_dvd {m₀ A q q' : ℕ} (h8 : 8 ∣ m₀)
    (hA : ∀ p, p.Prime → p ∣ A → p ∣ m₀) (hq : Odd q) (hqq' : q ≡ q' [MOD m₀]) :
    jacobiSym A q = jacobiSym A q' := by
  have he : Even m₀ := even_iff_two_dvd.2 (dvd_trans (by norm_num) h8)
  -- `q ≡ q' [MOD m₀]` is by definition the equation `q % m₀ = q' % m₀`.
  have hq' : Odd q' := (Odd.mod_even_iff he).1 (hqq' ▸ hq.mod_even he)
  induction A using Nat.recOnMul with
  | zero =>
    -- Every prime divides `m₀`, so `m₀ = 0` and `q = q'`.
    obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (m₀ + 1)
    obtain rfl : m₀ = 0 := Nat.eq_zero_of_dvd_of_lt (hA p hpp (dvd_zero p)) (by omega)
    rw [Nat.modEq_zero_iff.mp hqq']
  | one => simp only [Nat.cast_one, jacobiSym.one_left]
  | prime p hp =>
    have h4p : 4 * p ∣ m₀ := by
      rcases hp.eq_two_or_odd' with rfl | hpo
      · exact h8
      · have h4 : Nat.Coprime 4 p := by simpa using (Nat.coprime_two_left.2 hpo).pow_left 2
        exact h4.mul_dvd_of_dvd_of_dvd (dvd_trans (by norm_num) h8) (hA p hp dvd_rfl)
    rw [jacobiSym.mod_right _ hq, jacobiSym.mod_right _ hq', Int.natAbs_natCast,
      hqq'.of_dvd h4p]
  | mul a b iha ihb =>
    rw [Nat.cast_mul, jacobiSym.mul_left, jacobiSym.mul_left,
      iha fun p hp h => hA p hp (h.mul_right b), ihb fun p hp h => hA p hp (h.mul_left a)]

/-- Let `8 ∣ m₀` and `n = s t² A` with every prime factor of `A` dividing `m₀`. For odd `q` and
`q' ≡ q (mod m₀)`, both prime to `n`, the product `J(n | q) J(q | s)` takes the same value at `q`
and at `q'`. -/
theorem jacobiSym_mul_jacobiSym_eq_of_modEq {m₀ n s t A q q' : ℕ} (h8 : 8 ∣ m₀)
    (hn : n = s * t ^ 2 * A) (hA : ∀ p, p.Prime → p ∣ A → p ∣ m₀) (hq : Odd q)
    (hqq' : q ≡ q' [MOD m₀]) (hnq : n.Coprime q) (hnq' : n.Coprime q') :
    jacobiSym n q * jacobiSym q s = jacobiSym n q' * jacobiSym q' s := by
  subst hn
  have h := Nat.coprime_mul_iff_left.1 (Nat.coprime_mul_iff_left.1 hnq).1
  have h' := Nat.coprime_mul_iff_left.1 (Nat.coprime_mul_iff_left.1 hnq').1
  have ht : ∀ r : ℕ, (t ^ 2).Coprime r → (t : ℤ).gcd r = 1 := fun r hr => by
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self t two_ne_zero) hr
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left,
    jacobiSym.sq_one' (ht q h.2), jacobiSym.sq_one' (ht q' h'.2),
    jacobiSym_eq_of_modEq_of_forall_prime_dvd h8 hA hq hqq']
  linear_combination jacobiSym A q' *
    jacobiSym_mul_jacobiSym_eq_of_modEq_eight hq (hqq'.of_dvd h8) h.1 h'.1

/-- **Reciprocity on a residue class.** Let `8 ∣ m₀`, let `a₀` be odd, and let `n = s t² A` where
every prime factor of `A` divides `m₀`. There is `ε = ±1` such that every `q ≡ a₀ (mod m₀)` prime
to `n` satisfies `J(n | q) = ε J(q | s)`.

The canonical choice of `s` is `Nat.oddExpPart m₀ n`, the product of the primes `p ∤ m₀` dividing
`n` to an odd power (`exists_jacobiSym_eq_mul_jacobiSym_oddExpPart`). A prime `q` of the class is
prime to `n` when `q ∤ n`, and in particular when `n ≥ 1` and `q > n`. -/
theorem exists_jacobiSym_eq_mul_jacobiSym {m₀ a₀ n s t A : ℕ} (h8 : 8 ∣ m₀) (ha₀ : Odd a₀)
    (hn : n = s * t ^ 2 * A) (hA : ∀ p, p.Prime → p ∣ A → p ∣ m₀) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ q, q ≡ a₀ [MOD m₀] → n.Coprime q → jacobiSym n q = ε * jacobiSym q s := by
  by_cases h : ∃ q₀, q₀ ≡ a₀ [MOD m₀] ∧ n.Coprime q₀
  swap
  · exact ⟨1, Or.inl rfl, fun q hq hnq => absurd ⟨q, hq, hnq⟩ h⟩
  obtain ⟨q₀, hq₀, hnq₀⟩ := h
  have hs : ∀ q, n.Coprime q → (q : ℤ).gcd s = 1 := fun q hnq => by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Coprime.coprime_dvd_left ⟨t ^ 2 * A, by rw [hn, mul_assoc]⟩ hnq).symm
  have hn' : (n : ℤ).gcd q₀ = 1 := by rwa [Int.gcd_natCast_natCast]
  refine ⟨jacobiSym n q₀ * jacobiSym q₀ s, ?_, fun q hq hnq => ?_⟩
  · rcases jacobiSym.eq_one_or_neg_one hn' with h1 | h1 <;>
      rcases jacobiSym.eq_one_or_neg_one (hs q₀ hnq₀) with h2 | h2 <;> simp [h1, h2]
  · have he : Even m₀ := even_iff_two_dvd.2 (dvd_trans (by norm_num) h8)
    -- `q ≡ a₀ [MOD m₀]` is by definition the equation `q % m₀ = a₀ % m₀`.
    have hodd : Odd q := (Odd.mod_even_iff he).1 (hq ▸ ha₀.mod_even he)
    rw [← jacobiSym_mul_jacobiSym_eq_of_modEq h8 hn hA hodd (hq.trans hq₀.symm) hnq hnq₀]
    linear_combination (-jacobiSym n q) * jacobiSym.sq_one (hs q hnq)

/-- **Reciprocity on a residue class**, with the odd-exponent part. Let `8 ∣ m₀` and let `a₀` be
odd. There is `ε = ±1` such that every `q ≡ a₀ (mod m₀)` prime to `n` satisfies
`J(n | q) = ε J(q | Nat.oddExpPart m₀ n)`, where `Nat.oddExpPart m₀ n` is the product of the primes
`p ∤ m₀` that divide `n` to an odd power. A prime `q` of the class is prime to `n` when `q ∤ n`,
and in particular when `n ≥ 1` and `q > n`. -/
theorem exists_jacobiSym_eq_mul_jacobiSym_oddExpPart {m₀ a₀ n : ℕ} (h8 : 8 ∣ m₀) (ha₀ : Odd a₀) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ q, q ≡ a₀ [MOD m₀] → n.Coprime q →
      jacobiSym n q = ε * jacobiSym q (Nat.oddExpPart m₀ n) := by
  obtain ⟨t, A, hnA, hA⟩ := Nat.exists_eq_oddExpPart_mul_sq_mul m₀ n
  exact exists_jacobiSym_eq_mul_jacobiSym h8 ha₀ hnA hA

end TauCeti
