/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Int.SmoothPart
public import TauCeti.NumberTheory.ProgressionPowers.Basic
import Mathlib.Basic.Sign.Basic

/-!
# Signed factorization of a progression with perfect-power product

For an odd exponent, nonzero terms whose valuations at primes at least the length are divisible
by the exponent split uniquely as positive smooth coefficients times signed powers. A primitive
solution with odd prime exponent supplies these hypotheses. The coefficients keep all powers of
the primes strictly below the length. A prime equal to the length belongs to the root. These are
the coefficients in the generalized Fermat equations obtained from triples of progression terms.

See M. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
sums*, §3, equation (6).
-/

public section

namespace TauCeti.ProgressionPowers

/-- The signed factorizations `n + i*d = Aᵢ zᵢ^ℓ` with positive `k`-smooth coefficients
and nonzero roots supported on primes at least `k`. -/
@[mk_iff]
structure IsSignedFactorization (n d : ℤ) (k ℓ : ℕ) (A : Fin k → ℕ) (z : Fin k → ℤ) : Prop where
  smooth : ∀ i, A i ∈ k.smoothNumbers
  root_ne_zero : ∀ i, z i ≠ 0
  term_eq : ∀ i : Fin k, n.progressionTerm d i = (A i : ℤ) * z i ^ ℓ
  le_of_mem_primeFactors : ∀ i p, p ∈ (z i).natAbs.primeFactors → k ≤ p

variable {n d y : ℤ} {k ℓ : ℕ} {A B : Fin k → ℕ} {z w : Fin k → ℤ}

/-- The coefficient in any signed factorization is the full smooth part of the absolute term. -/
theorem IsSignedFactorization.coeff_eq_smoothPart (h : IsSignedFactorization n d k ℓ A z)
    (i : Fin k) : A i = (n.progressionTerm d i).natAbs.smoothPart k := by
  have heq := congrArg Int.natAbs (h.term_eq i)
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at heq
  rw [heq, Nat.smoothPart_mul (Nat.ne_zero_of_mem_smoothNumbers (h.smooth i))
    (pow_ne_zero _ (Int.natAbs_ne_zero.mpr (h.root_ne_zero i))),
    Nat.smoothPart_eq_self_iff.mpr (h.smooth i)]
  suffices ((z i).natAbs ^ ℓ).smoothPart k = 1 by simp [this]
  apply Nat.smoothPart_eq_one_iff.mpr
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp
  · simpa only [Nat.primeFactors_pow _ hℓ] using h.le_of_mem_primeFactors i

/-- For odd exponent, the signed root and the progression term have the same sign. -/
theorem IsSignedFactorization.sign_root (h : IsSignedFactorization n d k ℓ A z)
    (hℓ : Odd ℓ) (i : Fin k) : (z i).sign = (n.progressionTerm d i).sign := by
  have ha : 0 < (A i : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (h.smooth i))
  rw [Int.sign_eq_sign, Int.sign_eq_sign, h.term_eq, sign_mul, sign_pos ha, one_mul, sign_pow,
    SignType.pow_odd _ hℓ]

/-- At odd exponent the coefficient and root families are both unique. -/
theorem IsSignedFactorization.unique (h : IsSignedFactorization n d k ℓ A z)
    (h' : IsSignedFactorization n d k ℓ B w) (hℓ : Odd ℓ) : A = B ∧ z = w := by
  have hAB := funext fun i ↦ (h.coeff_eq_smoothPart i).trans (h'.coeff_eq_smoothPart i).symm
  subst B
  refine ⟨rfl, funext fun i ↦ hℓ.pow_injective ?_⟩
  have ha : (A i : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_mem_smoothNumbers (h.smooth i)
  exact mul_left_cancel₀ ha ((h.term_eq i).symm.trans (h'.term_eq i))

/-- Nonzero terms with `ℓ`-divisible large-prime valuations admit a unique signed factorization
for every odd `ℓ`. No product equation is needed once the valuations are known. -/
theorem existsUnique_signedFactorization (hℓ : Odd ℓ)
    (hne : ∀ i : Fin k, n.progressionTerm d i ≠ 0)
    (hval : ∀ (i : Fin k) (p : ℕ), p.Prime → k ≤ p → ℓ ∣ padicValInt p (n.progressionTerm d i)) :
    ∃! f : (Fin k → ℕ) × (Fin k → ℤ), IsSignedFactorization n d k ℓ f.1 f.2 := by
  choose z hz hlarge using fun i ↦ Int.exists_eq_smoothPart_mul_pow hℓ (hval i)
  let A (i : Fin k) := (n.progressionTerm d i).natAbs.smoothPart k
  have h : IsSignedFactorization n d k ℓ A z :=
    ⟨fun i ↦ Nat.smoothPart_mem_smoothNumbers .., fun i hzi ↦ hne i (by
      simpa [hzi, zero_pow hℓ.pos.ne'] using hz i), hz, hlarge⟩
  exact ⟨(A, z), h, fun _ h' ↦ Prod.ext_iff.mpr (h'.unique h hℓ)⟩

/-- A primitive progression solution of odd prime exponent has a unique signed factorization. -/
theorem PrimitiveSolution.existsUnique_signedFactorization (h : PrimitiveSolution n d k y ℓ)
    (hℓ : Odd ℓ) :
    ∃! f : (Fin k → ℕ) × (Fin k → ℤ), IsSignedFactorization n d k ℓ f.1 f.2 :=
  ProgressionPowers.existsUnique_signedFactorization hℓ (fun i ↦ h.term_ne_zero i.isLt)
    fun i _ hp hk ↦ dvd_padicValInt_term h.gcd_eq_one h.prod_eq_pow hp hk i.isLt

end TauCeti.ProgressionPowers
