/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.CMField.DyadicPrimes
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# Conjugation-fixed primes in the quadratic cyclotomic tower

At a prime fixed by complex conjugation, the trace-one quadratic integer and its conjugate
are both units locally. This excludes all primes dividing the cyclotomic order, since their
rational primes divide the norm of that quadratic integer. Once the characteristic is odd,
the dyadic part of the cyclotomic order determines the residue class of the rational prime.

These are the fixed-prime assertions of `New.Parameters.not_dvd_q₁_of_star_eq` and
`New.Parameters.natCast_eq_neg_one_of_star_eq` in
`grh/src/New/Derivatives/Field/PrimeDecomposition.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open NumberField IsCMField

namespace TauCeti.OneSidedBound.Parameters

/-- A conjugation-fixed prime cannot lie over a divisor of the tower order. Here `β` is the
image of the quadratic integer `(1 + √(-d)) / 2`, specified by its trace and norm. -/
theorem not_dvd_q₁_of_conj_fixed (P : Parameters) (s : ℕ)
    {E : Type*} [Field E] [NumberField E] [IsCMField E] {p : ℕ}
    (w : Ideal (𝓞 E)) [w.IsPrime] [w.LiesOver (Ideal.span {(p : ℤ)})]
    (hw : w.map (ringOfIntegersComplexConj E) = w) {β : 𝓞 E}
    (hβ : β + ringOfIntegersComplexConj E β = 1)
    (hN : β * ringOfIntegersComplexConj E β = (((P.d + 1) / 4 : ℕ) : 𝓞 E)) :
    ¬ p ∣ P.q₁ s := by
  intro h
  have hp₀ : p ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos h (P.q₁_pos s))
  have hp : p.Prime := Nat.prime_iff_prime_int.mpr
    ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp₀)).mp
      (Ideal.isPrime_of_liesOver w (Ideal.span {(p : ℤ)})))
  have hd := P.dvd_d_add_one_div_four hp h
  have hmem := (Ideal.algebraMap_mem_iff_dvd_of_liesOver (a := (p : ℤ)) w
    (((P.d + 1) / 4 : ℕ) : ℤ)).mpr (Int.natCast_dvd_natCast.mpr hd)
  apply mul_conj_notMem_of_add_conj_eq_one w hw hβ
  rw [hN]
  simpa only [map_natCast] using hmem

/-- In the cyclotomic tower, a conjugation-fixed prime lies above a rational prime congruent to
`-1` modulo `2 ^ (s + 1)`, including at primes that ramify in the quadratic base. -/
theorem natCast_eq_neg_one_of_conj_fixed (P : Parameters) (s : ℕ)
    {E : Type*} [Field E] [NumberField E] [IsCMField E] {p : ℕ}
    (w : Ideal (𝓞 E)) [w.IsMaximal] [w.LiesOver (Ideal.span {(p : ℤ)})]
    (hw : w.map (ringOfIntegersComplexConj E) = w) {β ζ : 𝓞 E}
    (hβ : β + ringOfIntegersComplexConj E β = 1)
    (hN : β * ringOfIntegersComplexConj E β = (((P.d + 1) / 4 : ℕ) : 𝓞 E))
    (hζ : IsPrimitiveRoot ζ (P.q₁ s)) : (p : ZMod (2 ^ (s + 1))) = -1 := by
  obtain ⟨a, ha⟩ := P.two_pow_succ_dvd_q₁ s
  have hζ' : IsPrimitiveRoot (ζ ^ a) (2 ^ (s + 1)) :=
    hζ.pow (P.q₁_pos s) (ha.trans (Nat.mul_comm _ _))
  have h₂ : (2 : 𝓞 E) ∉ w := by
    intro h
    have hd : (p : ℤ) ∣ 2 := (Ideal.algebraMap_mem_iff_dvd_of_liesOver w (2 : ℤ)).mp
      (by simpa using h)
    have hp₂ : p ∣ 2 := by exact_mod_cast hd
    apply P.not_dvd_q₁_of_conj_fixed s (p := p) w hw hβ hN
    exact hp₂.trans ((dvd_pow_self 2 (by omega : s + 1 ≠ 0)).trans (P.two_pow_succ_dvd_q₁ s))
  exact IsCMField.natCast_eq_neg_one_of_conj_fixed w hw h₂ hζ'

end TauCeti.OneSidedBound.Parameters
