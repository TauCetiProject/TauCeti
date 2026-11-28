/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Int.Basic
import TauCeti.Algebra.QuadraticAlgebra.TracePower

/-!
# Arithmetic of the trace-dual frame length

For the cyclotomic order `q₁` and the quadratic half-generator `β` of norm
`(d+1)/4`, the power with exponent `j = ⌈log₂ q₁⌉` has two uses in the
trace-dual frame construction. Its norm clears the denominator `q₁`, while
its trace is one modulo every prime dividing `q₁`. Adding that trace to the
uncorrected length, a multiple of `q₁`, therefore makes the length coprime to `q₁`.

The length and its correction are those of `New.Parameters.dualResolutionFactor` in
`New/Derivatives/Vacuum/ShortVectors.lean` of lsernau/grh-lean, revision `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- The norm of the indicated power of the quadratic half-generator clears the
cyclotomic order, not just its prime divisors. -/
theorem q₁_dvd_halfGeneratorNorm_pow (P : Parameters) {s j : ℕ} (hj : P.q₁ s ≤ 2 ^ j) :
    P.q₁ s ∣ ((P.d + 1) / 4) ^ j := by
  have hn : (P.d + 1) / 4 ≠ 0 := by have := P.sixty_four_lt_d; omega
  rw [← Nat.factorization_le_iff_dvd (P.q₁_pos s).ne' (pow_ne_zero _ hn),
    Nat.factorization_pow]
  intro p
  by_cases h : p ∈ (P.q₁ s).primeFactors
  · have hp := Nat.prime_of_mem_primeFactors h
    have hd := P.dvd_d_add_one_div_four hp (Nat.dvd_of_mem_primeFactors h)
    have h₁ : (P.q₁ s).factorization p ≤ j :=
      Nat.factorization_le_of_le_pow (hj.trans (Nat.pow_le_pow_left hp.two_le _))
    simpa only [Finsupp.smul_apply, smul_eq_mul] using
      h₁.trans (Nat.le_mul_of_pos_right _ (hp.factorization_pos_of_dvd hn hd))
  · have hzero : (P.q₁ s).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using h)
    rw [hzero]
    exact Nat.zero_le _

/-- Adding the trace correction to a multiple of `q₁` gives an integer coprime to `q₁`.
The pair `β, β'` represents the two roots of the quadratic polynomial of the half-generator;
the formula also applies after embedding them in the field of the frame coefficients. -/
theorem exists_isCoprime_trace_dual_frame_length (P : Parameters) (s : ℕ)
    {R : Type*} [CommRing R] {β β' : R} (hadd : β + β' = 1)
    (hmul : β * β' = (((P.d + 1) / 4 : ℕ) : R)) {j : ℕ} (hj : 0 < j) (t : ℤ) :
    ∃ h : ℤ, IsCoprime (P.q₁ s : ℤ) h ∧
      (h : R) = (P.q₁ s : R) * (t : R) + β ^ j + β' ^ j := by
  let N := (P.d + 1) / 4
  let c : ℤ := QuadraticAlgebra.trace
    ((QuadraticAlgebra.omega : QuadraticAlgebra ℤ (-(N : ℤ)) 1) ^ j)
  have hc : (c : R) = β ^ j + β' ^ j :=
    QuadraticAlgebra.intCast_trace_omega_pow (N := (N : ℤ)) hadd
      (by simpa only [Int.cast_natCast, N] using hmul) j
  refine ⟨(P.q₁ s : ℤ) * t + c, ?_, by simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hc,
    add_assoc]⟩
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
  by_contra h
  obtain ⟨p, hp, hq, hh⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hc' : c ≡ 1 [ZMOD p] := QuadraticAlgebra.trace_omega_pow_modEq_one
    (Int.natCast_dvd_natCast.mpr (P.dvd_d_add_one_div_four hp hq)) hj
  have hq' : (P.q₁ s : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hq
  have hh' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.natCast_dvd.mpr hh)
  have hc'' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hc'
  have : Fact p.Prime := ⟨hp⟩
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hq', zero_mul, zero_add, hc'',
    Int.cast_one, one_ne_zero] at hh'

end TauCeti.OneSidedBound.Parameters
