/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.Splitting

/-!
# Products of two ideal norms in quadratic fields

Among more than `h_K` distinct absolute ideal norms in a quadratic field, two
have a product that is an absolute element norm. At split primes this selects two distinct
rational primes whose product is the norm of a single algebraic integer. In `ℚ(√−d)` with
`d ≡ 3 (mod 4)`, primes congruent to `1` modulo `d` furnish such ideal norms.
-/

public section

open Polynomial
open scoped NumberField ComplexConjugate nonZeroDivisors

namespace TauCeti.NumberField

/-- In a quadratic number field, if a finite set of absolute ideal norms has more
members than the class number, the product of two distinct members is the absolute norm of
an algebraic integer. -/
theorem exists_natAbs_norm_eq_mul_of_classNumber_lt {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (S : Finset ℕ) (hS : NumberField.classNumber K < S.card)
    (hI : ∀ n ∈ S, ∃ I : Ideal (𝓞 K), Ideal.absNorm I = n) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ z : 𝓞 K, (Algebra.norm ℤ z).natAbs = a * b := by
  classical
  by_cases hzero : 0 ∈ S
  · have htwo : 1 < S.card := by
      have := NumberField.classNumber_pos (K := K)
      omega
    obtain ⟨b, hb, hb0⟩ := S.exists_mem_ne htwo 0
    exact ⟨0, hzero, b, hb, hb0.symm, 0, by simp⟩
  have hpos (n : S) : 0 < n.val := Nat.pos_of_ne_zero (fun hn ↦ hzero (hn ▸ n.property))
  choose I hnorm using fun n : S ↦ hI n n.property
  have hne (n : S) : I n ≠ 0 := by
    intro h
    exact (hpos n).ne' (by simpa [h] using (hnorm n).symm)
  let J (n : S) : (Ideal (𝓞 K))⁰ := ⟨I n, mem_nonZeroDivisors_of_ne_zero (hne n)⟩
  obtain ⟨a, b, hab, hclass⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : S ↦ ClassGroup.mk0 (J n)) (by simpa [NumberField.classNumber] using hS)
  -- Complete `I b` to the principal ideal `(b)`, then replace `I b` by `I a`.
  have hdiv : I b ∣ Ideal.span {(b.val : 𝓞 K)} := Ideal.dvd_iff_le.mpr <| by
    simpa only [hnorm b] using Ideal.span_singleton_absNorm_le (I b)
  obtain ⟨L, hL⟩ := hdiv
  have hLnorm : Ideal.absNorm L = b.val := by
    apply Nat.eq_of_mul_eq_mul_left (hpos b)
    simpa only [Ideal.absNorm_span_natCast, map_mul, NumberField.RingOfIntegers.rank, hK,
      hnorm b, pow_two] using (congrArg Ideal.absNorm hL).symm
  have hLne : L ≠ 0 := by
    intro hz
    exact (hpos b).ne' (by simpa [hz] using hLnorm.symm)
  let L₀ : (Ideal (𝓞 K))⁰ := ⟨L, mem_nonZeroDivisors_of_ne_zero hLne⟩
  have hprincipal : Submodule.IsPrincipal (I b * L) := ⟨⟨b.val, hL.symm⟩⟩
  have hm (n : S) : ClassGroup.mk0 (J n * L₀) = 1 ↔ Submodule.IsPrincipal (I n * L) :=
    ClassGroup.mk0_eq_one_iff (J n * L₀).property
  have : Submodule.IsPrincipal (I a * L) := (hm a).mp <| by
    rw [map_mul, hclass, ← map_mul]
    exact (hm b).mpr hprincipal
  refine ⟨a, a.property, b, b.property, fun h ↦ hab (Subtype.ext h),
    Submodule.IsPrincipal.generator (I a * L), ?_⟩
  rw [← Ideal.absNorm_span_singleton, Ideal.span_singleton_generator, map_mul, hnorm a, hLnorm]

/-- Among more than `h_K` primes congruent to `1` modulo `d`, two have product `z * conj z`
for an algebraic integer `z` of `K = ℚ(√−d)`. The identity is written at the embedding `σ`. -/
theorem exists_prime_pair_mul_conj_eq_of_classNumber_lt {K : Type*} [Field K] [NumberField K]
    {d : ℕ} (hd₄ : d % 4 = 3) {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = X ^ 2 - C (-(d : ℤ))) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (σ : K →+* ℂ) (S : Finset ℕ) (hS : NumberField.classNumber K < S.card)
    (hprime : ∀ p ∈ S, p.Prime ∧ p ≡ 1 [MOD d]) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ z : 𝓞 K, σ z * conj (σ z) = (p : ℂ) * q := by
  have hK := NumberField.finrank_rat_eq_two hmin hgen
  have hd : 1 < d := by omega
  have hd' : Odd d := Nat.odd_iff.mpr (by omega)
  have : NumberField.IsTotallyComplex K :=
    NumberField.isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin
      (neg_lt_zero.mpr (by exact_mod_cast (zero_lt_one.trans hd)))
  have hI (p : ℕ) (hp : p ∈ S) : ∃ I : Ideal (𝓞 K), Ideal.absNorm I = p := by
    obtain ⟨hpp, hpd⟩ := hprime p hp
    have hp₂ : p ≠ 2 := by
      rintro rfl
      have := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 2)).mp hpd.symm
      exact hd.ne' (Nat.dvd_one.mp (by simpa using this : d ∣ 1))
    have hp' : Odd p := Nat.odd_iff.mpr (hpp.eq_two_or_odd.resolve_left hp₂)
    have : Fact p.Prime := ⟨hpp⟩
    have hsign : qrSign d p = ZMod.χ₄ p := by
      rw [qrSign, ZMod.χ₄_nat_three_mod_four hd₄, jacobiSym.at_neg_one hp']
    have hJ : jacobiSym p d = 1 := by
      rw [jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hpd), Nat.cast_one, jacobiSym.one_left]
    have hleg : legendreSym p (-(d : ℤ)) = 1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hp',
        jacobiSym.quadratic_reciprocity' hd' hp', qrSign.symm hp' hd', hJ,
        mul_one, ← hsign, ← sq, qrSign.sq_eq_one hd' hp']
    obtain ⟨I, _, _, hnorm⟩ :=
      NumberField.exists_isPrime_and_absNorm_eq_of_legendreSym_eq_one hmin hgen hp₂ hleg
    exact ⟨I, hnorm⟩
  obtain ⟨p, hp, q, hq, hpq, z, hz⟩ :=
    exists_natAbs_norm_eq_mul_of_classNumber_lt hK S hS hI
  have hz' := abs_norm_eq_norm_sq_of_finrank_eq_two hK σ (z : K)
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Nat.cast_natAbs, hz] at hz'
  refine ⟨p, hp, q, hq, hpq, z, ?_⟩
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hz']
  push_cast
  rfl

end TauCeti.NumberField
