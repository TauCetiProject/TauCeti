/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Data.Nat.Prime.Basic
import TauCeti.Algebra.AddCircle
import TauCeti.NumberTheory.SmoothNumbers

/-!
# Rational numbers at almost every prime

A rational number has only finitely many primes dividing its numerator or its denominator. Hence
its image in `ℚ_[p]` is a `p`-adic integer at all but finitely many primes `p`, and a nonzero
rational number is a `p`-adic unit at all but finitely many primes. These are the statements that
make a rational object, such as a rational basis or a rational isometry, integral in every
completion outside a finite set of primes. Conversely, a rational number that is a `p`-adic integer
at every prime is an integer, and so is a rational number whose denominator is a power of `p` and
which is a `p`-adic integer. Consequently two rational numbers agree in `ℚ/ℤ` when their
difference has `p`-power denominator and is a `p`-adic integer. Finally, for a prime `l`, the
rational numbers that are `p`-adic units at every prime `p ≠ l` are exactly the numbers `± lⁿ`,
`n ∈ ℤ`.

## Main results

* `Rat.eventually_not_dvd_den`: almost every prime is coprime to the denominator.
* `Padic.eventually_norm_rat_le_one`: a rational number is `p`-adically integral at almost every
  prime.
* `Padic.eventually_norm_rat_eq_one`: a nonzero rational number has `p`-adic norm one at almost
  every prime.
* `Padic.forall_norm_rat_le_one_iff_den_eq_one`: a rational number is an integer exactly when it
  is a `p`-adic integer at every prime.
* `Padic.den_eq_one_of_pow_mul_eq_of_norm_rat_le_one`: a `p`-adic integer whose product with a
  power of `p` is an integer is an integer.
* `Padic.forall_norm_rat_eq_one_iff_exists_zpow`: a rational number is a `p`-adic unit at every
  prime `p ≠ l` exactly when it is `± lⁿ` for an integer `n`.
* `Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap`: two rational numbers agree in `ℚ/ℤ` when their
  difference has `p`-power denominator and lies in `ℤ_p`.
-/

public section

open Filter

/-- All but finitely many primes do not divide the denominator of a rational number. -/
theorem Rat.eventually_not_dvd_den (q : ℚ) :
    ∀ᶠ p : Nat.Primes in cofinite, ¬ (p : ℕ) ∣ q.den := by
  refine eventually_cofinite.mpr
    (((Set.finite_Iic q.den).preimage Subtype.val_injective.injOn).subset fun p hp ↦ ?_)
  exact Nat.le_of_dvd q.den_pos (not_not.mp hp)

namespace Padic

/-- A rational number is a `p`-adic integer at all but finitely many primes `p`. -/
theorem eventually_norm_rat_le_one (q : ℚ) :
    ∀ᶠ p : Nat.Primes in cofinite, ‖(q : ℚ_[p])‖ ≤ 1 := by
  filter_upwards [q.eventually_not_dvd_den] with p hp
  exact norm_rat_le_one hp

/-- A nonzero rational number is a `p`-adic unit at all but finitely many primes `p`. -/
theorem eventually_norm_rat_eq_one {q : ℚ} (hq : q ≠ 0) :
    ∀ᶠ p : Nat.Primes in cofinite, ‖(q : ℚ_[p])‖ = 1 := by
  filter_upwards [eventually_norm_rat_le_one q, eventually_norm_rat_le_one q⁻¹] with p hp hp'
  have hpos : 0 < ‖(q : ℚ_[p])‖ := norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hq)
  rw [Rat.cast_inv, norm_inv] at hp'
  exact le_antisymm hp ((inv_le_one₀ hpos).mp hp')

/-- A rational number is an integer, that is, has denominator one, exactly when it is a `p`-adic
integer at every prime `p`. -/
theorem forall_norm_rat_le_one_iff_den_eq_one {q : ℚ} :
    (∀ p : Nat.Primes, ‖(q : ℚ_[p])‖ ≤ 1) ↔ q.den = 1 := by
  refine ⟨fun h ↦ ?_, fun h p ↦ norm_rat_le_one (by rw [h]; exact p.prop.not_dvd_one)⟩
  by_contra hq
  -- A prime dividing the denominator makes the denominator a non-unit in `ℤ_[p]`.
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq
  let : Fact p.Prime := ⟨hp⟩
  have hlt := (PadicInt.norm_int_lt_one_iff_dvd (p := p) q.den).mpr
    (Int.natCast_dvd_natCast.mpr hpd)
  rw [Int.cast_natCast] at hlt
  exact hlt.ne ((PadicInt.isUnit_iff).mp (PadicInt.isUnit_den q (h ⟨p, hp⟩)))

/-- A rational number `q` such that `p ^ k * q` is an integer is itself an integer as soon as it is
a `p`-adic integer. -/
theorem den_eq_one_of_pow_mul_eq_of_norm_rat_le_one {p : ℕ} [Fact p.Prime] {q : ℚ} {k : ℕ}
    {n : ℤ} (hn : (p : ℚ) ^ k * q = n) (hq : ‖(q : ℚ_[p])‖ ≤ 1) : q.den = 1 := by
  have hnorm : ‖(n : ℚ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
    rw [← Rat.cast_intCast, ← hn, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, norm_mul,
      norm_p_pow]
    exact mul_le_of_le_one_right (zpow_nonneg (Nat.cast_nonneg p) _) hq
  obtain ⟨m, rfl⟩ := (norm_int_le_pow_iff_dvd n k).mp hnorm
  have hp : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hqm : q = m := mul_left_cancel₀ hp (by rw [hn]; push_cast; ring)
  rw [hqm, Rat.den_intCast]

/-- For a prime `l`, a rational number is a `p`-adic unit at every prime `p ≠ l` exactly when it
is `± lⁿ` for an integer `n`. -/
theorem forall_norm_rat_eq_one_iff_exists_zpow {l : ℕ} [Fact l.Prime] {q : ℚ} :
    (∀ p : Nat.Primes, (p : ℕ) ≠ l → ‖(q : ℚ_[p])‖ = 1) ↔
      ∃ n : ℤ, q = (l : ℚ) ^ n ∨ q = -(l : ℚ) ^ n := by
  have hl : l.Prime := Fact.out
  have hnorm_l {p : Nat.Primes} (hp : (p : ℕ) ≠ l) : ‖((l : ℚ) : ℚ_[p])‖ = 1 := by
    rw [Rat.cast_natCast, norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes p.prop hl).mpr hp
  constructor
  · intro h
    have hq : q ≠ 0 := by
      obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
      rintro rfl
      simpa using h ⟨p, hp⟩ (show p ≠ l by omega)
    -- Away from `l` the valuations of `q` vanish, so `|num q|` and `den q` are powers of `l`.
    have hv (p : ℕ) (hp : p.Prime) (hpl : p ∉ ({l} : Finset ℕ)) : padicValRat p q = 0 := by
      have : Fact p.Prime := ⟨hp⟩
      have hpq := h ⟨p, hp⟩ (by simpa using hpl)
      rw [eq_padicNorm, padicNorm.eq_zpow_of_ne_zero hq, Rat.cast_zpow, Rat.cast_natCast,
        zpow_eq_one_iff_right₀ (Nat.cast_nonneg p) (mod_cast hp.ne_one)] at hpq
      exact neg_eq_zero.mp hpq
    obtain ⟨hnum, hden⟩ := (TauCeti.forall_padicValRat_eq_zero_iff_mem_factoredNumbers hq).mp hv
    have hS : ∀ p ∈ ({l} : Finset ℕ), p.Prime := by simpa using hl
    have hnum' := TauCeti.prod_pow_padicValNat_eq_self_of_mem_factoredNumbers hS hnum
    have hden' := TauCeti.prod_pow_padicValNat_eq_self_of_mem_factoredNumbers hS hden
    rw [Finset.prod_singleton] at hnum' hden'
    refine ⟨padicValNat l q.num.natAbs - padicValNat l q.den,
      (abs_eq (zpow_nonneg (Nat.cast_nonneg l) _)).mp ?_⟩
    rw [zpow_sub₀ (mod_cast hl.ne_zero), zpow_natCast, zpow_natCast, ← Nat.cast_pow,
      ← Nat.cast_pow, hnum', hden', Rat.abs_def, Rat.divInt_eq_div]
    simp [Nat.cast_natAbs]
  · rintro ⟨n, rfl | rfl⟩ p hp
    · rw [Rat.cast_zpow, norm_zpow, hnorm_l hp, one_zpow]
    · rw [Rat.cast_neg, norm_neg, Rat.cast_zpow, norm_zpow, hnorm_l hp, one_zpow]

/-- Two rational numbers agree modulo `ℤ` when their difference has `p`-power denominator and
lies in `ℤ_p`. -/
theorem addCircle_coe_eq_coe_of_eq_add_algebraMap {p : ℕ} [Fact p.Prime] {r s : ℚ} {k : ℕ} {n : ℤ}
    (hn : (p : ℚ) ^ k * (r - s) = n) {z : ℤ_[p]}
    (hz : (r : ℚ_[p]) = s + algebraMap ℤ_[p] ℚ_[p] z) :
    (r : AddCircle (1 : ℚ)) = s := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff_mem_one]
  have hden := den_eq_one_of_pow_mul_eq_of_norm_rat_le_one hn (by
    rw [Rat.cast_sub, hz, add_sub_cancel_left, PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one z)
  exact Submodule.mem_one.mpr ⟨_, (eq_intCast _ _).trans ((Rat.den_eq_one_iff _).mp hden)⟩

/-- The integer `D = ∏_p p ^ k p` of a finitely supported family of exponents factors at each
prime `p` as `p ^ k p * D' p`, where `D' p` is a `p`-adic unit divisible by `q ^ k q` for
`q ≠ p`. -/
theorem exists_nat_eq_pow_mul (k : Nat.Primes → ℕ)
    (hk : ∀ᶠ p in cofinite, k p = 0) :
    ∃ (D : ℕ) (D' : Nat.Primes → ℕ), D ≠ 0 ∧ (∀ p : Nat.Primes, D = (p : ℕ) ^ k p * D' p) ∧
      (∀ {p q : Nat.Primes}, q ≠ p → (q : ℕ) ^ k q ∣ D' p) ∧
      ∀ p : Nat.Primes, IsUnit (D' p : ℤ_[p]) := by
  classical
  have hS : {p | k p ≠ 0}.Finite := eventually_cofinite.mp hk
  let S := hS.toFinset
  have hkS {q : Nat.Primes} (hq : q ∉ S) : k q = 0 := by simpa [S] using hq
  refine ⟨∏ q ∈ S, (q : ℕ) ^ k q, fun p ↦ ∏ q ∈ S.erase p, (q : ℕ) ^ k q,
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ q.property.ne_zero, fun p ↦ ?_,
    fun {p q} hqp ↦ ?_, fun p ↦ ?_⟩
  · by_cases hp : p ∈ S
    · exact (Finset.mul_prod_erase S _ hp).symm
    · simp [hkS hp, Finset.erase_eq_of_notMem hp]
  · by_cases hq : q ∈ S
    · exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hqp, hq⟩)
    · simp [hkS hq]
  · rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
      Nat.Prime.coprime_iff_not_dvd p.property, Prime.dvd_finsetProd_iff p.property.prime]
    rintro ⟨q, hq, hpq⟩
    exact (Finset.mem_erase.mp hq).1
      (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp
          (p.property.dvd_of_dvd_pow hpq))).symm

end Padic
