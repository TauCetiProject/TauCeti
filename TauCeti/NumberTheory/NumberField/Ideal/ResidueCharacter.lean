/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.NumberField.ResidueDegree
import TauCeti.NumberTheory.MulChar.Kernel

/-!
# Residue characters with prescribed orders and triviality on roots of unity

Given an ideal containing a rational level `M`, one can prescribe the same order for the
characters at the primes dividing that ideal, and take the principal character elsewhere. A
sufficient congruence on the rational primes dividing `M` guarantees that the characters can
be made trivial on a prescribed subgroup of roots of unity in each residue field. This is
useful for choosing a tame part compatible with global roots of unity.

## References

* The local order and triviality conditions follow the choice `New.Data.chiMLocal` in
  `New/Derivatives/Field/ChosenPlaces.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
  at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace Ideal

/-- Let `I` contain the rational integer `M`. If `r * m` divides `p - 1` for every rational
prime `p` dividing `M`, there is a family of complex residue characters of order `m` at all
primes containing `I`, principal elsewhere, and trivial on `r`-torsion at every prime.
The primes containing `I` are finite when `M ≠ 0`, by `Ideal.finite_factors`. -/
theorem exists_residueCharacterFamily {K : Type*} [Field K] [NumberField K] (I : Ideal (𝓞 K))
    {M r m : ℕ} (hM : (M : 𝓞 K) ∈ I) (h : ∀ p : ℕ, p.Prime → p ∣ M → r * m ∣ p - 1) :
    ∃ ω : (v : HeightOneSpectrum (𝓞 K)) → MulChar (𝓞 K ⧸ v.asIdeal) ℂ,
      (∀ v, I ≤ v.asIdeal → orderOf (ω v) = m) ∧
      (∀ v, ¬ I ≤ v.asIdeal → ω v = 1) ∧
      ∀ v (u : (𝓞 K ⧸ v.asIdeal)ˣ), u ^ r = 1 → ω v u = 1 := by
  classical
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      ∃ χ : MulChar (𝓞 K ⧸ v.asIdeal) ℂ, (I ≤ v.asIdeal → orderOf χ = m) ∧
        (¬ I ≤ v.asIdeal → χ = 1) ∧ ∀ u : (𝓞 K ⧸ v.asIdeal)ˣ, u ^ r = 1 → χ u = 1 := by
    by_cases hv : I ≤ v.asIdeal
    · let p := TauCeti.rationalPrimeBelow v
      have hp : p.Prime := TauCeti.prime_rationalPrimeBelow v
      have hpM : p ∣ M := by
        have hcast : ((M : ℤ) : 𝓞 K) ∈ v.asIdeal := by exact_mod_cast hv hM
        exact Int.natCast_dvd_natCast.mp ((v.intCast_mem_asIdeal_iff M).mp hcast)
      have hd := h p hp hpM
      let _ := Ideal.Quotient.field v.asIdeal
      let _ := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
      have hq : r * m ∣ Fintype.card (𝓞 K ⧸ v.asIdeal) - 1 := by
        rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard,
          TauCeti.absNorm_eq_rationalPrimeBelow_pow]
        exact hd.trans (Nat.sub_one_dvd_pow_sub_one _ _)
      have hm : 0 < m := Nat.pos_of_dvd_of_pos ((dvd_mul_left m r).trans hd)
        (Nat.sub_pos_of_lt hp.one_lt)
      obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (𝓞 K ⧸ v.asIdeal)
        ((dvd_mul_left m r).trans hq) (Complex.isPrimitiveRoot_exp _ hm.ne')
      refine ⟨χ, fun _ ↦ hχ, fun hnv ↦ (hnv hv).elim,
        (χ.forall_apply_eq_one_of_pow_eq_one_iff r).mpr ?_⟩
      rw [hχ, Nat.card_units, Nat.card_eq_fintype_card]
      exact (Nat.mul_dvd_mul_left m (Nat.gcd_dvd_right _ _)).trans (mul_comm r m ▸ hq)
    · exact ⟨1, fun hv' ↦ (hv hv').elim, fun _ ↦ rfl, fun u _ ↦ MulChar.one_apply_coe u⟩
  choose ω hω using hlocal
  exact ⟨ω, fun v ↦ (hω v).1, fun v ↦ (hω v).2.1, fun v ↦ (hω v).2.2⟩

end Ideal
