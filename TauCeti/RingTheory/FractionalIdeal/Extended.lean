/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import TauCeti.RingTheory.DedekindDomain.Factorization
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Multiplicities in extended fractional ideals

Extension of a fractional ideal multiplies its multiplicity at a prime by the ramification
index. This is the ideal-theoretic counterpart of the valuation formula for extension of
completions, and permits comparison of ideal extension with extension of finite ideles.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R B K L : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]
  [Module.IsTorsionFree R B] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra B L] [IsFractionRing B L]
  {hf : R⁰ ≤ Submonoid.comap (algebraMap R B) B⁰}

open Classical in
/-- The multiplicity of a prime in the extension of a prime ideal is its ramification
index, and is zero when the prime downstairs is not the prime below it. -/
theorem count_extended_prime (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) :
    count L w (extended L hf (v.asIdeal : FractionalIdeal R⁰ K)) =
      if v = w.under R then (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) else 0 := by
  classical
  have hmap : v.asIdeal.map (algebraMap R B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  rw [extended_coeIdeal_eq_map, count_coe L w hmap,
    Ideal.count_associates_factors_eq hmap w.isPrime w.ne_bot,
    ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap w.isPrime w.ne_bot]
  split_ifs with h
  · rfl
  · have hn : ¬ v.asIdeal.map (algebraMap R B) ≤ w.asIdeal := by
      intro hv
      have hle : v.asIdeal ≤ (w.under R).asIdeal := by
        simpa only [HeightOneSpectrum.under_asIdeal, Ideal.under_def] using
          (Ideal.map_le_iff_le_comap.mp hv)
      exact h (HeightOneSpectrum.asIdeal_injective
        (v.isMaximal.eq_of_le (w.under R).isPrime.ne_top hle))
    simp [Ideal.ramificationIdx'_of_not_le hn]

/-- **Extension multiplies prime multiplicities by the ramification index.** No Galois
hypothesis is needed, and the formula also holds for the zero fractional ideal. -/
@[simp]
theorem count_extended (I : FractionalIdeal R⁰ K) (w : HeightOneSpectrum B) :
    count L w (extended L hf I) =
      ((w.under R).asIdeal.ramificationIdx' w.asIdeal : ℤ) * count K (w.under R) I := by
  classical
  rw [← extendedHom'_apply L hf]
  by_cases hI0 : I = 0
  · simp [hI0, count_zero]
  obtain ⟨I, rfl⟩ := isUnit_iff_ne_zero.mpr hI0
  let E := Units.map (extendedHom L B : FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom
  have hprime (v : HeightOneSpectrum R) (n : ℤ) :
      count L w (E (v.unitOfPrime K ^ n) : FractionalIdeal B⁰ L) =
        ((w.under R).asIdeal.ramificationIdx' w.asIdeal : ℤ) *
          count K (w.under R) (v.unitOfPrime K ^ n : (FractionalIdeal R⁰ K)ˣ) := by
    simp only [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, HeightOneSpectrum.coe_unitOfPrime, count_zpow, E]
    rw [extendedHom'_apply, count_extended_prime, count_maximal]
    split_ifs with h <;> simp_all [mul_comm]
  have hI := finprod_unitOfPrime_zpow_count I
  have h : count L w (E (∏ᶠ v : HeightOneSpectrum R,
        v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K)) : FractionalIdeal B⁰ L) =
      ((w.under R).asIdeal.ramificationIdx' w.asIdeal : ℤ) *
        count K (w.under R) (∏ᶠ v : HeightOneSpectrum R,
          v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K) : (FractionalIdeal R⁰ K)ˣ) := by
    apply finprod_induction (fun J : (FractionalIdeal R⁰ K)ˣ ↦
      count L w (E J : FractionalIdeal B⁰ L) =
        ((w.under R).asIdeal.ramificationIdx' w.asIdeal : ℤ) *
          count K (w.under R) (J : FractionalIdeal R⁰ K))
    · simp [count_one]
    · intro a b ha hb
      simp only [map_mul, Units.val_mul, count_mul _ _ (Units.ne_zero _) (Units.ne_zero _), ha, hb]
      ring
    · intro v
      exact hprime v _
  rw [← hI] at h
  exact h

end FractionalIdeal
