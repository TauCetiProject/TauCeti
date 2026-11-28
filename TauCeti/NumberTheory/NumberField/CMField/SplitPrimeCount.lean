/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.NumberTheory.RamificationInertia.Splitting
import TauCeti.RingTheory.RamificationInertia.ConjugateFactors

/-!
# Prime counts for a conjugate factor of a split level

If `z * conj z` is a rational level and a completely split prime occurs in that level
with exponent one, exactly half its primes upstairs contain `z`. In a CM field this
count equals the number of infinite places. For a squarefree split level the counts add
across the distinct rational prime factors.

The count is the one used in `New.Data.card_chosenPlace` in `New/UpperBound/Objects/LiftChains.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
We use `Ideal.card_primesOver_eq_two_mul_of_mul_eq_algebraMap` for the partition by conjugation.
-/

public section

open NumberField NumberField.IsCMField Module

namespace Ideal

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- If `p` splits completely in a CM field and `z * conj z = p * c` with `p ∤ c`,
the primes above `p` containing `z` are as numerous as the infinite places. -/
theorem natCard_primesOver_conjugateFactor {p c : ℕ} {z : 𝓞 E} (hc : ¬ p ∣ c)
    (hsplit : ((span {(p : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℚ E)
    (hz : z * ringOfIntegersComplexConj E z = ((p * c : ℕ) : 𝓞 E)) :
    Nat.card {P : (span {(p : ℤ)}).primesOver (𝓞 E) // z ∈ P.val} =
      Fintype.card (InfinitePlace E) := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp [primesOver_bot, IsTotallyComplex.finrank E] at hsplit
    omega
  have hpsplit : ((span {(p : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℤ (𝓞 E) := by
    rwa [RingOfIntegers.rank]
  have hcount := card_primesOver_eq_two_mul_of_mul_eq_algebraMap
    ((ringOfIntegersComplexConj E).restrictScalars ℤ) (a := z) (r := (p : ℤ)) (c := (c : ℤ))
    (by simpa using hp) (by simpa only [mem_span_singleton, Int.natCast_dvd_natCast] using hc)
    (fun P ↦ (ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
      (span {(p : ℤ)}) P.val hpsplit).1) (by simpa using hz)
  have h := congrArg ENat.toNat hcount
  simp only [ENat.toNat_card, ENat.toNat_mul, ENat.toNat_ofNat, Nat.card_coe_set_eq, hsplit,
    IsTotallyComplex.finrank E] at h
  simpa [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces] using h.symm

/-- For a finite set of completely split rational primes, a conjugate factor of their
product selects `#T` times the number of infinite places. The sigma type indexes the chosen
prime ideals together with their rational primes. -/
theorem natCard_sigma_primesOver_conjugateFactor {T : Finset ℕ} {z : 𝓞 E}
    (hsplit : ∀ p ∈ T, ((span {(p : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℚ E)
    (hz : z * ringOfIntegersComplexConj E z = ((∏ p ∈ T, p : ℕ) : 𝓞 E)) :
    Nat.card (Σ p : T, {P : (span {(p.val : ℤ)}).primesOver (𝓞 E) // z ∈ P.val}) =
      T.card * Fintype.card (InfinitePlace E) := by
  let (p : T) : Finite ((span {(p.val : ℤ)}).primesOver (𝓞 E)) :=
    Algebra.QuasiFinite.finite_primesOver _
  rw [Nat.card_sigma]
  have hprime (p : ℕ) (hp : p ∈ T) : p.Prime := by
    have hs := hsplit p hp
    have hp₀ : p ≠ 0 := by
      rintro rfl
      simp [primesOver_bot, IsTotallyComplex.finrank E] at hs
      omega
    obtain ⟨P, hP, hover⟩ := Set.nonempty_of_ncard_ne_zero (hs.trans_ne finrank_pos.ne')
    have : P.IsPrime := hP
    have : P.LiesOver (span {(p : ℤ)}) := hover
    exact Nat.prime_iff_prime_int.mpr ((span_singleton_prime (by exact_mod_cast hp₀)).mp
      (isPrime_of_liesOver P (span {(p : ℤ)})))
  have hfiber (p : T) :
      Nat.card {P : (span {(p.val : ℤ)}).primesOver (𝓞 E) // z ∈ P.val} =
        Fintype.card (InfinitePlace E) := by
    have hp := hprime p p.property
    refine natCard_primesOver_conjugateFactor (c := ∏ q ∈ T.erase p, q) ?_
      (hsplit p p.property) ?_
    · refine hp.prime.not_dvd_finsetProd fun q hq hdiv ↦ ?_
      exact (Finset.ne_of_mem_erase hq)
        (((hprime q (Finset.mem_of_mem_erase hq)).dvd_iff_eq hp.ne_one).mp hdiv)
    · have hprod : p.val * (∏ q ∈ T.erase p, q) = ∏ q ∈ T, q :=
        T.mul_prod_erase id p.property
      rwa [hprod]
  simp [hfiber]

end Ideal
