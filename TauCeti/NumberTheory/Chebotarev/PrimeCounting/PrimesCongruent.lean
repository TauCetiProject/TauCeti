/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
public import TauCeti.NumberTheory.Chebotarev.PrimesCongruent
import TauCeti.NumberTheory.Cyclotomic.Aut

/-!
# Natural density of cyclotomic Frobenius fibres and arithmetic progressions

Natural-density Chebotarev gives density `1 / φ(m)` for each arithmetic Frobenius fibre of
`ℚ(ζₘ)`. The cyclotomic Frobenius formula identifies the fibre tagged by `a` with primes whose
norm is congruent to `a` modulo `m`, up to finitely many primes dividing the level. Thus each
invertible arithmetic progression has the same natural density, measured relative to all primes.
No restriction on the nonzero level is needed: the possible discrepancy at two for levels
congruent to two modulo four is finite.

In particular, each of the four fibres of `ℚ(ζ₅)` has natural density `1/4`, agreeing with its
Dirichlet density. The existing exact fibre dictionary sends arithmetic Frobenius to the norm
modulo five, so the tags `2` and `3` are not interchanged.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2, for cyclotomic Frobenius.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13, for Chebotarev density.
-/

public section

open IsDedekindDomain IsCyclotomicExtension
open scoped NumberField

namespace NumberField.Chebotarev

/-- Over `ℚ`, the cyclotomic Frobenius fibre tagged by a unit modulo `m` has natural density
`1 / φ(m)`. -/
theorem hasNaturalDensity_frobeniusPrimeSet_galEquivZMod_symm
    (F : Type*) [Field F] [NumberField F] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} ℚ F] [IsGalois ℚ F] (a : (ZMod m)ˣ) :
    NumberField.Set.HasNaturalDensity
      (frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod m F).symm a)))
      (1 / (Nat.totient m : ℝ)) := by
  have := IsCyclotomicExtension.isMulCommutative {m} ℚ F
  have h := hasNaturalDensity_frobeniusPrimeSet ℚ F
    (ConjClasses.mk ((Rat.galEquivZMod m F).symm a))
  rwa [Nat.card_coe_set_eq, ConjClasses.ncard_carrier_mk_of_mem_center
    (Subgroup.mem_center_iff.mpr fun _ ↦ mul_comm' _ _), Nat.cast_one,
    card_aut_eq_totient ℚ F (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))] at h

/-- Each arithmetic Frobenius fibre of a fifth cyclotomic field has natural density `1/4`,
the same value as its Dirichlet density. -/
theorem hasNaturalDensity_frobeniusPrimeSet_cyclotomic_five
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {5} ℚ F] [IsGalois ℚ F]
    (a : (ZMod 5)ˣ) :
    NumberField.Set.HasNaturalDensity
      (frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod 5 F).symm a)))
      (1 / 4) := by
  simpa [Nat.totient_prime (by decide : Nat.Prime 5)] using
    hasNaturalDensity_frobeniusPrimeSet_galEquivZMod_symm F 5 a

/-- **Natural density of primes in arithmetic progressions.** At every nonzero level `m`,
the primes of `𝓞 ℚ` whose norms are congruent to an invertible residue `a` have natural density
`1 / φ(m)`. The congruence is the arithmetic Frobenius tag, without inversion. -/
theorem hasNaturalDensity_primesCongruent (m a : ℕ) [NeZero m]
    (ha : IsUnit (a : ZMod m)) :
    NumberField.Set.HasNaturalDensity
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m}
      (1 / (Nat.totient m : ℝ)) := by
  let : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  have := IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
  obtain ⟨u, hu⟩ := ha
  have h := (hasNaturalDensity_frobeniusPrimeSet_galEquivZMod_symm
    (CyclotomicField m ℚ) m u).of_finite_symmDiff
      (S := {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod m) = u})
      (by simpa only [symmDiff_comm] using
        finite_symmDiff_frobeniusPrimeSet_galEquivZMod_symm (CyclotomicField m ℚ) m u)
  simpa only [hu, ZMod.natCast_eq_natCast_iff'] using h

end NumberField.Chebotarev
