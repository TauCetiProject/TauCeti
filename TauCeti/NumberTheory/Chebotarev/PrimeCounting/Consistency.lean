/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount

/-!
# Natural density of Frobenius fibres: the ramified primes and Dirichlet density

Let `L / K` be a finite Galois extension of number fields with group `G`, and let `C` be a
conjugacy class of `G`. Natural-density Chebotarev, `hasNaturalDensity_frobeniusPrimeSet`, gives
the primes of `𝓞 K` with Frobenius class `C` natural density `#C / #G`. This file records the two
consistency statements that accompany it.

* The finitely many primes of `K` ramified in `L` are invisible to natural density: their
  complement has natural density `1`, and a set of primes that differs from a Frobenius fibre in
  finitely many primes has natural density `δ` exactly when `δ = #C / #G`.
* Natural density and Dirichlet density agree on Frobenius fibres. In general natural density
  implies Dirichlet density (`NumberField.Set.hasDirichletDensity_of_hasNaturalDensity`) but not
  conversely; for a set differing from a Frobenius fibre in finitely many primes the two notions
  coincide, because the Dirichlet-density and natural-density Chebotarev theorems produce the same
  value `#C / #G`.

## Main results

* `NumberField.Chebotarev.hasNaturalDensity_compl_ramifiedPrimes`: the primes of `𝓞 K` unramified
  in `L` have natural density `1`.
* `NumberField.Chebotarev.hasNaturalDensity_iff_of_finite_symmDiff_frobeniusPrimeSet`: a set of
  primes differing from a Frobenius fibre in finitely many primes has natural density `δ` if and
  only if `δ = #C / #G`.
* `hasNaturalDensity_iff_hasDirichletDensity_of_finite_symmDiff_frobeniusPrimeSet` and
  `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet_iff_hasDirichletDensity`: on such a
  set, and in particular on a Frobenius fibre, natural density `δ` and Dirichlet density `δ` are
  equivalent.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13, for Dirichlet density, natural
  density, and the Chebotarev density theorem.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)
open scoped NumberField symmDiff

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The unramified primes have natural density one.** Only finitely many primes of `𝓞 K` ramify
in `L`, so their complement carries all of the natural density. -/
theorem hasNaturalDensity_compl_ramifiedPrimes :
    NumberField.Set.HasNaturalDensity
      ((↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ) 1 := by
  simpa using
    (NumberField.Set.hasNaturalDensity_of_finite (ramifiedPrimes K L).finite_toSet).compl

variable {K L} [IsGalois K L]

/-- **Natural-density Chebotarev up to finitely many primes.** A set `S` of primes of `𝓞 K` that
differs from the Frobenius fibre of a conjugacy class `C` of `Gal(L/K)` in only finitely many
primes has natural density `δ` if and only if `δ = #C / #Gal(L/K)`. -/
theorem hasNaturalDensity_iff_of_finite_symmDiff_frobeniusPrimeSet
    {S : Set (HeightOneSpectrum (𝓞 K))} {C : ConjClasses (L ≃ₐ[K] L)} {δ : ℝ}
    (hS : (S ∆ frobeniusPrimeSet K L C).Finite) :
    NumberField.Set.HasNaturalDensity S δ ↔
      δ = (Nat.card C.carrier : ℝ) / (Nat.card (L ≃ₐ[K] L) : ℝ) := by
  have hC := hasNaturalDensity_frobeniusPrimeSet K L C
  rw [NumberField.Set.hasNaturalDensity_iff_of_finite_symmDiff hS]
  exact ⟨fun h ↦ h.unique hC, fun h ↦ h ▸ hC⟩

/-- **Natural and Dirichlet density agree near a Frobenius fibre.** A set `S` of primes of `𝓞 K`
that differs from the Frobenius fibre of a conjugacy class of `Gal(L/K)` in only finitely many
primes has natural density `δ` if and only if it has Dirichlet density `δ`. -/
theorem hasNaturalDensity_iff_hasDirichletDensity_of_finite_symmDiff_frobeniusPrimeSet
    {S : Set (HeightOneSpectrum (𝓞 K))} {C : ConjClasses (L ≃ₐ[K] L)} {δ : ℝ}
    (hS : (S ∆ frobeniusPrimeSet K L C).Finite) :
    NumberField.Set.HasNaturalDensity S δ ↔ NumberField.Set.HasDirichletDensity S δ := by
  rw [hasNaturalDensity_iff_of_finite_symmDiff_frobeniusPrimeSet hS,
    hasDirichletDensity_iff_of_finite_symmDiff_frobeniusPrimeSet hS]

/-- **Natural and Dirichlet density agree on a Frobenius fibre.** The primes of `𝓞 K` with
Frobenius class `C` in `Gal(L/K)` have natural density `δ` if and only if they have Dirichlet
density `δ`; both hold exactly for `δ = #C / #Gal(L/K)`. -/
theorem hasNaturalDensity_frobeniusPrimeSet_iff_hasDirichletDensity
    (C : ConjClasses (L ≃ₐ[K] L)) {δ : ℝ} :
    NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L C) δ ↔
      NumberField.Set.HasDirichletDensity (frobeniusPrimeSet K L C) δ :=
  hasNaturalDensity_iff_hasDirichletDensity_of_finite_symmDiff_frobeniusPrimeSet (C := C)
    (by simp)

end NumberField.Chebotarev
