/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Multiplicities of ideals in a completed integer ring

Extending an ideal of a Dedekind domain to the integer ring of its completion preserves its
multiplicity at the selected prime. The prime generates the maximal ideal of the completion,
so its ramification index in this extension is one. This comparison lets coefficients of
global ideals be read in the completed ring.
-/

public section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The coefficient at `v` of a nonzero ideal equals the coefficient at the maximal ideal after
extension to the integer ring of the `v`-adic completion. -/
@[simp]
theorem multiplicity_map_adicCompletionIntegers (v : HeightOneSpectrum R)
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (I.map (algebraMap R (v.adicCompletionIntegers K))) =
      multiplicity v.asIdeal I := by
  let B := v.adicCompletionIntegers K
  let P : Ideal B := IsLocalRing.maximalIdeal B
  have hmap : Ideal.map (algebraMap R B) v.asIdeal = P :=
    v.map_asIdeal_adicCompletionIntegers (K := K)
  have hP : P ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hPprime : P.IsPrime := inferInstance
  have : P.LiesOver v.asIdeal :=
    (Ideal.liesOver_iff_dvd_map hPprime.ne_top).2
      (by rw [hmap])
  have hidx : Ideal.ramificationIdx' v.asIdeal P = 1 := by
    rw [← hmap]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmap]; exact hPprime.ne_top)
      (by rw [hmap]; exact hP)
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hI
    v.irreducible (Ideal.prime_of_isPrime hP hPprime).irreducible hP
  rw [hidx, Nat.cast_one, one_mul,
    (FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime hP hPprime)
        (Ideal.map_ne_bot_of_ne_bot hI)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left v.prime hI).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

end IsDedekindDomain.HeightOneSpectrum

end
