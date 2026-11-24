/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Noetherian
public import TauCeti.RingTheory.Dagger.Preparation
public import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Monsky–Washnitzer algebras are unique factorisation domains

Over a complete ultrametric normed field `K`, the Monsky–Washnitzer algebra `K⟨X⟩†` in finitely
many variables is a unique factorisation domain.

Write `W = K⟨X⟩†` and `W' = K⟨X, Y⟩†`, with `Y = X none`, and evaluate polynomials at `Y` by
`washnitzerAlgebra.polynomialToOption : W[Y] → W'`. Factoriality follows by induction on the
number of variables. Since `W'` is a noetherian domain, it suffices that every irreducible
`f ∈ W'` is prime. A triangular automorphism makes `f` distinguished in `Y` with a unit
coefficient in the distinguished degree, and overconvergent Weierstrass preparation writes it as
a unit multiple of a monic polynomial `ω ∈ W[Y]`
(`washnitzerAlgebra.exists_associated_polynomialToOption`). Overconvergent Weierstrass division
compares divisibility by `ω` in `W[Y]` and in `W'`, so `ω` is irreducible in `W[Y]`, hence prime,
since `W[Y]` is a unique factorisation domain by induction and Gauss's lemma. So `ω` and `f` are
prime in `W'`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.uniqueFactorizationMonoid`: `K⟨X⟩†` is a unique factorisation
  domain for finitely many variables.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.6,
  Theorem 1 (the same statement for Tate algebras).

The argument follows `TauCeti.MvPowerSeries.uniqueFactorizationMonoid` in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization`, with the comparison lemmas
`TauCeti.Dagger.washnitzerAlgebra.irreducible_of_irreducible_polynomialToOption` and
`TauCeti.Dagger.washnitzerAlgebra.prime_polynomialToOption_iff` of
`TauCeti.RingTheory.Dagger.Weierstrass` and overconvergent preparation in place of their
fixed-radius counterparts.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K

section UniqueFactorization

variable [CompleteSpace K]

/-- The inductive step: if `K⟨X⟩†` is a unique factorisation domain, so is `K⟨X, Y⟩†`. -/
private theorem uniqueFactorizationMonoid_option [Finite σ] [UniqueFactorizationMonoid W] :
    UniqueFactorizationMonoid W' := by
  refine { irreducible_iff_prime := fun {f} ↦ ⟨fun hf ↦ ?_, Prime.irreducible⟩ }
  -- Up to an automorphism `E`, `f` is associated to `ω(Y)` with `ω` monic and distinguished.
  obtain ⟨E, s, ω, hω, hm, hassoc⟩ := exists_associated_polynomialToOption f hf.ne_zero
  have hirr : Irreducible (polynomialToOption ω) :=
    (MulEquiv.irreducible_iff E).mp (hassoc.irreducible hf)
  -- `ω` is irreducible, hence prime, in the unique factorisation domain `K⟨X⟩†[Y]`.
  have hωp : Prime ω := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_irreducible_polynomialToOption hω hm hirr)
  -- So `ω(Y)`, hence `f`, is prime in `K⟨X, Y⟩†`.
  exact hassoc.symm.prime
    ((MulEquiv.prime_iff E).mpr ((prime_polynomialToOption_iff hω hm).mpr hωp))

/-- **Monsky–Washnitzer algebras are unique factorisation domains.** Over a complete ultrametric
normed field `K`, the algebra `K⟨X⟩†` of overconvergent power series in finitely many variables
is a unique factorisation domain. -/
instance uniqueFactorizationMonoid [Finite σ] : UniqueFactorizationMonoid W :=
  Finite.induction_empty_option
    (P := fun σ ↦ ∀ [Finite σ], UniqueFactorizationMonoid (washnitzerAlgebra σ K))
    (fun {α β} e h _ ↦
      have : Finite α := .of_equiv β e.symm
      (renameAlgEquiv (R := K) e).toMulEquiv.uniqueFactorizationMonoid h)
    ((RingEquiv.ofBijective (algebraMap K (washnitzerAlgebra PEmpty K))
      ⟨(algebraMap K _).injective, algebraMap_surjective⟩).toMulEquiv.uniqueFactorizationMonoid
        inferInstance)
    (fun {_} _ h _ ↦
      have := h
      uniqueFactorizationMonoid_option) σ

end UniqueFactorization

end TauCeti.Dagger.washnitzerAlgebra
