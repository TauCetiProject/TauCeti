/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
public import TauCeti.NumberTheory.Cyclotomic.Surjectivity
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Surjectivity of rational cyclotomic characters

The absolute Galois group of `ℚ` realizes every unit modulo each positive integer, and
every `p`-adic unit for each prime `p`, through its action on roots of unity. Irreducibility
of cyclotomic polynomials over `ℚ` supplies the finite-level surjectivity; compactness of
the absolute Galois group supplies a single automorphism realizing all `p`-power levels.
The `p`-adic statements cover both `localCyclotomicCharacter` on the absolute Galois group
and Mathlib's `cyclotomicCharacter` on ring automorphisms of `AlgebraicClosure ℚ`.

These statements concern the full rational absolute Galois group. They do not assert
surjectivity over arbitrary number fields, nor simultaneous realization of independently
specified `p`-adic units at different primes.

## References

* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.7.4.
-/

public section

namespace TauCeti

/-- Every unit modulo a positive integer is realized by the action of an element of
`G_ℚ` on the roots of unity of that order. -/
theorem surjective_modularCyclotomicCharacter_rat (n : ℕ) [NeZero n] :
    Function.Surjective (fun σ : Field.absoluteGaloisGroup ℚ ↦
      modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) n) σ.toRingEquiv) :=
  modularCyclotomicCharacter_surjective_of_irreducible (K := ℚ) _
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))

/-- The `p`-adic cyclotomic character of `G_ℚ` is surjective for every prime `p`, including
`p = 2`. -/
theorem surjective_localCyclotomicCharacter_rat (p : ℕ) [Fact p.Prime] :
    Function.Surjective (localCyclotomicCharacter p ℚ) :=
  localCyclotomicCharacter_surjective_of_irreducible fun n ↦
    Polynomial.cyclotomic.irreducible_rat (pow_pos (Fact.out : p.Prime).pos n)

/-- Mathlib's `p`-adic cyclotomic character on ring automorphisms of `AlgebraicClosure ℚ`
is surjective for every prime `p`. -/
theorem surjective_cyclotomicCharacter_rat (p : ℕ) [Fact p.Prime] :
    Function.Surjective (cyclotomicCharacter (AlgebraicClosure ℚ) p) := by
  intro u
  obtain ⟨σ, hσ⟩ := surjective_localCyclotomicCharacter_rat p u
  exact ⟨σ.toRingEquiv, (localCyclotomicCharacter_apply p ℚ σ).symm.trans hσ⟩

end TauCeti
