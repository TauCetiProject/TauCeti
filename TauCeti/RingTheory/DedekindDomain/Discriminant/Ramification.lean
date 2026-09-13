/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindDomain.RelNorm
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Separable

/-!
# Ramification and the relative discriminant

For a separable extension of fraction fields of Dedekind domains, a nonzero prime divides the
relative discriminant exactly when some prime above it is ramified. Here ramification is expressed
intrinsically by failure of `Algebra.IsUnramifiedAt`; no residue-field separability is required.

## Main results

* `TauCeti.dvd_relDiscr_iff_exists_not_isUnramifiedAt`: a prime divides the relative discriminant
  exactly when the extension ramifies at a prime above it.

This is the relative-discriminant ramification criterion of Neukirch, *Algebraic Number Theory*,
Chapter III, §2, Proposition 12.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **A nonzero prime divides the relative discriminant exactly when a prime above it is
ramified.** Ramification means failure of `Algebra.IsUnramifiedAt`, so this statement does not
need the residue extensions to be separable. -/
theorem dvd_relDiscr_iff_exists_not_isUnramifiedAt {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    p ∣ relDiscr A B ↔
      ∃ P : p.primesOver B, ¬ Algebra.IsUnramifiedAt A (P : Ideal B) := by
  rw [relDiscr_def, Ideal.dvd_relNorm_iff_exists_liesOver_dvd hp]
  apply exists_congr
  intro P
  constructor
  · exact dvd_differentIdeal_iff.mp
  · exact dvd_differentIdeal_iff.mpr

end TauCeti

end
