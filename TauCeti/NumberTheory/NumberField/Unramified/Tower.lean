/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Unramifiedness descends along a tower of number fields

For a tower `L / M / K` of number fields, unramifiedness over `K` of every prime of `𝓞 L` above a
place of `𝓞 K` descends to the primes of `𝓞 M` above it. The prime-by-prime statement is
`TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`, proved there for an
arbitrary base ring; what this file adds is the version quantified over the places outside a finite
set, which is the shape the unramified-away hypotheses take.

The hypothesis and conclusion are stated as the quantified `Algebra.IsUnramifiedAt` condition
rather than through `Algebra.IsUnramifiedIn`, which is the form the Artin symbol takes as its
defining side condition.

The same descent, read simultaneously at every prime outside a finite set of finite places of
`K`, is `NumberField.isUnramifiedAway_of_intermediateField`; that is the form a construction
defined away from a finite set of primes consumes, since it turns one hypothesis about the top
field into the corresponding hypothesis about every subextension.

## Main results

* `NumberField.isUnramifiedAway_of_intermediateField`: unramifiedness outside a finite set of
  finite places descends to an intermediate field.
-/

public section

open IsDedekindDomain

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Unramifiedness outside a finite set of finite places descends to an intermediate field.**
If every prime of `L` above a place of `K` outside `S` is unramified over `K`, then so is every
prime of an intermediate field `M` above such a place. This is what makes the unramified
hypothesis for a subextension a consequence of the one for the top field rather than a second
assumption. -/
theorem isUnramifiedAway_of_intermediateField (M : Type*) [Field M] [NumberField M]
    {L : Type*} [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q :=
  fun v hv P _ _ ↦
    TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn (S := 𝓞 L) (hur v hv) P

end NumberField
