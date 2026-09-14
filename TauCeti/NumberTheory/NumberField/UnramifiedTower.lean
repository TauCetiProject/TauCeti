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
import TauCeti.RingTheory.Unramified.RingEquiv

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

A tower is often presented as an intermediate field `E` of `L / ℚ` together with an intermediate
field `B` of `E / ℚ`, while the unramifiedness hypothesis is available for the copy
`IntermediateField.lift B` of `B` inside `L`. The two copies of `B` are different types, so
`NumberField.isUnramifiedIn_of_isUnramifiedIn_lift` combines the descent with the transport of
unramifiedness between them.

## Main results

* `NumberField.isUnramifiedAway_of_intermediateField`: unramifiedness outside a finite set of
  finite places descends to an intermediate field.
* `NumberField.isUnramifiedIn_of_isUnramifiedIn_lift`: if `L` is unramified over the copy of `B`
  inside it, then an intermediate field `E` containing `B` is unramified over `B`.
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

/-- **An intermediate field inherits unramifiedness over a subfield of it.** Let `E` be an
intermediate field of `L / ℚ` and `B` an intermediate field of `E / ℚ`. If every prime of the copy
`IntermediateField.lift B` of `B` inside `L` is unramified in `L`, then every prime of `B` is
unramified in `E`.

The hypothesis and the conclusion speak about the two different models of the same field, so the
proof transports unramifiedness along `IntermediateField.liftAlgEquiv B` before descending from
`L` to `E`. -/
theorem isUnramifiedIn_of_isUnramifiedIn_lift {L : Type*} [Field L] [NumberField L]
    {E : IntermediateField ℚ L} (B : IntermediateField ℚ E)
    (hur : ∀ p : Ideal (𝓞 (IntermediateField.lift B)), p.IsPrime →
      Algebra.IsUnramifiedIn (𝓞 L) p)
    (q : Ideal (𝓞 B)) [q.IsPrime] :
    Algebra.IsUnramifiedIn (𝓞 E) q := by
  let e : 𝓞 B ≃+* 𝓞 (IntermediateField.lift B) :=
    (RingOfIntegers.mapAlgEquiv (IntermediateField.liftAlgEquiv B)).toRingEquiv
  have he : (algebraMap (𝓞 (IntermediateField.lift B)) (𝓞 L)).comp
      (e : 𝓞 B →+* 𝓞 (IntermediateField.lift B)) = algebraMap (𝓞 B) (𝓞 L) := by
    refine RingHom.ext fun x ↦ RingOfIntegers.ext ?_
    exact IntermediateField.liftAlgEquiv_apply B (x : B)
  have hL : Algebra.IsUnramifiedIn (𝓞 L) q :=
    RingEquiv.isUnramifiedIn_of_eq_comap e he (Ideal.comap_of_equiv e).symm
      (hur (q.comap (e.symm : 𝓞 (IntermediateField.lift B) →+* 𝓞 B)) inferInstance)
  exact TauCeti.RamificationInertia.isUnramifiedIn_of_isUnramifiedIn hL

end NumberField
