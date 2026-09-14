/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramifiedness does not depend on the model of the base

`Algebra.IsUnramifiedAt R q` and `Algebra.IsUnramifiedIn S p` are stated relative to a base ring.
Two isomorphic bases acting on the same algebra through matching structure maps therefore see the
same unramified primes. This file records that invariance, in the two shapes the base appears in:
at a fixed prime of the top ring, and for a prime of the base itself.

It is the base-side counterpart of `TauCeti.RingTheory.Unramified.AlgEquiv`, which transports
unramifiedness along an isomorphism of the top algebra. Both are needed when a field is presented
twice — for instance as an intermediate field of an intermediate field, and as an intermediate
field of the ambient field.

## Main results

* `RingEquiv.isUnramifiedAt_of_comp_eq`: unramifiedness at a prime of the top ring passes between
  isomorphic bases.
* `RingEquiv.isUnramifiedIn_of_eq_comap`: unramifiedness of a prime of the base passes to the
  corresponding prime of an isomorphic base.
-/

public section

namespace RingEquiv

variable {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R S] [Algebra R' S]

/-- **Unramifiedness at a prime is invariant under an isomorphism of the base.** If `e : R ≃+* R'`
identifies the two structure maps to `S`, then a prime of `S` unramified over `R` is unramified
over `R'`. -/
theorem isUnramifiedAt_of_comp_eq (e : R ≃+* R')
    (he : (algebraMap R' S).comp (e : R →+* R') = algebraMap R S)
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P] :
    Algebra.IsUnramifiedAt R' P := by
  let : Algebra R R' := e.toRingHom.toAlgebra
  have : IsScalarTower R R' S := IsScalarTower.of_algebraMap_eq' he.symm
  exact Algebra.IsUnramifiedAt.of_restrictScalars R P

/-- The prime of `R` below a prime of `S` is the contraction along `e` of the prime of `R'` below
it, when `e : R ≃+* R'` identifies the two structure maps to `S`. -/
theorem under_eq_comap_under (e : R ≃+* R')
    (he : (algebraMap R' S).comp (e : R →+* R') = algebraMap R S) (P : Ideal S) :
    P.under R = (P.under R').comap (e : R →+* R') := by
  rw [Ideal.under, Ideal.under, ← he, ← Ideal.comap_comap]

/-- **Unramifiedness of a prime of the base is invariant under an isomorphism of the base.** If
`e : R ≃+* R'` identifies the two structure maps to `S`, then a prime `p` of `R` is unramified in
`S` as soon as the prime `p'` of `R'` it contracts from is. -/
theorem isUnramifiedIn_of_eq_comap (e : R ≃+* R')
    (he : (algebraMap R' S).comp (e : R →+* R') = algebraMap R S)
    {p : Ideal R} {p' : Ideal R'} (hp : p = p'.comap (e : R →+* R'))
    (h : Algebra.IsUnramifiedIn S p') : Algebra.IsUnramifiedIn S p := by
  intro P hP hlo
  have hcomap : p'.comap (e : R →+* R') = (P.under R').comap (e : R →+* R') := by
    rw [← hp, Ideal.LiesOver.over (p := p) (P := P), under_eq_comap_under e he]
  have : P.LiesOver p' :=
    ⟨Ideal.comap_injective_of_surjective (e : R →+* R') e.surjective hcomap⟩
  have : Algebra.IsUnramifiedAt R' P := h P hP this
  refine isUnramifiedAt_of_comp_eq e.symm ?_ P
  rw [← he, RingHom.comp_assoc]
  simp

end RingEquiv
