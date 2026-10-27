/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Submodule
public import TauCeti.AlgebraicGeometry.SpecOpenSubring

/-!
# The blowup of a submodule over an open subring of a Huber ring

Let `C` be an open subring of a Huber ring `A` and let `F ⊆ A` generate the unit ideal. The
blowup `Proj R(J) ⟶ Spec C` of `J = span C F` restricts to an isomorphism over the non-open
primes of `C`. This combines `TauCeti.AlgebraicGeometry.submoduleBlowup.isIso_toSpec_restrict`
with `Subring.isIso_morphismRestrict_nonOpenPrimes`. For a ring of definition `C` with ideal of
definition `I`, the non-open primes are those not containing `I`, and this is the situation of
Huber's proof.

## Main results

* `TauCeti.AlgebraicGeometry.submoduleBlowup.isIso_toSpec_restrict_nonOpenPrimes`: for an open
  subring `C` of a Huber ring, `Y ⟶ Spec C` is an isomorphism over the non-open primes of `C`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of Theorem 2.5, Case I, (1.2)(iii).
-/

public section

open CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.submoduleBlowup

open _root_.AlgebraicGeometry

/-- **The blowup over the non-open primes of an open subring.** Let `C` be an open subring of a
Huber ring `A` and let `F ⊆ A` generate the unit ideal. Then the blowup `Proj R(J) ⟶ Spec C` of
`J = span C F` restricts to an isomorphism over the non-open primes of `C`. For a ring of
definition `C` with ideal of definition `I`, these are the primes not containing `I`. -/
theorem isIso_toSpec_restrict_nonOpenPrimes {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Huber.IsHuberRing A] (C : Subring A) (hC : IsOpen (C : Set A))
    {F : Set A} (hF : Ideal.span F = ⊤) :
    IsIso (toSpec C F ∣_ C.nonOpenPrimes) :=
  isIso_toSpec_restrict C hF (C.isIso_morphismRestrict_nonOpenPrimes hC)

end TauCeti.AlgebraicGeometry.submoduleBlowup
