/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RingHom.Flat
import TauCeti.RingTheory.Flat.Noetherian

/-!
# Descent of regularity along flat local homomorphisms

A ring faithfully flat in a regular local ring is regular local. Neither locality nor
Noetherianity of the source is necessary: both descend by faithful flatness. The projective
dimension of the source residue field is then bounded by the dimension of the target, so
Serre's criterion proves regularity.

In particular, regularity descends along any flat local homomorphism
(`TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom`). The closed fibre need not be a field or be
regular. This is the local input for descent of regularity of schemes along faithfully flat
covers.

Globally, a ring faithfully flat in a regular ring is a regular ring
(`TauCeti.IsRegularRing.of_faithfullyFlat`), by passing to localizations at primes and a prime
of the target above each. Consequently regularity of a base change `S ⊗[R] C` descends to
`S ⊗[R] B` when `C` is faithfully flat over `B`
(`TauCeti.IsRegularRing.tensorProduct_of_faithfullyFlat`); this is the input for descending
regular ring maps along faithfully flat maps.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7 (i).
* `TauCeti.IsRegularRing.projectiveDimension_le_ringKrullDim_of_faithfullyFlat` and
  `TauCeti.isRegularLocalRing_iff_projectiveDimension_ne_top` supply the homological criteria.
-/

public section

open IsLocalRing CategoryTheory TensorProduct

universe u v

namespace TauCeti.IsRegularLocalRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A ring faithfully flat in a regular local ring is regular local. Locality and
Noetherianity of the source follow from faithful flatness, rather than being hypotheses. -/
theorem of_faithfullyFlat [IsRegularLocalRing S]
    [Module.FaithfullyFlat R S] : IsRegularLocalRing R := by
  have := Module.FaithfullyFlat.isLocalRing R S
  have : IsNoetherianRing R := .of_faithfullyFlat S
  apply (isRegularLocalRing_iff_projectiveDimension_ne_top (R := R)).mpr
  exact ((IsRegularRing.projectiveDimension_le_ringKrullDim_of_faithfullyFlat
    (R := S) (Shrink.{u} (R ⧸ maximalIdeal R))).trans_lt
      (ringKrullDim_lt_top (R := S))).ne

/-- Regularity descends along a flat local homomorphism, without a hypothesis on the closed
fibre or a locality or Noetherianity assumption on the source. -/
theorem of_flat_of_isLocalHom [IsRegularLocalRing S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] : IsRegularLocalRing R := by
  have := (algebraMap R S).domain_isLocalRing
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact of_faithfullyFlat (S := S)

end TauCeti.IsRegularLocalRing

/-- **Regularity descends along faithfully flat extensions by regular rings.** If a regular ring
`S` is faithfully flat over a ring `R`, then `R` is a regular ring (in particular Noetherian). -/
theorem TauCeti.IsRegularRing.of_faithfullyFlat {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsRegularRing S] [Module.FaithfullyFlat R S] : IsRegularRing R := by
  have : IsNoetherianRing R := .of_faithfullyFlat S
  refine isRegularRing_iff.mpr fun p _ ↦ ?_
  obtain ⟨q, _, _⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) p
  let := Localization.AtPrime.algebraOfLiesOver p q
  exact TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom (S := Localization.AtPrime q)

/-- **Regularity descends along faithfully flat base changes.** If `C` is a faithfully flat
`B`-algebra over `R` and `S ⊗[R] C` is a regular ring for an `R`-algebra `S`, then `S ⊗[R] B` is
a regular ring. -/
theorem TauCeti.IsRegularRing.tensorProduct_of_faithfullyFlat {R : Type*} (S : Type*)
    {B : Type*} (C : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing C] [Algebra R S]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Module.FaithfullyFlat B C]
    [IsRegularRing (S ⊗[R] C)] : IsRegularRing (S ⊗[R] B) := by
  -- `(B ⊗[R] S) ⊗[B] C ≃ C ⊗[B] (B ⊗[R] S) ≃ C ⊗[R] S ≃ S ⊗[R] C`
  let e : (B ⊗[R] S) ⊗[B] C ≃+* S ⊗[R] C :=
    ((Algebra.TensorProduct.comm B _ C).trans
      (Algebra.TensorProduct.cancelBaseChange R B B C S)).toRingEquiv.trans
        (Algebra.TensorProduct.comm R C S).toRingEquiv
  have : IsRegularRing ((B ⊗[R] S) ⊗[B] C) := .of_ringEquiv e.symm
  have : IsRegularRing (B ⊗[R] S) := of_faithfullyFlat (S := (B ⊗[R] S) ⊗[B] C)
  exact .of_ringEquiv (Algebra.TensorProduct.comm R B S).toRingEquiv
