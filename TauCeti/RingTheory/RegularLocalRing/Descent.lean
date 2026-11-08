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

Globally, a ring faithfully flat in a regular ring is a regular ring
(`TauCeti.IsRegularRing.of_faithfullyFlat`), by passing to localizations at primes and a prime
of the target above each. In particular, regularity descends along any flat local homomorphism.
The closed fibre need not be a field or be regular. This is the local input for descent of
regularity of schemes along faithfully flat covers.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7 (i).
* `TauCeti.IsRegularRing.projectiveDimension_le_ringKrullDim_of_faithfullyFlat` and
  `TauCeti.isRegularLocalRing_iff_projectiveDimension_ne_top` supply the homological criteria.
-/

public section

open IsLocalRing CategoryTheory

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
fibre or a Noetherianity assumption on the source. -/
theorem of_flat_of_isLocalHom [IsLocalRing R] [IsRegularLocalRing S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] : IsRegularLocalRing R := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact of_faithfullyFlat (S := S)

end TauCeti.IsRegularLocalRing

/-- **Regularity descends along faithfully flat extensions by regular rings.** If a regular ring
`R` is faithfully flat over a ring `A`, then `A` is a regular ring. Noetherianity of `A` descends
as well, and no bound on the Krull dimension of `R` is needed: at a prime `p` of `A`, a prime `q`
of `R` over `p` makes `A_p → R_q` a flat local homomorphism into a regular local ring. -/
theorem TauCeti.IsRegularRing.of_faithfullyFlat {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsRegularRing S] [Module.FaithfullyFlat R S] : IsRegularRing R := by
  have : IsNoetherianRing R := .of_faithfullyFlat S
  refine isRegularRing_iff.mpr fun p _ ↦ ?_
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) ⟨p, ‹_›⟩
  have hqp : p = q.asIdeal.comap (algebraMap R S) := (congrArg PrimeSpectrum.asIdeal hq).symm
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p q.asIdeal (algebraMap R S) hqp).toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    RingHom.flat_algebraMap_iff.mp
      (RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) q.asIdeal p hqp)
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal)) :=
    Localization.isLocalHom_localRingHom p q.asIdeal (algebraMap R S) hqp
  exact TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom (S := Localization.AtPrime q.asIdeal)
