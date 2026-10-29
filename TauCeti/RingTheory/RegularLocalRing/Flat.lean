/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Unramified.LocalRing
public import TauCeti.RingTheory.KrullDimension.Fiber
public import TauCeti.RingTheory.LocalRing.MaximalIdeal.Flat

/-!
# Regularity along flat local homomorphisms with a field as closed fibre

Let `R → S` be a flat homomorphism of Noetherian local rings under which the maximal ideal of `R`
generates the maximal ideal of `S`. Then `R` is regular if and only if `S` is: the maximal ideals
of `R` and `S` need the same number of generators, and `R` and `S` have the same Krull dimension.
The ascent of regularity is the special case, with a field as closed fibre, of the ascent along
flat local homomorphisms with regular closed fibre. The descent of regularity is the special case
of the descent along arbitrary flat local homomorphisms; it applies for instance to the completion
of a Noetherian local ring.

Formally unramified local homomorphisms essentially of finite type satisfy the hypothesis on the
maximal ideals, so regularity ascends along local homomorphisms of this kind which are flat, such
as the localizations of étale algebras at primes. This is the local input for showing that an
algebra smooth over a regular ring is regular.

## Main declarations

* `TauCeti.isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq`: along a flat homomorphism of
  Noetherian local rings with `𝔪_R S = 𝔪_S`, the target is regular if and only if the source is;
* `TauCeti.IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq`: regularity ascends along such a
  homomorphism;
* `TauCeti.IsRegularLocalRing.of_flat_of_formallyUnramified`: the same for a flat, formally
  unramified local homomorphism essentially of finite type.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7.
-/

public section

namespace TauCeti

open _root_.IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Along a flat homomorphism of Noetherian local rings under which the maximal ideal of the
source generates the maximal ideal of the target, the target is regular if and only if the source
is. -/
theorem isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq [IsLocalRing R] [IsNoetherianRing R]
    [IsLocalRing S] [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    _root_.IsRegularLocalRing S ↔ _root_.IsRegularLocalRing R := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff,
    IsLocalRing.spanFinrank_maximalIdeal_eq_of_flat_of_map_maximalIdeal_eq h,
    ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq h]

namespace IsRegularLocalRing

/-- Regularity ascends along a flat homomorphism of Noetherian local rings under which the maximal
ideal of the source generates the maximal ideal of the target. -/
theorem of_flat_of_map_maximalIdeal_eq [IsRegularLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsRegularLocalRing S :=
  (isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq h).mpr ‹_›

/-- Regularity ascends along a flat, formally unramified local homomorphism essentially of finite
type between Noetherian local rings. -/
theorem of_flat_of_formallyUnramified [IsRegularLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    IsRegularLocalRing S :=
  of_flat_of_map_maximalIdeal_eq (Algebra.FormallyUnramified.map_maximalIdeal (R := R))

end IsRegularLocalRing

end TauCeti
