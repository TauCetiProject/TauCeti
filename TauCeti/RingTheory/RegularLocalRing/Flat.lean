/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Regularity ascends along flat unramified local homomorphisms

Let `R → S` be a flat homomorphism of Noetherian local rings under which the maximal ideal of `R`
generates the maximal ideal of `S`. If `R` is regular, so is `S`: the images of `dim R`
generators of `𝔪_R` generate `𝔪_S`, and flatness gives going down, hence `dim R ≤ dim S`.
This is the special case, with a field as closed fibre, of the ascent of regularity along flat
local homomorphisms with regular closed fibre.

Formally unramified local homomorphisms essentially of finite type satisfy the hypothesis on the
maximal ideals, so regularity ascends along local homomorphisms of this kind which are flat, such
as the localizations of étale algebras at primes. This is the local input for showing that an
algebra smooth over a regular ring is regular.

## Main declarations

* `TauCeti.IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq`: regularity ascends along a flat
  homomorphism of Noetherian local rings with `𝔪_R S = 𝔪_S`;
* `TauCeti.IsRegularLocalRing.of_flat_of_formallyUnramified`: the same for a flat, formally
  unramified local homomorphism essentially of finite type.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7.
-/

public section

namespace TauCeti

open _root_.IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsRegularLocalRing

/-- Regularity ascends along a flat homomorphism of Noetherian local rings under which the maximal
ideal of the source generates the maximal ideal of the target. -/
theorem of_flat_of_map_maximalIdeal_eq [IsRegularLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsRegularLocalRing S := by
  have : IsLocalHom (algebraMap R S) :=
    ((local_hom_TFAE (algebraMap R S)).out 1 3).mpr h.le
  apply _root_.IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hspan : (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank :=
    h ▸ Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal R).fg_of_isNoetherianRing
  -- Going down along the flat map bounds the height of `𝔪_R` by that of `𝔪_S`.
  have hdim : ringKrullDim R ≤ ringKrullDim S := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)]
    exact_mod_cast le_self_add
  calc ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
        exact_mod_cast hspan
    _ = ringKrullDim R := _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := hdim

/-- Regularity ascends along a flat, formally unramified local homomorphism essentially of finite
type between Noetherian local rings. -/
theorem of_flat_of_formallyUnramified [IsRegularLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    IsRegularLocalRing S :=
  of_flat_of_map_maximalIdeal_eq (Algebra.FormallyUnramified.map_maximalIdeal (R := R))

end IsRegularLocalRing

end TauCeti
