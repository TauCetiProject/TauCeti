/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Descent of regularity along flat local homomorphisms

A local ring faithfully flat in a regular local ring is regular. No Noetherianity assumption
on the source is necessary: Noetherianity itself descends by faithful flatness. The projective
dimension of the source residue field is then bounded by the dimension of the target, so
Serre's criterion proves regularity.

In particular, regularity descends along any flat local homomorphism. The closed fibre need
not be a field or be regular. This is the local input for descent of regularity of schemes
along faithfully flat covers.

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

/-- A local ring faithfully flat in a regular local ring is regular. Noetherianity of the
source follows from faithful flatness, rather than being an additional hypothesis. -/
theorem of_faithfullyFlat [IsLocalRing R] [IsRegularLocalRing S]
    [Module.FaithfullyFlat R S] : IsRegularLocalRing R := by
  have : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := R) (A := S) (M := R) inferInstance
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
