/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.AlgebraicGeometry.Scheme.Connectedness

/-!
# Connectedness of the punctured spectrum

The punctured spectrum of a Noetherian local ring of depth at least two is connected,
without any reducedness or normality assumption. Indeed, Hartogs extension identifies its
global functions with the original local ring.

Connectedness allows a morphism of finite étale covers to be tested on one geometric fibre.
In particular it supplies the connected-base input when identifying a lifted cover with a
cover on the punctured spectrum from their agreement on a nonempty hypersurface section.

## References

* The Stacks Project, Lemma 31.5.11 (0E9I), extension of sections across depth-two loci.
* The Stacks Project, Lemma 58.20.7 (0BLM), extension from a hypersurface section.
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The punctured spectrum of a Noetherian local ring of depth at least two is connected. -/
theorem connectedSpace_puncturedSpectrum_of_two_le_depth
    (hdepth : 2 ≤ depth (ModuleCat.of A A)) : ConnectedSpace (puncturedSpectrum A).toScheme := by
  let U := puncturedSpectrum A
  have hΓ := TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat
    (A := A) (B := A) hdepth U fun p hp ↦
      (mem_puncturedSpectrum_iff A p).mpr fun h ↦ hp (congrArg PrimeSpectrum.asIdeal h)
  let e := RingEquiv.ofBijective ((Spec (.of A)).presheaf.map U.leTop.op).hom hΓ
  have : IsLocalRing Γ(Spec (.of A), ⊤) :=
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.isLocalRing
  have : IsLocalRing Γ(Spec (.of A), U) := e.isLocalRing
  let eU := (Scheme.restrictFunctorΓ (X := Spec (.of A))).app (Opposite.op U)
  have : IsLocalRing Γ(U.toScheme, ⊤) := eU.symm.commRingCatIsoToRingEquiv.isLocalRing
  exact U.toScheme.connectedSpace_of_isLocalRing

end TauCeti.IsLocalRing
