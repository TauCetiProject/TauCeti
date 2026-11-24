/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Induced maps between residue fields of local rings

This file provides typeclass infrastructure for maps between residue fields induced by ring
isomorphisms of local rings, allowing semilinear maps and equivalences to be stated directly over
`IsLocalRing.ResidueField.mapEquiv`.

## Main declarations

* `IsLocalRing.ResidueField.ringHomInvPair_mapEquiv`: `ResidueField.mapEquiv σ` and
  `ResidueField.mapEquiv σ.symm` form an inverse pair of ring homomorphisms.
-/

public section

namespace IsLocalRing

/-- `ResidueField.mapEquiv σ` and `ResidueField.mapEquiv σ.symm` form an inverse pair of ring
homomorphisms, allowing semilinear equivalences over `ResidueField.mapEquiv σ`. -/
instance ResidueField.ringHomInvPair_mapEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (σ : R ≃+* S) :
    RingHomInvPair (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)
      (ResidueField.mapEquiv σ.symm : ResidueField S →+* ResidueField R) := by
  simpa only [ResidueField.mapEquiv.symm] using
    RingHomInvPair.of_ringEquiv (ResidueField.mapEquiv σ)

end IsLocalRing
