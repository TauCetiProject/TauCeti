/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Induced maps between residue fields of local rings

This file provides typeclass infrastructure for maps and equivalences between residue fields
induced by local ring homomorphisms and ring isomorphisms of local rings, allowing semilinear
maps and equivalences (including their identity, composition, and inverse laws) to be stated
directly over `IsLocalRing.ResidueField.map` and `IsLocalRing.ResidueField.mapEquiv`.

## Main declarations

* `IsLocalRing.ResidueField.ringHomId_map`, `IsLocalRing.ResidueField.ringHomId_mapEquiv`,
  `IsLocalRing.ResidueField.ringHomId_mapEquiv_symm`: identity instances for residue-field maps.
* `IsLocalRing.ResidueField.ringHomInvPair_mapEquiv`,
  `IsLocalRing.ResidueField.ringHomInvPair_mapEquiv_symm`: inverse-pair instances for
  `ResidueField.mapEquiv σ` and `ResidueField.mapEquiv σ.symm`.
* `IsLocalRing.ResidueField.ringHomCompTriple_map`,
  `IsLocalRing.ResidueField.ringHomCompTriple_mapEquiv`: low-priority composition-triple instances
  for induced residue-field maps and equivalences.
-/

public section

namespace IsLocalRing

section ResidueField

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]

/-- `ResidueField.map (RingHom.id R)` is propositionally the identity ring homomorphism. -/
instance ResidueField.ringHomId_map :
    RingHomId (ResidueField.map (RingHom.id R)) where
  eq_id := ResidueField.map_id

/-- `ResidueField.mapEquiv (RingEquiv.refl R)` is propositionally the identity ring homomorphism. -/
instance ResidueField.ringHomId_mapEquiv :
    RingHomId (ResidueField.mapEquiv (RingEquiv.refl R) : ResidueField R →+* ResidueField R) where
  eq_id := RingHom.ext fun x ↦ by simp

/-- `ResidueField.mapEquiv (RingEquiv.refl R).symm` is propositionally the identity ring
homomorphism. -/
instance ResidueField.ringHomId_mapEquiv_symm :
    RingHomId (ResidueField.mapEquiv (RingEquiv.refl R).symm :
      ResidueField R →+* ResidueField R) where
  eq_id := RingHom.ext fun x ↦ by simp

/-- `ResidueField.mapEquiv σ` and `ResidueField.mapEquiv σ.symm` form an inverse pair of ring
homomorphisms, allowing semilinear equivalences over `ResidueField.mapEquiv σ`. -/
instance ResidueField.ringHomInvPair_mapEquiv (σ : R ≃+* S) :
    RingHomInvPair (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)
      (ResidueField.mapEquiv σ.symm : ResidueField S →+* ResidueField R) := by
  simpa only [ResidueField.mapEquiv.symm] using
    RingHomInvPair.of_ringEquiv (ResidueField.mapEquiv σ)

/-- The reverse inverse pair for `ResidueField.mapEquiv σ.symm`, avoiding double-inverse
simplification mismatches against `ResidueField.mapEquiv σ`. -/
instance (priority := high) ResidueField.ringHomInvPair_mapEquiv_symm (σ : R ≃+* S) :
    RingHomInvPair (ResidueField.mapEquiv σ.symm : ResidueField S →+* ResidueField R)
      (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S) :=
  RingHomInvPair.symm (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)
    (ResidueField.mapEquiv σ.symm : ResidueField S →+* ResidueField R)

/-- Induced maps on residue fields compose functorially. -/
instance (priority := low) ResidueField.ringHomCompTriple_map
    (f : R →+* S) (g : S →+* T) [IsLocalHom f] [IsLocalHom g] :
    RingHomCompTriple (ResidueField.map f) (ResidueField.map g) (ResidueField.map (g.comp f)) where
  comp_eq := (ResidueField.map_comp f g).symm

/-- Induced equivalences on residue fields compose functorially. -/
instance (priority := low) ResidueField.ringHomCompTriple_mapEquiv
    (σ : R ≃+* S) (τ : S ≃+* T) :
    RingHomCompTriple (ResidueField.mapEquiv σ : ResidueField R →+* ResidueField S)
      (ResidueField.mapEquiv τ : ResidueField S →+* ResidueField T)
      (ResidueField.mapEquiv (σ.trans τ) : ResidueField R →+* ResidueField T) where
  comp_eq := by
    change ((ResidueField.mapEquiv σ).trans (ResidueField.mapEquiv τ) :
      ResidueField R →+* ResidueField T) = _
    rw [← ResidueField.mapEquiv_trans]

end ResidueField

end IsLocalRing
