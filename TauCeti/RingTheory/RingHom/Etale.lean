/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Etale

/-!
# Composition of étale ring homomorphisms

Composition preserves étaleness also when the three rings live in different universes.
This is the ring-homomorphism form of `Algebra.Etale.comp`.
-/

public section

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The composite of two étale ring homomorphisms is étale. -/
theorem Etale.comp {f : R →+* S} {g : S →+* T} (hg : g.Etale) (hf : f.Etale) :
    (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp R S T

end RingHom
