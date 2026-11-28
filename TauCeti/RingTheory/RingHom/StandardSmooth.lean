/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Standard smooth ring homomorphisms

This file complements `Mathlib.RingTheory.RingHom.StandardSmooth` with the extraction of the
relative dimension from a standard smooth ring homomorphism:

* `RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension`: every standard smooth
  ring homomorphism is standard smooth of some natural-number relative dimension.
-/

public section

namespace RingHom

/-- A standard smooth ring homomorphism is standard smooth of some relative dimension. -/
theorem IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension
    {R S : Type*} [CommRing R] [CommRing S] {g : R →+* S} (hg : g.IsStandardSmooth) :
    ∃ m : ℕ, g.IsStandardSmoothOfRelativeDimension m := by
  let := g.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hg
  exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩

end RingHom
