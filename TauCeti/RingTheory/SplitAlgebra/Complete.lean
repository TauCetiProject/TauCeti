/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.RingHom.Pure
public import TauCeti.RingTheory.SplitAlgebra.Basic

import TauCeti.RingTheory.Pure.Complete

/-!
# Pure algebras over complete local rings

Over a complete Noetherian local ring, an algebra with pure structure map has a linear unit
retraction. This converts tensor purity of an absolute integral closure into splitting over
the base, as in the application discussed in André, *La conjecture du facteur direct*,
Annexe A.3.
-/

public section

open IsLocalRing

namespace TauCeti

/-- An algebra over a complete Noetherian local ring splits if and only if its structure map
is pure. -/
theorem splitAlgebra_iff_isPure_of_isAdicComplete
    {R S : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [Algebra R S] :
    SplitAlgebra R S ↔ (algebraMap R S).IsPure := by
  rw [RingHom.isPure_algebraMap_iff]
  constructor
  · intro h
    obtain ⟨ρ, hρ⟩ := h.exists_leftInverse
    exact LinearMap.isPure_of_comp_eq_id (g := ρ) (LinearMap.ext hρ)
  · intro h
    obtain ⟨ρ, hρ⟩ := h.exists_leftInverse_of_isAdicComplete
    exact SplitAlgebra.of_map_one ρ (by simpa using hρ 1)

end TauCeti
