/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import TauCeti.RingTheory.Flat.Pi

/-!
# Faithful flatness of a finite product of ring homomorphisms

A finite family of flat ring homomorphisms `f i : R →+* S i` combines into a faithfully flat ring
homomorphism `RingHom.pi f : R →+* ∀ i, S i` as soon as every maximal ideal of `R` stays proper
under some `f i`.

## Main results

* `RingHom.FaithfullyFlat.pi_of_exists_map_ne_top`: the criterion above.
-/

public section

namespace RingHom.FaithfullyFlat

/-- **A finite product of flat ring homomorphisms is faithfully flat as soon as no maximal ideal
becomes the unit ideal under every factor.** No single `f i` need be faithfully flat: each maximal
ideal `m` of `R` only has to stay proper under *some* `f i`, and which one may depend on `m`. Since
`m` is maximal, `m.map (f i) ≠ ⊤` holds exactly when some prime of `S i` lies over `m`.

This is `Module.FaithfullyFlat.pi_of_exists_submodule_ne_top` for the `R`-algebra structures
induced by the `f i`, with its condition `m • ⊤ ≠ ⊤` rephrased as `m.map (f i) ≠ ⊤`. The finiteness
of `ι` cannot be dropped: an infinite product of flat modules need not be flat. -/
theorem pi_of_exists_map_ne_top {R ι : Type*} [CommRing R] [_root_.Finite ι] {S : ι → Type*}
    [∀ i, CommRing (S i)] {f : ∀ i, R →+* S i} (hf : ∀ i, (f i).Flat)
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ i, m.map (f i) ≠ ⊤) : (RingHom.pi f).FaithfullyFlat := by
  let _ : ∀ i, Algebra R (S i) := fun i ↦ (f i).toAlgebra
  have _ : ∀ i, Module.Flat R (S i) := hf
  -- `RingHom.FaithfullyFlat` of `RingHom.pi` unfolds to `Module.FaithfullyFlat` of the product
  change Module.FaithfullyFlat R (∀ i, S i)
  refine Module.FaithfullyFlat.pi_of_exists_submodule_ne_top fun m hm ↦ (h m hm).imp fun i hi ↦ ?_
  rwa [Ideal.smul_top_eq_map, Ne, Submodule.restrictScalars_eq_top_iff]

end RingHom.FaithfullyFlat

end
