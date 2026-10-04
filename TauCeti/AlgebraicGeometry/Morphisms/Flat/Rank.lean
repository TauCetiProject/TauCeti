/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Rank transport over a fixed base

The rank function of a finite flat morphism is invariant under isomorphisms over its base.
This packages Mathlib's `Scheme.Hom.finrank_comp_left_of_isIso` for objects of `Over S`.
`TauCeti.finrank_eq_of_nonempty_iso_over` requires only the existence of an isomorphism over the
base, incorporating its commuting triangle. It compares an affine group scheme with the Hopf
spectrum of its coordinate algebra, and also transports rank through isomorphisms with Cartier
duals.

For `e : X ≅ Y` in `Over S`, use `TauCeti.finrank_eq_of_nonempty_iso_over ⟨e⟩` to obtain
`X.hom.finrank = Y.hom.finrank` when `Y.hom` is finite and flat.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

/-- Isomorphic schemes over a fixed base have the same rank function when the target
structural morphism is finite and flat. -/
theorem finrank_eq_of_nonempty_iso_over {S : Scheme.{u}} {X Y : Over S}
    (h : Nonempty (X ≅ Y))
    [Flat Y.hom] [IsFinite Y.hom] : X.hom.finrank = Y.hom.finrank := by
  obtain ⟨e⟩ := h
  rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]

end TauCeti
