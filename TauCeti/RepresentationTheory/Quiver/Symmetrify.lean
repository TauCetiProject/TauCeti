/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Fintype.Sum

/-!
# Symmetrified quivers

This file supplies general infrastructure for Mathlib's `Quiver.Symmetrify` construction.

## References

This file supplies a prerequisite for Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `Finite Q`. -/
instance instFiniteSymmetrify (Q : Type u) [Finite Q] : Finite (Symmetrify Q) :=
  inferInstanceAs (Finite Q)

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `DecidableEq Q`. -/
instance instDecidableEqSymmetrify (Q : Type u) [DecidableEq Q] : DecidableEq (Symmetrify Q) :=
  inferInstanceAs (DecidableEq Q)

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `Fintype Q`. -/
instance instFintypeSymmetrify (Q : Type u) [Fintype Q] : Fintype (Symmetrify Q) :=
  inferInstanceAs (Fintype Q)

/-- The arrows of the doubled quiver between two vertices are the arrows of `Q` in either
direction, so there are finitely many whenever `Q` has finitely many between each pair. -/
instance instFintypeSymmetrifyHom (Q : Type u) [Quiver.{v} Q] [∀ i j : Q, Fintype (i ⟶ j)]
    (x y : Symmetrify Q) : Fintype (x ⟶ y) :=
  inferInstanceAs (Fintype (((show Q from x) ⟶ (show Q from y)) ⊕
    ((show Q from y) ⟶ (show Q from x))))

end TauCeti
