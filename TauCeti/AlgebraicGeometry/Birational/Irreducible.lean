/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Irreducibility is a birational invariant

Two birational schemes have isomorphic dense open subschemes. A nonempty open subset of an
irreducible space is irreducible, and a space with a dense irreducible subset is irreducible, so
one of two birational schemes is irreducible exactly when the other is. For instance the source of
a modification of an irreducible scheme is irreducible, and it is integral as soon as it is
reduced.

## Main results

* `AlgebraicGeometry.Scheme.Birational.irreducibleSpace`: a scheme birational to an irreducible
  scheme is irreducible.
* `AlgebraicGeometry.Scheme.Birational.irreducibleSpace_iff`: birational schemes are irreducible
  together.
-/

public section

namespace AlgebraicGeometry.Scheme.Birational

universe u

variable {X Y : Scheme.{u}}

/-- A scheme birational to an irreducible scheme is irreducible: it contains a dense open
subscheme isomorphic to a nonempty open subscheme of the irreducible scheme. -/
theorem irreducibleSpace (h : X.Birational Y) [IrreducibleSpace Y] : IrreducibleSpace X := by
  obtain ⟨e⟩ := h
  have : IrreducibleSpace e.target := Subtype.irreducibleSpace ⟨e.dense_target.nonempty,
    (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset e.target.isOpen
      (Set.subset_univ _)⟩
  have : IrreducibleSpace (e.source : Set X) := e.iso.hom.homeomorph.irreducibleSpace_iff.mpr this
  rw [irreducibleSpace_def, Set.top_eq_univ, ← e.dense_source.closure_eq]
  exact (IsIrreducible.of_subtype (s := (e.source : Set X))).closure

/-- Birational schemes are irreducible together. -/
theorem irreducibleSpace_iff (h : X.Birational Y) : IrreducibleSpace X ↔ IrreducibleSpace Y :=
  ⟨fun _ ↦ h.symm.irreducibleSpace, fun _ ↦ h.irreducibleSpace⟩

end AlgebraicGeometry.Scheme.Birational
