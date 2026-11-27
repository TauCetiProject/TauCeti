/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.BooleanRing
public import TauCeti.RingTheory.VonNeumannRegular.Basic

/-!
# Von Neumann regularity of Boolean rings

Every element of a Boolean ring is its own square, so the multiplicative identity is an
inner inverse for every element.
-/

public section

namespace TauCeti.IsVonNeumannRegularSemigroup

variable {R : Type*}

/-- A Boolean ring is von Neumann regular. -/
instance [BooleanRing R] : IsVonNeumannRegularSemigroup R :=
  ⟨fun a ↦ ⟨1, by simp [BooleanRing.mul_self]⟩⟩

end TauCeti.IsVonNeumannRegularSemigroup
