/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitivity of a permutation triple

The monodromy action is primitive when it is preprimitive in Mathlib's sense.
-/

public section

namespace TauCeti

namespace PermutationTriple

open MulAction

variable {n : ℕ} (t : PermutationTriple n)

/-- The monodromy action of a permutation triple is primitive in the roadmap's convention. -/
def IsPrimitive : Prop := IsPreprimitive t.monodromyGroup (Fin n)

/-- Primitivity of a triple is preprimitivity of its monodromy action. -/
theorem isPrimitive_iff : t.IsPrimitive ↔ IsPreprimitive t.monodromyGroup (Fin n) := Iff.rfl

end PermutationTriple

end TauCeti
