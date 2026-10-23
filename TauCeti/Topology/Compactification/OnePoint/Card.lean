/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `OnePoint` occurs in the statement below.
public import Mathlib.Topology.Compactification.OnePoint.Basic
-- `Finite.card_option` is the underlying count.
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The number of points of a one-point compactification

The one-point compactification of a finite space has one more point than the space itself. The
count is Mathlib's `Finite.card_option` read through the definition `OnePoint X = Option X`, in the
same style as the other restatements of `Option` lemmas for `OnePoint` in
`Mathlib/Topology/Compactification/OnePoint/Basic.lean`.
-/

public section

namespace TauCeti

/-- **The one-point compactification of a finite space has one more point.** -/
@[simp]
theorem natCard_onePoint (X : Type*) [Finite X] : Nat.card (OnePoint X) = Nat.card X + 1 :=
  Finite.card_option

end TauCeti
