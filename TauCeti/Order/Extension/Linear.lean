/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Extension.Linear

/-!
# Leaving the linear extension of a partial order

Mathlib's `LinearExtension S` is a copy of a partially ordered type `S` carrying a chosen linear
order which extends the order of `S`, with the monotone identity map `toLinearExtension`. This file
adds the identity map back, `TauCeti.ofLinearExtension`, which need not be monotone, so that an
element of the linear extension can be compared in the original order of `S`, and records that the
linear extension of a finite type is finite.
-/

public section

namespace TauCeti

universe w

section LinearExtension

variable {S : Type w} [PartialOrder S]

/-- The identity map from the linear extension `LinearExtension S` back to `S`, inverse to
`toLinearExtension`. It need not be monotone. -/
def ofLinearExtension : LinearExtension S → S := fun a ↦ a

@[simp]
lemma ofLinearExtension_toLinearExtension (a : S) :
    ofLinearExtension (toLinearExtension a) = a := (rfl)

@[simp]
lemma toLinearExtension_ofLinearExtension (a : LinearExtension S) :
    toLinearExtension (ofLinearExtension a) = a := (rfl)

/-- The linear extension extends the order of `S`. -/
lemma le_of_ofLinearExtension_le {a b : LinearExtension S}
    (h : ofLinearExtension a ≤ ofLinearExtension b) : a ≤ b :=
  (toLinearExtension (α := S)).monotone h

instance [Finite S] : Finite (LinearExtension S) :=
  .of_equiv S ⟨toLinearExtension, ofLinearExtension, ofLinearExtension_toLinearExtension,
    toLinearExtension_ofLinearExtension⟩

end LinearExtension

end TauCeti
