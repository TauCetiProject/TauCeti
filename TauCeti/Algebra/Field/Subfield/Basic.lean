/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Coercion lemmas for subfield equivalences

This file provides `RingEquiv.coe_subfieldCongr_apply`, showing that coercing
`RingEquiv.subfieldCongr h y` to the ambient division ring equals coercing `y`.
-/

public section

namespace RingEquiv

/-- Coercing `RingEquiv.subfieldCongr h` to the ambient division ring preserves the underlying
element. -/
@[simp]
theorem coe_subfieldCongr_apply {L : Type*} [DivisionRing L] {S T : Subfield L} (h : S = T)
    (y : S) : (subfieldCongr h y : L) = (y : L) := rfl

end RingEquiv
