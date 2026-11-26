/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Equality transport between subfields

`RingEquiv.subfieldCongr` identifies two equal subfields. This file records that it keeps the
underlying element of the ambient field, the subfield analogue of Mathlib's
`RingEquiv.coe_subringCongr_apply`.
-/

public section

namespace RingEquiv

variable {K : Type*} [DivisionRing K] {s t : Subfield K}

/-- `RingEquiv.subfieldCongr` keeps the underlying element of the ambient field. -/
@[simp]
theorem coe_subfieldCongr_apply (h : s = t) (x : s) : (subfieldCongr h x : K) = x :=
  rfl

end RingEquiv
