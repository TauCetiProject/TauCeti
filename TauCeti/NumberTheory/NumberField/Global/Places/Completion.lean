/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Places.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Completions indexed by all places

`Place.Completion` selects Mathlib's adic or archimedean completion according to the place.
It allows local conditions to range over all places in one family of field extensions, without
replacing either of the existing completion constructions.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II.
-/

public section

namespace TauCeti.GlobalNumberFields.Place

open IsDedekindDomain NumberField
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The completion at a finite or infinite place, using the existing completion in each case. -/
abbrev Completion : Place K → Type _
  | .inl v => v.adicCompletion K
  | .inr w => w.Completion

noncomputable instance (v : Place K) : Field v.Completion := by
  cases v <;> exact inferInstance

noncomputable instance (v : Place K) : Algebra K v.Completion := by
  cases v <;> exact inferInstance

end TauCeti.GlobalNumberFields.Place

end
