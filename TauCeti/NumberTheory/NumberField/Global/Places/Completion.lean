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

`TauCeti.GlobalNumberFields.Place.Completion` selects Mathlib's completion of a number field `K`
at a place: the adic completion `v.adicCompletion K` at a finite place `v`, and the archimedean
completion `w.Completion` at an infinite place `w`. Families of local conditions ranging over all
places of `K`, such as those cutting out the Shafarevich–Tate group of an elliptic curve, are
indexed by `Place K` with these fields.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II.
-/

public section

namespace TauCeti.GlobalNumberFields.Place

open IsDedekindDomain NumberField
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The completion of `K` at a finite or infinite place, using the existing completion in each
case. -/
abbrev Completion : Place K → Type _
  | .inl v => v.adicCompletion K
  | .inr w => w.Completion

noncomputable instance (v : Place K) : Field v.Completion := by
  cases v <;> exact inferInstance

noncomputable instance (v : Place K) : Algebra K v.Completion := by
  cases v <;> exact inferInstance

end TauCeti.GlobalNumberFields.Place

end
