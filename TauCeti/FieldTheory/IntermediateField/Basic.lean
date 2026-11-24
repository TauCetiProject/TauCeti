/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Basic properties of intermediate fields

This file records that the algebra structure map from an intermediate field
`E : IntermediateField K L` into the ambient field `L` coincides with `SubringClass.subtype E`.

## Main results

* `IntermediateField.algebraMap_eq_subtype`: `(algebraMap E L : E →+* L) = SubringClass.subtype E`.
-/

public section

namespace IntermediateField

/-- For an intermediate field `E` of `L / K`, the algebra structure map `algebraMap E L` equals
the canonical inclusion `SubringClass.subtype E`. -/
theorem algebraMap_eq_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) :
    (algebraMap E L : E →+* L) = SubringClass.subtype E := by
  ext x
  exact IntermediateField.algebraMap_apply E x

end IntermediateField
