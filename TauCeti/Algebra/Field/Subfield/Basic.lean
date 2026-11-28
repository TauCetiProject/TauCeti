/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Subfield algebra structures and equality transport

When `k` is an `R`-algebra and `S` is a subfield of `k` containing the image of
`algebraMap R k`, codomain restriction equips `S` with an `R`-algebra structure forming a
scalar tower `R → S → k`.

`RingEquiv.subfieldCongr` identifies two equal subfields. This file also records that it keeps
the underlying element of the ambient field, the subfield analogue of Mathlib's
`RingEquiv.coe_subringCongr_apply`.

## Main definitions

* `Subfield.restrictAlgebra`: the `R`-algebra structure on a subfield `S` containing the image of
  `algebraMap R k`.

## Main results

* `Subfield.isScalarTower_restrictAlgebra`: the scalar tower `IsScalarTower R S k` for
  `S.restrictAlgebra`.
* `RingEquiv.coe_subfieldCongr_apply`: `RingEquiv.subfieldCongr` keeps the underlying element
  of the ambient field.
-/

public section

namespace Subfield

variable {R k : Type*} [CommSemiring R] [Field k] [Algebra R k]

/-- When the structure map `algebraMap R k` takes values in a subfield `S` of `k`, codomain
restriction equips `S` with an `R`-algebra structure. -/
@[instance_reducible]
def restrictAlgebra (S : Subfield k) (hR : ∀ r : R, algebraMap R k r ∈ S) : Algebra R S :=
  RingHom.toAlgebra ((algebraMap R k).codRestrict S hR)

/-- The restricted `R`-algebra structure on a subfield `S` of `k` containing the image of `R`
forms a scalar tower `R → S → k`. -/
theorem isScalarTower_restrictAlgebra (S : Subfield k)
    (hR : ∀ r : R, algebraMap R k r ∈ S) :
    let := S.restrictAlgebra hR
    IsScalarTower R S k := by
  let := S.restrictAlgebra hR
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  rw [Algebra.algebraMap_ofSubsemiring_apply, RingHom.algebraMap_toAlgebra,
    RingHom.codRestrict_apply]

end Subfield

namespace RingEquiv

variable {K : Type*} [DivisionRing K] {s t : Subfield K}

/-- `RingEquiv.subfieldCongr` keeps the underlying element of the ambient field. -/
@[simp]
theorem coe_subfieldCongr_apply (h : s = t) (x : s) : (subfieldCongr h x : K) = x :=
  rfl

end RingEquiv
