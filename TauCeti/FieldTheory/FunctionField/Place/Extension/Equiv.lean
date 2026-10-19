/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Ramification under field isomorphisms

The ramification index depends on the extension, not on its presentation as a field carrier:
transporting a place of the upstairs field along an isomorphism over the downstairs field does not
change its ramification index. This allows an extension to be placed in a finite Galois overfield
without changing its ramification behaviour.
-/

public section

namespace TauCeti.Place

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']

/-- **The ramification index is invariant under an isomorphism of the upstairs field** over the
base field: transporting a place of `L` along `e : L ≃ₐ[F] L'` does not change its ramification
index over `F`. -/
@[simp]
theorem ramificationIdx_equivOfRingEquiv (e : L ≃ₐ[F] L') (Q : Place k L) :
    ramificationIdx F (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
      (fun c ↦ by simp [IsScalarTower.algebraMap_apply k F L,
        IsScalarTower.algebraMap_apply k F L']) Q) = ramificationIdx F Q := by
  rw [ramificationIdx_def, ramificationIdx_def]
  congr 1
  ext c
  rw [Valuation.comap_apply, Valuation.comap_apply, valuation_equivOfRingEquiv]
  exact congrArg Q.valuation (e.symm.commutes c)

end TauCeti.Place
