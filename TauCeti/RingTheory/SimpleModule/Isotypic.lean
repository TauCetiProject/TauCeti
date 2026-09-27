/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# A semisimple module is the direct sum of its isotypic components

Mathlib shows that the isotypic components of a module are independent
(`sSupIndep_isotypicComponents`) and, for a semisimple module, span it
(`sSup_isotypicComponents`); it reads off the consequence for endomorphisms
(`IsSemisimpleModule.endAlgEquiv`). This file records the consequence for the module itself: a
semisimple module is the internal direct sum of its isotypic components. When there are finitely
many components, for instance when the module is Noetherian, composing with
`DFinsupp.linearEquivFunOnFintype` presents it as their product.

## Main definitions

* `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents`: a semisimple module is linearly
  equivalent to the direct sum of its isotypic components.

## Main statements

* `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents_apply_coe` and
  `TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents_symm_single`: the equivalence and its
  inverse on a single isotypic component.
-/

public section

namespace TauCeti.IsSemisimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  [DecidableEq (isotypicComponents R M)]

/-- **A semisimple module is the direct sum of its isotypic components.** The equivalence sends
an element to its family of components, and its inverse adds the components up. This is the
module-level counterpart of `IsSemisimpleModule.endAlgEquiv`. -/
noncomputable def linearEquivIsotypicComponents : M ≃ₗ[R] Π₀ c : isotypicComponents R M, c.1 :=
  .symm <| ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).linearEquiv <|
    (sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M

variable {R M}

/-- The inverse of `linearEquivIsotypicComponents` sends the family that is `x` at the isotypic
component `c` and zero elsewhere to `x`, viewed as an element of `M`. -/
@[simp]
theorem linearEquivIsotypicComponents_symm_single (c : isotypicComponents R M) (x : c.1) :
    (linearEquivIsotypicComponents R M).symm (DFinsupp.single c x) = x := by
  simp [linearEquivIsotypicComponents]

/-- `linearEquivIsotypicComponents` sends an element `x` of an isotypic component `c`, viewed as an
element of `M`, to the family that is `x` at `c` and zero elsewhere. -/
@[simp]
theorem linearEquivIsotypicComponents_apply_coe {c : isotypicComponents R M} (x : c.1) :
    linearEquivIsotypicComponents R M x = DFinsupp.single c x := by
  rw [← linearEquivIsotypicComponents_symm_single, LinearEquiv.apply_symm_apply]

-- Not `@[simp]`: the component `c` does not occur in the left-hand side, so `simp` could only
-- find it by solving `x ∈ c.1` for `c`. The simp form is
-- `linearEquivIsotypicComponents_apply_coe`, as with `DirectSum.decompose_coe` and
-- `DirectSum.decompose_of_mem`.
/-- An element `x` of `M` lying in an isotypic component `c` is sent by
`linearEquivIsotypicComponents` to the family that is `x` at `c` and zero elsewhere. -/
theorem linearEquivIsotypicComponents_apply_of_mem {c : isotypicComponents R M} {x : M}
    (hx : x ∈ c.1) : linearEquivIsotypicComponents R M x = DFinsupp.single c ⟨x, hx⟩ :=
  linearEquivIsotypicComponents_apply_coe ⟨x, hx⟩

end TauCeti.IsSemisimpleModule
