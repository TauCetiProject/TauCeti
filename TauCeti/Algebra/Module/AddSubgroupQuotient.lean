/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.Hom
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Scalars on a quotient of scalar-stable additive subgroups

For additive subgroups `B` and `Z` of an `R`-module `A` that are stable under the scalars, the
quotient `Z ⧸ B.addSubgroupOf Z` is an `R`-module, the scalar `r` acting on the class of `z` as
the class of `r • z`. The subgroups are additive subgroups, not submodules, because that is how
they arise for instance as the cocycles and coboundaries of continuous group cohomology, whose
definition involves no coefficient ring; the module structure is therefore not an instance, and a
consumer supplies the stability proofs.

## Main definitions

* `AddSubgroup.quotientSMulHom`: multiplication by a scalar on `Z ⧸ B.addSubgroupOf Z`.
* `AddSubgroup.quotientSMulRingHom`: the scalar action as a ring homomorphism into the
  additive endomorphisms.
* `AddSubgroup.quotientModule`: the resulting `R`-module structure.

## Main results

* `AddSubgroup.quotientSMulHom_mk`, `AddSubgroup.quotientModule_smul_mk`: a scalar acts on the
  class of an element as on the element.
-/

public section

namespace AddSubgroup

variable {R : Type*} [Semiring R] {A : Type*} [AddCommGroup A] [Module R A]
  (Z B : AddSubgroup A) (hZ : ∀ (r : R), ∀ a ∈ Z, r • a ∈ Z)
  (hB : ∀ (r : R), ∀ a ∈ B, r • a ∈ B)

/-- Multiplication by a scalar `r` on `Z ⧸ B.addSubgroupOf Z`, for additive subgroups `Z` and `B`
of an `R`-module that are stable under the scalars: the map induced by `r • ·` on `Z`. -/
def quotientSMulHom (r : R) : AddMonoid.End (Z ⧸ B.addSubgroupOf Z) :=
  QuotientAddGroup.map _ _
    (((DistribSMul.toAddMonoidHom A r).comp Z.subtype).codRestrict Z fun z ↦ hZ r z z.property)
    fun z hz ↦ hB r z hz

/-- `quotientSMulHom` acts on the class of an element as the scalar on that element. -/
@[simp]
theorem quotientSMulHom_mk (r : R) (z : Z) :
    quotientSMulHom Z B hZ hB r (z : Z ⧸ B.addSubgroupOf Z) =
      ((⟨r • (z : A), hZ r z z.property⟩ : Z) : Z ⧸ B.addSubgroupOf Z) :=
  (rfl)

/-- The scalar action on `Z ⧸ B.addSubgroupOf Z` as a ring homomorphism into the additive
endomorphisms. -/
def quotientSMulRingHom : R →+* AddMonoid.End (Z ⧸ B.addSubgroupOf Z) where
  toFun := quotientSMulHom Z B hZ hB
  map_one' := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun z ↦ ?_)
    exact congrArg (QuotientAddGroup.mk' _) (Subtype.ext (one_smul R (z : A)))
  map_mul' r s := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun z ↦ ?_)
    exact congrArg (QuotientAddGroup.mk' _) (Subtype.ext (mul_smul r s (z : A)))
  map_zero' := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun z ↦ ?_)
    exact congrArg (QuotientAddGroup.mk' _) (Subtype.ext (zero_smul R (z : A)))
  map_add' r s := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun z ↦ ?_)
    exact congrArg (QuotientAddGroup.mk' _) (Subtype.ext (add_smul r s (z : A)))

/-- The `R`-module structure on `Z ⧸ B.addSubgroupOf Z` for scalar-stable additive subgroups `Z`
and `B` of an `R`-module, with `r • [z] = [r • z]`. Not an instance: the stability proofs are
supplied by the consumer. -/
abbrev quotientModule : Module R (Z ⧸ B.addSubgroupOf Z) :=
  Module.compHom _ (quotientSMulRingHom Z B hZ hB)

/-- For `quotientModule`, a scalar acts on the class of an element as on that element. -/
theorem quotientModule_smul_mk (r : R) (z : Z) :
    letI := quotientModule Z B hZ hB
    r • (z : Z ⧸ B.addSubgroupOf Z) =
      ((⟨r • (z : A), hZ r z z.property⟩ : Z) : Z ⧸ B.addSubgroupOf Z) :=
  (rfl)

end AddSubgroup
