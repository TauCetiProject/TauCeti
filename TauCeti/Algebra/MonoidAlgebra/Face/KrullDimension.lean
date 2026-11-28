/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.Algebra.Group.Submonoid.Saturation
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.MonoidAlgebra.KrullDimension

/-!
# Krull dimensions of face algebras and orbit coordinate algebras

Over a field `k` and a torsion-free abelian group `G` (`[HasUniqueDiv G]`), every finitely
generated face `F` of `S : AddSubmonoid G` satisfies
`ringKrullDim k[F] = ringKrullDim k[F.faceSubgroup] = Module.finrank ℤ F.faceSubgroup`.

## Main declarations

* `SaturatedAddSubmonoid.ringKrullDim_addMonoidAlgebra_faceSubgroup`
* `SaturatedAddSubmonoid.ringKrullDim_addMonoidAlgebra`
-/

public section

open AddMonoidAlgebra

namespace SaturatedAddSubmonoid

variable {G : Type*} [AddCommGroup G] [HasUniqueDiv G] {S : AddSubmonoid G}
  (F : SaturatedAddSubmonoid S)

private theorem hasUniqueDiv_faceSubgroup : HasUniqueDiv F.faceSubgroup :=
  Function.Injective.hasUniqueDiv
    ((AddSubgroup.closure (S : Set G)).subtype.comp F.faceSubgroup.subtype)
    ((AddSubgroup.closure (S : Set G)).subtype_injective.comp F.faceSubgroup.subtype_injective)

/-- Over a field `k`, for a finitely generated face `F` of a submonoid `S` of a torsion-free
abelian group `G`, the localized orbit coordinate algebra `k[F.faceSubgroup]` has Krull dimension
`Module.finrank ℤ F.faceSubgroup`. -/
theorem ringKrullDim_addMonoidAlgebra_faceSubgroup (hF : F.toAddSubmonoid.FG)
    (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k F.faceSubgroup) = Module.finrank ℤ F.faceSubgroup :=
  have := F.moduleFinite_faceSubgroup hF
  have := F.hasUniqueDiv_faceSubgroup
  AddMonoidAlgebra.ringKrullDim_of_free k F.faceSubgroup

/-- Over a field `k`, for a finitely generated face `F` of a submonoid `S` of a torsion-free
abelian group `G`, the closed face algebra `k[F]` has Krull dimension
`Module.finrank ℤ F.faceSubgroup`. -/
theorem ringKrullDim_addMonoidAlgebra (hF : F.toAddSubmonoid.FG) (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k F) = Module.finrank ℤ F.faceSubgroup :=
  have : AddMonoid.FG F := (AddMonoid.fg_iff_addSubmonoid_fg F.toAddSubmonoid).2 hF
  have := F.hasUniqueDiv_faceSubgroup
  AddMonoidAlgebra.ringKrullDim_of_exists_add_eq F.toFaceSubgroup_injective
    F.exists_add_toFaceSubgroup_eq k

end SaturatedAddSubmonoid
