/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.DiagonalizableCoaction
public import TauCeti.Algebra.MonoidAlgebra.Face.Localization

/-!
# Diagonalizable-group coaction equivariance of face maps

For an additive submonoid `S` of an abelian group `G` and a face `F : SaturatedAddSubmonoid S`,
face restriction (`AddMonoidAlgebra.map_faceRestriction_comp_gradedCoaction`) and `F.orbitMap R`
(`AddSubmonoid.map_orbitMap_comp_diagonalizableCoaction`) are equivariant with respect to the
diagonalizable-group coaction.

## Main declarations

* `AddMonoidAlgebra.map_faceRestriction_comp_gradedCoaction`: face restriction commutes with
  `gradedCoaction`.
* `AddSubmonoid.map_orbitMap_comp_diagonalizableCoaction`: `F.orbitMap R` commutes with
  `S.diagonalizableCoaction R`.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

namespace AddMonoidAlgebra

/-- Restriction to a face `F` is equivariant with respect to `gradedCoaction`. -/
theorem map_faceRestriction_comp_gradedCoaction (R : Type*) [CommSemiring R] {M L : Type*}
    [AddCommMonoid M] [AddMonoid L] (w : M →+ L) (F : SaturatedAddSubmonoid M) :
    (Algebra.TensorProduct.map (AlgHom.id R (AddMonoidAlgebra R L))
      (F.toAddSubmonoid.faceRestriction F.addSaturated R)).comp (gradedCoaction R w) =
      (gradedCoaction R (w.comp F.toAddSubmonoid.subtype)).comp
        (F.toAddSubmonoid.faceRestriction F.addSaturated R) := by
  ext m; by_cases hm : m ∈ F
  · simp [F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hm]
  · simp [F.toAddSubmonoid.faceRestriction_single_of_notMem F.addSaturated hm]

end AddMonoidAlgebra

namespace AddSubmonoid

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G) (R : Type*) [CommSemiring R]

/-- For any face `F` of `S`, `F.orbitMap R` is equivariant for the diagonalizable-group coaction
of `R[AddSubgroup.closure S]`. -/
theorem map_orbitMap_comp_diagonalizableCoaction (F : SaturatedAddSubmonoid S) :
    (Algebra.TensorProduct.map (AlgHom.id R _) (F.orbitMap R)).comp (S.diagonalizableCoaction R) =
      (gradedCoaction R F.faceSubgroup.subtype).comp (F.orbitMap R) := by
  have h1 := map_faceRestriction_comp_gradedCoaction R S.toGroupClosure F
  have h2 := map_mapDomain_comp_gradedCoaction R (g := AddMonoidHom.id _) (f := F.toFaceSubgroup)
    (w₁ := S.toGroupClosure.comp F.toAddSubmonoid.subtype) (w₂ := F.faceSubgroup.subtype)
    F.subtype_comp_toFaceSubgroup
  rw [mapDomainAlgHom_id] at h2
  rw [F.orbitMap_def R, S.diagonalizableCoaction_def R, ← AlgHom.comp_id (AlgHom.id R _),
    Algebra.TensorProduct.map_comp, AlgHom.comp_assoc, h1, ← AlgHom.comp_assoc, h2,
    AlgHom.comp_assoc]

end AddSubmonoid
