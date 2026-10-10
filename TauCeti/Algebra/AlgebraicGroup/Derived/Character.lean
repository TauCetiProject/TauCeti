/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Characters are trivial on the derived subgroup

Every character of an affine group restricts to the trivial character on its derived closed
subgroup. In coordinates, a group-like element minus one belongs to the derived defining ideal.
This supplies the diagonal equations when restricting a triangular representation to the
derived subgroup.

The proof uses the canonical evaluation morphism from the group algebra of the characters and
functoriality of the derived subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

namespace GroupLike

open TauCeti

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- Every character restricts to one on the derived closed subgroup. -/
@[simp]
theorem sub_one_mem_derivedDefiningIdeal (x : GroupLike R H) :
    (x : H) - 1 ∈ CommHopfAlgCat.derivedDefiningIdeal (R := R) H := by
  let f := TauCeti.GroupLike.evaluationBialgHom R H
  have hmem : MonoidAlgebra.single x (1 : R) - 1 ∈
      CommHopfAlgCat.derivedDefiningIdeal (R := R) (MonoidAlgebra R (GroupLike R H)) := by
    rw [(CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_iff_isCocomm _).mpr inferInstance,
      HopfIdeal.mem_augmentation]
    simp
  have h := CommHopfAlgCat.derivedDefiningIdeal_map_le f
    (HopfIdeal.mem_map_of_mem f hmem)
  simpa [f] using h

end GroupLike
