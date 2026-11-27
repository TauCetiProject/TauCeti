/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Topology
import TauCeti.Topology.Algebra.PointTopology.HopfIdeal

/-!
# The point topology of a closed subgroup scheme of `GL_n`

Let `I` be a Hopf ideal of the coordinate Hopf algebra of `GL_n` over `k`, cutting out a closed
subgroup scheme. Over a T1 topological ring `R`, its points
`TauCeti.GeneralLinear.hopfIdealPointsSubgroup n I R` form a closed subgroup of
`GL (Fin n) R`: the homeomorphism `TauCeti.GeneralLinear.pointsContinuousMulEquiv` carries them
onto the points vanishing on `I`, which are closed in the point topology
(`TauCeti.PointTopology.isClosed_quotientPointsSubgroup`).

The identification of the points of the quotient coordinate ring with this matrix subgroup is a
homeomorphism for the subspace topology.

## Main declarations

* `TauCeti.GeneralLinear.isHomeomorph_hopfIdealPointsSubgroupMulEquiv`: the intrinsic point
  topology agrees with that induced from the matrix group.
* `TauCeti.GeneralLinear.isClosed_hopfIdealPointsSubgroup`: over a T1 topological ring, the
  points of a closed subgroup scheme of `GL_n` form a closed subgroup of `GL (Fin n) R`.
-/

public section

namespace TauCeti.GeneralLinear

variable {k : Type*} [CommRing k] (n : ℕ) {R : Type*} [CommRing R] [Algebra k R]
  [TopologicalSpace R] [IsTopologicalRing R]

open Topology PointTopology in
/-- Evaluating a point of a quotient of the coordinate Hopf algebra of `GLₙ` gives a
homeomorphism onto the corresponding matrix subgroup, with its subspace topology. -/
theorem isHomeomorph_hopfIdealPointsSubgroupMulEquiv
    (I : HopfIdeal k (coordinateHopfAlgebra k n)) :
    IsHomeomorph (hopfIdealPointsSubgroupMulEquiv n I (CommAlgCat.of k R)) := by
  let H := coordinateHopfAlgebra k n
  refine isHomeomorph_iff_isEmbedding_surjective.2 ⟨?_, MulEquiv.surjective _⟩
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  have heq : Subtype.val ∘ hopfIdealPointsSubgroupMulEquiv n I (CommAlgCat.of k R) =
      pointsContinuousMulEquiv n ∘ CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k R) := by
    funext x
    simpa only [Function.comp_apply, pointsContinuousMulEquiv_apply] using
      coe_hopfIdealPointsSubgroupMulEquiv_apply n I (CommAlgCat.of k R) x
  rw [heq]
  exact (pointsContinuousMulEquiv (k := k) n).isEmbedding.comp (isEmbedding_quotientPointsHom R H I)

/-- **The points of a closed subgroup scheme of `GL_n` form a closed subgroup.** Over a T1
topological ring `R`, the invertible matrices cut out by a Hopf ideal `I` of the coordinate Hopf
algebra are a closed subset of `GL (Fin n) R`: they are the image under the homeomorphism
`pointsContinuousMulEquiv` of the points vanishing on `I`, an intersection of zero sets of
continuous evaluations. -/
theorem isClosed_hopfIdealPointsSubgroup [T1Space R] (I : HopfIdeal k (coordinateHopfAlgebra k n)) :
    IsClosed (hopfIdealPointsSubgroup n I R : Set (Matrix.GeneralLinearGroup (Fin n) R)) := by
  -- The definition of `hopfIdealPointsSubgroup` is not exposed outside its module, so the
  -- subgroup is identified with the preimage through its membership lemma.
  have h : (hopfIdealPointsSubgroup n I R : Set (Matrix.GeneralLinearGroup (Fin n) R)) =
      (pointsContinuousMulEquiv (k := k) n).symm ⁻¹'
        (CommHopfAlgCat.quotientPointsSubgroup _ I (CommAlgCat.of k R)) := by
    ext g
    rw [Set.mem_preimage, pointsContinuousMulEquiv_symm_apply, SetLike.mem_coe, SetLike.mem_coe,
      mem_hopfIdealPointsSubgroup_iff, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  rw [h]
  exact (PointTopology.isClosed_quotientPointsSubgroup R _ I).preimage
    (pointsContinuousMulEquiv (k := k) n).symm.continuous

end TauCeti.GeneralLinear
