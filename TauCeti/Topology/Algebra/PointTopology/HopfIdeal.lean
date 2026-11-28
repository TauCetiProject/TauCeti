/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic
import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Closed subgroups cut out by Hopf ideals in the point topology

Let `H` be a commutative Hopf algebra over `R` and `I` a Hopf ideal of `H`, cutting out the closed
subgroup scheme `Spec (H ⧸ I)` of `Spec H`. Over a topological `R`-algebra `A` whose points are
closed, its `A`-points `TauCeti.CommHopfAlgCat.quotientPointsSubgroup H I A`, the points vanishing
on `I`, form a closed subgroup of `G(A)` for the point topology: they are the intersection of the
zero sets of the continuous evaluations at the elements of `I`.

## Main declarations

* `TauCeti.PointTopology.isEmbedding_quotientPointsHom`: the point topology on a quotient
  coordinate algebra agrees with the subspace topology on its image.
* `TauCeti.PointTopology.isClosed_quotientPointsSubgroup`.
-/

public section

open WithConv TauCeti.CommHopfAlgCat

universe u

namespace TauCeti.PointTopology

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [TopologicalSpace A]

open Topology in
/-- The points of the quotient coordinate algebra embed in the ambient point group for the
evaluation topology, for any topology on the coefficient ring. -/
theorem isEmbedding_quotientPointsHom (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    IsEmbedding (quotientPointsHom H I (CommAlgCat.of R A)) := by
  let q := CommHopfAlgCat.mkQuotient H I
  have heq : ⇑(quotientPointsHom H I (CommAlgCat.of R A)) = BialgHom.mapDomain (A := A) q.hom := by
    funext x
    rw [quotientPointsHom_apply, BialgHom.mapDomain_apply]
  rw [heq]
  exact q.hom.isEmbedding_mapDomain_of_surjective (CommHopfAlgCat.mkQuotient_surjective H I)

variable [T1Space A]

/-- Over a T1 topological algebra `A`, the `A`-points of the closed subgroup scheme cut out by a
Hopf ideal `I` form a closed subgroup of the `A`-points of `Spec H`. -/
theorem isClosed_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    IsClosed (quotientPointsSubgroup H I (CommAlgCat.of R A) : Set (WithConv (H →ₐ[R] A))) := by
  convert isClosed_biInter (fun h (_ : h ∈ I) ↦
    (isClosed_singleton (x := (0 : A))).preimage (continuous_eval_ofConv (k := R) (R := A) h))
    using 1
  ext x
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  exact mem_quotientPointsSubgroup_iff H I (CommAlgCat.of R A) x

end TauCeti.PointTopology
