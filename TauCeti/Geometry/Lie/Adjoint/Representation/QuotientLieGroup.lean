/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Quotient
public import TauCeti.Geometry.Lie.Subgroup.NormalQuotient

/-!
# The adjoint representation of the quotient Lie group `G ⧸ N`

Let `N` be a closed normal subgroup of a Lie group `G` with boundaryless model, with Lie algebra
`𝔫 ⊆ 𝔤`. The adjoint representation of `G` descends to a representation of `G ⧸ N` on `𝔤 ⧸ 𝔫`
(`Subgroup.quotientAdjointRepresentation`), defined without any Lie group structure on `G ⧸ N`.
With the charts `Subgroup.quotientChartedSpaceOfIsClosed`, `G ⧸ N` is a Lie group
(`Subgroup.lieGroup_quotientOfIsClosed`) whose tangent Lie algebra is identified with `𝔤 ⧸ 𝔫`
by the differential of the projection (`Subgroup.quotientGroupLieAlgebraEquiv`). This file shows
that this identification intertwines `Subgroup.quotientAdjointRepresentation N` with the adjoint
representation of the quotient Lie group.

## Main results

* `TauCeti.Lie.quotientGroupLieAlgebraEquiv_quotientAdjointRepresentation_apply`: under
  `𝔤 ⧸ 𝔫 ≃ Lie(G ⧸ N)`, the quotient adjoint representation is the adjoint representation of
  `G ⧸ N`.

## References

* J. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007 (reduction by a normal subgroup).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The quotient adjoint representation is the adjoint representation of `G ⧸ N`**: the
identification `𝔤 ⧸ 𝔫 ≃ Lie(G ⧸ N)` of `Subgroup.quotientGroupLieAlgebraEquiv` intertwines
`Subgroup.quotientAdjointRepresentation N` with the adjoint representation of the quotient Lie
group `G ⧸ N`. -/
theorem quotientGroupLieAlgebraEquiv_quotientAdjointRepresentation_apply {N : Subgroup G}
    [N.Normal] (hN : IsClosed (N : Set G)) (q : G ⧸ N)
    (x : GroupLieAlgebra I G ⧸ (N.groupLieSubalgebra (I := I)).toSubmodule) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
    haveI := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
    N.quotientGroupLieAlgebraEquiv hN (N.quotientAdjointRepresentation hN q x) =
      adjointRepresentation ℝ 𝓘(ℝ, Subgroup.QuotientModelSpace I N) (G ⧸ N) q
        (N.quotientGroupLieAlgebraEquiv hN x) := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hN
  have := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [quotientAdjointRepresentation_mk_apply_mk, Subgroup.quotientGroupLieAlgebraEquiv_apply_mk,
    Subgroup.quotientGroupLieAlgebraEquiv_apply_mk, adjointRepresentation_apply,
    adjointRepresentation_apply]
  exact (QuotientGroup.mk' N).groupLieAlgebraMap_adjointContinuousLinearMap g ξ

end TauCeti.Lie
