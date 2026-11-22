/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup
import TauCeti.RepresentationTheory.Quotient

/-!
# The adjoint action of `G ⧸ N` on `𝔤 ⧸ 𝔫`

Let `N` be a closed normal subgroup of a Lie group `G`, with Lie algebra `𝔫 ⊆ 𝔤`
(`Subgroup.groupLieSubalgebra N`). The adjoint representation of `G` preserves `𝔫`, and `N` acts
trivially on `𝔤 ⧸ 𝔫` because `Ad_n ξ - ξ ∈ 𝔫` for `n ∈ N`
(`TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup`). So the adjoint representation descends
to a representation of the quotient group `G ⧸ N` on `𝔤 ⧸ 𝔫`,
`Subgroup.quotientAdjointRepresentation N`, by `[g] · [ξ] = [Ad_g ξ]`; its pullback to `G` is the
quotient representation of `G` on `𝔤 ⧸ 𝔫`. No Lie group structure on `G ⧸ N` is assumed or
constructed here. When `G ⧸ N` carries a quotient Lie group structure, the differential at the
identity of the projection `G → G ⧸ N` induces a canonical isomorphism `𝔤 ⧸ 𝔫 ≃ Lie(G ⧸ N)`, and
under it this representation and its dual on `(𝔤 ⧸ 𝔫)*` correspond to the adjoint and coadjoint
representations of `G ⧸ N`; that comparison is not proved here.

The dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*` and its comparison with the coadjoint action of `G` on
the annihilator `𝔫⁰ ⊆ 𝔤*` are in `TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Quotient`.

## Main definitions

* `Subgroup.quotientAdjointRepresentation`: the representation of `G ⧸ N` on `𝔤 ⧸ 𝔫` induced by
  the adjoint representation.

## Main results

* `TauCeti.Lie.isTrivial_quotient_adjointRepresentation_comp_subtype`: `N` acts trivially on
  `𝔤 ⧸ 𝔫`.
* `TauCeti.Lie.quotientAdjointRepresentation_comp_mk'`: the pullback of
  `Subgroup.quotientAdjointRepresentation N` to `G` is the quotient of the adjoint representation.
* `TauCeti.Lie.quotientAdjointRepresentation_mk_apply_mk`: `[g] · [ξ] = [Ad_g ξ]`.

## References

* J. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007 (reduction by a normal subgroup).
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **A closed normal subgroup acts trivially on `𝔤 ⧸ 𝔫`**: the restriction to `N` of the
representation of `G` on `𝔤 ⧸ 𝔫` induced by the adjoint representation is trivial. -/
theorem isTrivial_quotient_adjointRepresentation_comp_subtype {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) :
    Representation.IsTrivial (((adjointRepresentation ℝ I G).quotient
      (N.groupLieSubalgebra (I := I)).toSubmodule
      groupLieSubalgebra_le_comap_adjointRepresentation).comp N.subtype) :=
  ⟨fun n ↦ by
    rw [MonoidHom.comp_apply]
    exact (Representation.quotient_apply_eq_id_iff (ρ := adjointRepresentation ℝ I G)
      groupLieSubalgebra_le_comap_adjointRepresentation).2
      (adjointRepresentation_apply_sub_mem_groupLieSubalgebra hN n.property)⟩

/-- **The adjoint representation of `G ⧸ N` on `𝔤 ⧸ 𝔫`** for a closed normal subgroup `N` with Lie
algebra `𝔫`: the adjoint representation of `G` descends to `𝔤 ⧸ 𝔫` because `𝔫` is `Ad`-invariant,
and then to `G ⧸ N` because `N` acts trivially on `𝔤 ⧸ 𝔫`. -/
def _root_.Subgroup.quotientAdjointRepresentation (N : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) :
    Representation ℝ (G ⧸ N)
      (GroupLieAlgebra I G ⧸ (N.groupLieSubalgebra (I := I)).toSubmodule) :=
  haveI := isTrivial_quotient_adjointRepresentation_comp_subtype (I := I) hN
  ((adjointRepresentation ℝ I G).quotient _
    groupLieSubalgebra_le_comap_adjointRepresentation).ofQuotient N

/-- The definition of `Subgroup.quotientAdjointRepresentation`, whose body is not exposed: it is the
quotient of the adjoint representation, descended through `N`. -/
theorem _root_.Subgroup.quotientAdjointRepresentation_def (N : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) :
    N.quotientAdjointRepresentation (I := I) hN =
      haveI := isTrivial_quotient_adjointRepresentation_comp_subtype (I := I) hN
      ((adjointRepresentation ℝ I G).quotient _
        groupLieSubalgebra_le_comap_adjointRepresentation).ofQuotient N :=
  (rfl)

/-- **The pullback of the adjoint representation of `G ⧸ N` to `G`** is the representation of `G`
on `𝔤 ⧸ 𝔫` induced by the adjoint representation. -/
@[simp]
theorem quotientAdjointRepresentation_comp_mk' {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) :
    (N.quotientAdjointRepresentation (I := I) hN).comp (QuotientGroup.mk' N) =
      (adjointRepresentation ℝ I G).quotient _
        groupLieSubalgebra_le_comap_adjointRepresentation := by
  have := isTrivial_quotient_adjointRepresentation_comp_subtype (I := I) hN
  rw [Subgroup.quotientAdjointRepresentation, Representation.ofQuotient_comp_mk']

/-- The class of `g` acts on the class of `ξ` by `[g] · [ξ] = [Ad_g ξ]`. -/
@[simp]
theorem quotientAdjointRepresentation_mk_apply_mk {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (g : G) (ξ : GroupLieAlgebra I G) :
    N.quotientAdjointRepresentation (I := I) hN g (Submodule.Quotient.mk ξ) =
      Submodule.Quotient.mk (adjointRepresentation ℝ I G g ξ) := by
  have h := DFunLike.congr_fun (quotientAdjointRepresentation_comp_mk' (I := I) hN) g
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h
  rw [h, Representation.quotient_apply, Submodule.mapQ_apply]

end TauCeti.Lie
