/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup
import TauCeti.RepresentationTheory.Dual
import TauCeti.RepresentationTheory.Quotient

/-!
# The adjoint action of `G ⧸ N` and the coadjoint action on the annihilator of `𝔫`

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

Dually, the coadjoint representation of `G` preserves the annihilator `𝔫⁰ ⊆ 𝔤*`, and `N` fixes
`𝔫⁰` pointwise. Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` of linear forms on the quotient with
linear forms vanishing on `𝔫` (`Submodule.dualQuotEquivDualAnnihilator`), the coadjoint action of
`G` on `𝔫⁰` is the dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`
(`Representation.dualQuotEquivDualAnnihilator_symm_dual_apply` for a general representation).

These are linear-algebra ingredients of reduction in stages for a normal subgroup: on the zero
level of the moment map of `N`, the moment map of `G` takes values in `𝔫⁰`, and through
`(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` it gives a map from the zero level to `(𝔤 ⧸ 𝔫)*`. This is the candidate for the
residual moment map before it is descended to the first reduced space.

## Main definitions

* `Subgroup.quotientAdjointRepresentation`: the representation of `G ⧸ N` on `𝔤 ⧸ 𝔫` induced by
  the adjoint representation.

## Main results

* `TauCeti.Lie.isTrivial_quotient_adjointRepresentation_comp_subtype`: `N` acts trivially on
  `𝔤 ⧸ 𝔫`.
* `TauCeti.Lie.quotientAdjointRepresentation_comp_mk'`: the pullback of
  `Subgroup.quotientAdjointRepresentation N` to `G` is the quotient of the adjoint representation.
* `TauCeti.Lie.dual_quotientAdjointRepresentation_comp_mk'`: the pullback of its dual to `G` is the
  dual of the quotient of the adjoint representation.
* `TauCeti.Lie.transpose_quotientAdjointRepresentation_inv_mk_apply_mk`: the dual action of `G ⧸ N`
  on `(𝔤 ⧸ 𝔫)*` evaluates on classes as `([g] · φ) [ξ] = φ [Ad_{g⁻¹} ξ]`.
* `TauCeti.Lie.dualQuotEquivDualAnnihilator_symm_coadjointRepresentation_apply`: the coadjoint
  action of `G` on `𝔫⁰` is the dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`.

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

/-- **The pullback of the dual action of `G ⧸ N` to `G`** is the dual of the representation of `G`
on `𝔤 ⧸ 𝔫` induced by the adjoint representation. -/
@[simp]
theorem dual_quotientAdjointRepresentation_comp_mk' {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) :
    (N.quotientAdjointRepresentation (I := I) hN).dual.comp (QuotientGroup.mk' N) =
      ((adjointRepresentation ℝ I G).quotient _
        groupLieSubalgebra_le_comap_adjointRepresentation).dual := by
  rw [← Representation.dual_comp, quotientAdjointRepresentation_comp_mk']

/-- The dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`: `([g] · φ) [ξ] = φ [Ad_{g⁻¹} ξ]`, stated on the
transpose `Module.Dual.transpose ([g]⁻¹ · -)` to which `Representation.dual_apply` rewrites the
dual action. -/
@[simp]
theorem transpose_quotientAdjointRepresentation_inv_mk_apply_mk {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (g : G)
    (φ : Module.Dual ℝ
      (GroupLieAlgebra I G ⧸ (N.groupLieSubalgebra (I := I)).toSubmodule))
    (ξ : GroupLieAlgebra I G) :
    Module.Dual.transpose (R := ℝ)
        (N.quotientAdjointRepresentation (I := I) hN (g : G ⧸ N)⁻¹) φ
        (Submodule.Quotient.mk ξ) =
      φ (Submodule.Quotient.mk (adjointRepresentation ℝ I G g⁻¹ ξ)) := by
  rw [Module.Dual.transpose_apply, LinearMap.comp_apply, ← QuotientGroup.mk_inv,
    quotientAdjointRepresentation_mk_apply_mk]

/-- **The coadjoint action of `G` on `𝔫⁰` is the dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`.**
Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` of `Submodule.dualQuotEquivDualAnnihilator`, the coadjoint
translate `Ad*_g ν` of `ν ∈ 𝔫⁰` corresponds to the translate of the corresponding form on `𝔤 ⧸ 𝔫`
by the class of `g` in `G ⧸ N`. -/
theorem dualQuotEquivDualAnnihilator_symm_coadjointRepresentation_apply {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (g : G) {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ν ∈ (N.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator) :
    (N.groupLieSubalgebra (I := I)).toSubmodule.dualQuotEquivDualAnnihilator.symm
        ⟨coadjointRepresentation ℝ I G g ν,
          coadjointRepresentation_apply_mem_dualAnnihilator_groupLieSubalgebra
            (Subgroup.normalizer_eq_top (H := N) ▸ Subgroup.mem_top g) hν⟩ =
      (N.quotientAdjointRepresentation (I := I) hN).dual g
        ((N.groupLieSubalgebra (I := I)).toSubmodule.dualQuotEquivDualAnnihilator.symm
          ⟨ν, hν⟩) := by
  have h := DFunLike.congr_fun (dual_quotientAdjointRepresentation_comp_mk' (I := I) hN) g
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h
  rw [h, ← Representation.dualQuotEquivDualAnnihilator_symm_dual_apply]
  simp only [coadjointRepresentation_def]

end TauCeti.Lie
