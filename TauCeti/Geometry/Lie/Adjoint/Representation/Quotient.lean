/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup
public import TauCeti.Geometry.Lie.Subgroup.NormalQuotient
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.RepresentationTheory.Quotient

/-!
# The adjoint action of `G ⧸ N` on `𝔤 ⧸ 𝔫`

Let `N` be a closed normal subgroup of a Lie group `G`, with Lie algebra `𝔫 ⊆ 𝔤`
(`Subgroup.groupLieSubalgebra N`). The adjoint representation of `G` preserves `𝔫`, and `N` acts
trivially on `𝔤 ⧸ 𝔫` because `Ad_n ξ - ξ ∈ 𝔫` for `n ∈ N`
(`TauCeti.Geometry.Lie.Adjoint.Representation.Subgroup`). So the adjoint representation descends
to a representation of the quotient group `G ⧸ N` on `𝔤 ⧸ 𝔫`,
`Subgroup.quotientAdjointRepresentation N`, by `[g] · [ξ] = [Ad_g ξ]`; its pullback to `G` is the
quotient representation of `G` on `𝔤 ⧸ 𝔫`. Its definition uses no Lie group structure on
`G ⧸ N`. For a boundaryless model, `G ⧸ N` is a Lie group (`Subgroup.lieGroup_quotientOfIsClosed`);
the differential at the identity of the projection `G → G ⧸ N` vanishes exactly on `𝔫` and is
surjective, so it induces a linear isomorphism `𝔤 ⧸ 𝔫 ≃ Lie(G ⧸ N)`
(`Subgroup.quotientGroupLieAlgebraEquiv`), and this isomorphism intertwines
`Subgroup.quotientAdjointRepresentation N` with the adjoint representation of `G ⧸ N`.

The dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*` and its comparison with the coadjoint action of `G` on
the annihilator `𝔫⁰ ⊆ 𝔤*` are in `TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Quotient`.

## Main definitions

* `Subgroup.quotientAdjointRepresentation`: the representation of `G ⧸ N` on `𝔤 ⧸ 𝔫` induced by
  the adjoint representation.
* `Subgroup.quotientGroupLieAlgebraEquiv`: the identification of `𝔤 ⧸ 𝔫` with the tangent Lie
  algebra of the quotient Lie group `G ⧸ N`, induced by the differential of the projection.

## Main results

* `TauCeti.Lie.isTrivial_quotient_adjointRepresentation_comp_subtype`: `N` acts trivially on
  `𝔤 ⧸ 𝔫`.
* `TauCeti.Lie.quotientAdjointRepresentation_comp_mk'`: the pullback of
  `Subgroup.quotientAdjointRepresentation N` to `G` is the quotient of the adjoint representation.
* `TauCeti.Lie.quotientAdjointRepresentation_mk_apply_mk`: `[g] · [ξ] = [Ad_g ξ]`.
* `TauCeti.Lie.groupLieAlgebraMap_quotientGroupMk'_eq_zero_iff`,
  `TauCeti.Lie.surjective_groupLieAlgebraMap_quotientGroupMk'`: the differential at the identity of
  `G → G ⧸ N` has kernel `𝔫` and is surjective.
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

/-! ### Comparison with the Lie algebra of the quotient Lie group -/

section QuotientLieGroup

variable [I.Boundaryless]

/-- **The differential of the projection onto `G ⧸ N` vanishes exactly on `𝔫`.** For a closed
normal subgroup `N`, with `G ⧸ N` carrying the charts `Subgroup.quotientChartedSpaceOfIsClosed`,
the kernel of the differential at the identity of `G → G ⧸ N` is the Lie algebra of `N`. -/
theorem groupLieAlgebraMap_quotientGroupMk'_eq_zero_iff {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) {ξ : GroupLieAlgebra I G} :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
    (QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, Subgroup.QuotientModelSpace I N) ξ = 0 ↔
      ξ ∈ N.groupLieSubalgebra (I := I) := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hN
  have := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, Subgroup.QuotientModelSpace I N)) (n := ∞)
      (by simp) (1 : G ⧸ N))
  -- Read at the identity, the Lie map of the projection is its differential.
  have h : e' (lieMap (Subgroup.quotientMkSmoothHom I hN) (e.symm ξ)) =
      (QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, Subgroup.QuotientModelSpace I N) ξ := by
    rw [leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap, LieEquiv.apply_symm_apply,
      Subgroup.coe_quotientMkSmoothHom, MonoidHom.groupLieAlgebraMap_apply, QuotientGroup.coe_mk']
  rw [← h, map_eq_zero_iff e' e'.injective, Subgroup.lieMap_quotientMkSmoothHom_eq_zero_iff,
    mem_groupLieSubalgebra_iff, leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply]

/-- **The differential of the projection onto `G ⧸ N` is surjective**, for a closed normal subgroup
`N` and the charts `Subgroup.quotientChartedSpaceOfIsClosed` on `G ⧸ N`. -/
theorem surjective_groupLieAlgebraMap_quotientGroupMk' {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
    Function.Surjective
      ((QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, Subgroup.QuotientModelSpace I N)) := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hN
  intro v
  obtain ⟨ξ, hξ⟩ := (Subgroup.isSubmersion_quotientMk (I := I) hN).surjective_mfderiv (by simp) 1 v
  refine ⟨ξ, ?_⟩
  rwa [MonoidHom.groupLieAlgebraMap_apply, QuotientGroup.coe_mk']

/-- **The tangent Lie algebra of `G ⧸ N` is `𝔤 ⧸ 𝔫`**: for a closed normal subgroup `N`, the
differential at the identity of the projection `G → G ⧸ N` induces a linear isomorphism from
`𝔤 ⧸ 𝔫` onto the tangent Lie algebra of the quotient Lie group `G ⧸ N`
(`Subgroup.lieGroup_quotientOfIsClosed`). -/
def _root_.Subgroup.quotientGroupLieAlgebraEquiv (N : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
    (GroupLieAlgebra I G ⧸ (N.groupLieSubalgebra (I := I)).toSubmodule) ≃ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℝ, Subgroup.QuotientModelSpace I N) (G ⧸ N) :=
  letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
  (Submodule.quotEquivOfEq _ _ (Submodule.ext fun _ ↦
      (groupLieAlgebraMap_quotientGroupMk'_eq_zero_iff hN).symm)).trans
    (LinearMap.quotKerEquivOfSurjective
      ((QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, Subgroup.QuotientModelSpace I N) :
        GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, Subgroup.QuotientModelSpace I N) (G ⧸ N))
      (surjective_groupLieAlgebraMap_quotientGroupMk' hN))

/-- The identification `𝔤 ⧸ 𝔫 ≃ Lie(G ⧸ N)` sends the class of `ξ` to the differential at the
identity of the projection, applied to `ξ`. -/
@[simp]
theorem quotientGroupLieAlgebraEquiv_mk {N : Subgroup G} [N.Normal] (hN : IsClosed (N : Set G))
    (ξ : GroupLieAlgebra I G) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
    N.quotientGroupLieAlgebraEquiv hN (Submodule.Quotient.mk ξ) =
      (QuotientGroup.mk' N).groupLieAlgebraMap I 𝓘(ℝ, Subgroup.QuotientModelSpace I N) ξ := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hN
  rw [Subgroup.quotientGroupLieAlgebraEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, ContinuousLinearMap.coe_coe]

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
  rw [quotientAdjointRepresentation_mk_apply_mk, quotientGroupLieAlgebraEquiv_mk,
    quotientGroupLieAlgebraEquiv_mk, adjointRepresentation_apply, adjointRepresentation_apply]
  exact (QuotientGroup.mk' N).groupLieAlgebraMap_adjointContinuousLinearMap g ξ

end QuotientLieGroup

end TauCeti.Lie
