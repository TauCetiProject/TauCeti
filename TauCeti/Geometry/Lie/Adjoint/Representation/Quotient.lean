/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.GroupLieAlgebra
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.Quotient

/-!
# The adjoint action of `G ⧸ N` and the coadjoint action on the annihilator of `𝔫`

Let `N` be a closed normal subgroup of a Lie group `G`, with Lie algebra `𝔫 ⊆ 𝔤`
(`TauCeti.Lie.groupLieSubalgebraOfSubgroup N`). The adjoint representation of `G` preserves `𝔫`,
and `N` acts trivially on `𝔤 ⧸ 𝔫` because `Ad_n ξ - ξ ∈ 𝔫` for `n ∈ N`. So the adjoint
representation descends to a representation of the quotient group `G ⧸ N` on `𝔤 ⧸ 𝔫`,
`TauCeti.Lie.quotientAdjointRepresentation N`, by `[g] · [ξ] = [Ad_g ξ]`. This is intended to
become the adjoint representation of `G ⧸ N`, and its dual on `(𝔤 ⧸ 𝔫)*` the coadjoint
representation of `G ⧸ N`, once the quotient Lie group and the identification
`Lie(G ⧸ N) ≃ 𝔤 ⧸ 𝔫` are available; neither is proved here.

Dually, the coadjoint representation of `G` preserves the annihilator `𝔫⁰ ⊆ 𝔤*` of `𝔫`, and `N`
fixes `𝔫⁰` pointwise. Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` of linear forms on the quotient
with linear forms vanishing on `𝔫` (`Submodule.dualQuotEquivDualAnnihilator`), the coadjoint
action of `G` on `𝔫⁰` is the dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`.

These are the linear-algebra ingredients of reduction in stages for a normal subgroup: on the zero
level of the moment map of `N`, the moment map of `G` takes values in `𝔫⁰`, where it is the moment
map of the residual action of `G ⧸ N`.

## Main definitions

* `TauCeti.Lie.quotientAdjointRepresentation`: the representation of `G ⧸ N` on `𝔤 ⧸ 𝔫` induced by
  the adjoint representation.

## Main results

* `TauCeti.Lie.isTrivial_quotient_adjointRepresentation_comp_subtype`: `N` acts trivially on
  `𝔤 ⧸ 𝔫`.
* `TauCeti.Lie.coadjointRepresentation_apply_mem_dualAnnihilator`: the coadjoint action preserves
  `𝔫⁰`.
* `TauCeti.Lie.coadjointRepresentation_apply_eq_self_of_mem_dualAnnihilator`: `N` fixes `𝔫⁰`
  pointwise.
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
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **A closed normal subgroup acts trivially on `𝔤 ⧸ 𝔫`**: the restriction to `N` of the
representation of `G` on `𝔤 ⧸ 𝔫` induced by the adjoint representation is trivial. -/
theorem isTrivial_quotient_adjointRepresentation_comp_subtype {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) :
    Representation.IsTrivial (((adjointRepresentation ℝ I G).quotient
      (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule
      groupLieSubalgebraOfSubgroup_le_comap_adjointRepresentation).comp N.subtype) :=
  ⟨fun n ↦ by
    rw [MonoidHom.comp_apply]
    exact Representation.quotient_apply_eq_id (ρ := adjointRepresentation ℝ I G)
      groupLieSubalgebraOfSubgroup_le_comap_adjointRepresentation
      (adjointRepresentation_apply_sub_mem_groupLieSubalgebraOfSubgroup hN n.2)⟩

/-- **The adjoint representation of `G ⧸ N` on `𝔤 ⧸ 𝔫`** for a closed normal subgroup `N` with Lie
algebra `𝔫`: the adjoint representation of `G` descends to `𝔤 ⧸ 𝔫` because `𝔫` is `Ad`-invariant,
and then to `G ⧸ N` because `N` acts trivially on `𝔤 ⧸ 𝔫`. -/
def quotientAdjointRepresentation (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    Representation ℝ (G ⧸ N)
      (GroupLieAlgebra I G ⧸ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule) :=
  haveI := isTrivial_quotient_adjointRepresentation_comp_subtype (I := I) hN
  ((adjointRepresentation ℝ I G).quotient _
    groupLieSubalgebraOfSubgroup_le_comap_adjointRepresentation).ofQuotient N

/-- The class of `g` acts on the class of `ξ` by `[g] · [ξ] = [Ad_g ξ]`. -/
@[simp]
theorem quotientAdjointRepresentation_mk_apply_mk {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (g : G) (ξ : GroupLieAlgebra I G) :
    quotientAdjointRepresentation (I := I) N hN g (Submodule.Quotient.mk ξ) =
      Submodule.Quotient.mk (adjointRepresentation ℝ I G g ξ) :=
  (rfl)

/-- The dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`: `([g] · φ) [ξ] = φ [Ad_{g⁻¹} ξ]`. Not a `simp`
lemma, since `Representation.dual_apply` already rewrites its left-hand side. -/
theorem dual_quotientAdjointRepresentation_mk_apply_mk {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (g : G)
    (φ : Module.Dual ℝ
      (GroupLieAlgebra I G ⧸ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule))
    (ξ : GroupLieAlgebra I G) :
    (quotientAdjointRepresentation (I := I) N hN).dual g φ (Submodule.Quotient.mk ξ) =
      φ (Submodule.Quotient.mk (adjointRepresentation ℝ I G g⁻¹ ξ)) := by
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    ← QuotientGroup.mk_inv, quotientAdjointRepresentation_mk_apply_mk]

/-- **The coadjoint action preserves the annihilator of the Lie algebra of a normal subgroup.** -/
theorem coadjointRepresentation_apply_mem_dualAnnihilator {N : Subgroup G} [N.Normal] (g : G)
    {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ν ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator) :
    coadjointRepresentation ℝ I G g ν ∈
      (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator := by
  rw [coadjointRepresentation_eq_dual]
  exact (adjointRepresentation ℝ I G).dualAnnihilator_le_comap_dual
    groupLieSubalgebraOfSubgroup_le_comap_adjointRepresentation g hν

/-- **A closed normal subgroup fixes the annihilator of its Lie algebra**: `Ad*_n ν = ν` for
`n ∈ N` and `ν ∈ 𝔫⁰`. -/
theorem coadjointRepresentation_apply_eq_self_of_mem_dualAnnihilator {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) {n : G} (hn : n ∈ N) {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ν ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator) :
    coadjointRepresentation ℝ I G n ν = ν := by
  rw [coadjointRepresentation_eq_dual]
  exact Representation.dual_apply_eq_self_of_mem_dualAnnihilator
    (adjointRepresentation_apply_sub_mem_groupLieSubalgebraOfSubgroup hN hn) hν

/-- **The coadjoint action of `G` on `𝔫⁰` is the dual action of `G ⧸ N` on `(𝔤 ⧸ 𝔫)*`.**
Under the identification `(𝔤 ⧸ 𝔫)* ≃ 𝔫⁰` of `Submodule.dualQuotEquivDualAnnihilator`, the coadjoint
translate `Ad*_g ν` of `ν ∈ 𝔫⁰` corresponds to the translate of the corresponding form on `𝔤 ⧸ 𝔫`
by the class of `g` in `G ⧸ N`. -/
theorem dualQuotEquivDualAnnihilator_symm_coadjointRepresentation_apply {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) (g : G) {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ν ∈ (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualAnnihilator) :
    (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator.symm
        ⟨coadjointRepresentation ℝ I G g ν,
          coadjointRepresentation_apply_mem_dualAnnihilator g hν⟩ =
      (quotientAdjointRepresentation (I := I) N hN).dual g
        ((groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.dualQuotEquivDualAnnihilator.symm
          ⟨ν, hν⟩) := by
  ext ξ
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply,
    dual_quotientAdjointRepresentation_mk_apply_mk,
    Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk, adjointRepresentation_apply]
  -- The left side is the anonymous-constructor element `⟨Ad*_g ν, _⟩` of `𝔫⁰` applied to `ξ`,
  -- whose coercion to `𝔤*` is `Ad*_g ν` by projection.
  exact coadjointRepresentation_apply g ν ξ

end TauCeti.Lie
