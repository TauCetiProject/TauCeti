/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
import TauCeti.Geometry.Lie.Adjoint.Derivation

/-!
# The Lie algebra of a subgroup in the tangent Lie algebra

The Lie algebra `TauCeti.Lie.lieSubalgebraOfSubgroup K` of a subgroup `K` of a Lie group `G` lives
in the left-invariant derivations of `G`. Moment maps, the adjoint and coadjoint representations and
the differentials of homomorphisms are stated on the tangent Lie algebra `𝔤 = GroupLieAlgebra I G`
at the identity instead. This file transports the Lie algebra of `K` along evaluation at the
identity (`TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra`) to a Lie subalgebra
`𝔨 ⊆ 𝔤`, `TauCeti.Lie.groupLieSubalgebraOfSubgroup K`, and records its properties there.

* For a closed subgroup, `ξ ∈ 𝔨` exactly when the one-parameter subgroup `t ↦ exp (t ξ)` stays in
  `K`.
* `𝔨` is invariant under `Ad_g` for `g` in the normalizer of `K`; so for a normal subgroup `N` it
  is a subrepresentation of the adjoint representation.
* For a closed normal subgroup `N` and `n ∈ N`, `Ad_n ξ - ξ ∈ 𝔫` for every `ξ ∈ 𝔤`, so `N` acts
  trivially on `𝔤 ⧸ 𝔫`.
* For an embedded Lie subgroup, `𝔨` is the range of the differential at the identity of the
  inclusion `K → G`, for any finite-dimensional model of `K`. This identifies the restriction
  `μ ∘ dι` of a moment map to `K` with the restriction of `μ` to `𝔨`.

## Main definitions

* `TauCeti.Lie.groupLieSubalgebraOfSubgroup`: the Lie algebra of a subgroup, in the tangent Lie
  algebra.

## Main results

* `TauCeti.Lie.mem_groupLieSubalgebraOfSubgroup`: for a closed subgroup, membership is the
  one-parameter subgroup condition.
* `TauCeti.Lie.adjointRepresentation_apply_mem_groupLieSubalgebraOfSubgroup`: invariance under the
  adjoint action of the normalizer.
* `TauCeti.Lie.adjointRepresentation_apply_sub_mem_groupLieSubalgebraOfSubgroup`: for `n` in a
  closed normal subgroup `N`, `Ad_n - 1` maps `𝔤` into `𝔫`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_subtype`: the differential of an
  embedded inclusion has range `𝔨`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.comp_groupLieAlgebraMap_subtype_eq_zero_iff`: a linear form
  vanishes along that differential exactly when it annihilates `𝔨`.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Section 9.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
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
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The Lie algebra of a subgroup `K`, in the tangent Lie algebra** `𝔤 = GroupLieAlgebra I G`:
the image of `TauCeti.Lie.lieSubalgebraOfSubgroup K` under evaluation of left-invariant
derivations at the identity. -/
def groupLieSubalgebraOfSubgroup (K : Subgroup G) : LieSubalgebra ℝ (GroupLieAlgebra I G) :=
  (lieSubalgebraOfSubgroup (I := I) K).map
    (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))).toLieHom

/-- A tangent vector lies in the Lie algebra of `K` exactly when its left-invariant derivation does.
-/
theorem mem_groupLieSubalgebraOfSubgroup_iff {K : Subgroup G} {ξ : GroupLieAlgebra I G} :
    ξ ∈ groupLieSubalgebraOfSubgroup (I := I) K ↔
      tangentToLeftInvariantDerivation ξ ∈ lieSubalgebraOfSubgroup (I := I) K := by
  rw [groupLieSubalgebraOfSubgroup, LieSubalgebra.mem_map,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))]
  constructor
  · rintro ⟨D, hD, rfl⟩
    rwa [LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply]
  · exact fun h ↦ ⟨_, h, LieEquiv.apply_symm_apply _ _⟩

/-- **The Lie algebra of a closed subgroup** in the tangent Lie algebra consists of the `ξ` whose
one-parameter subgroup `t ↦ exp (t ξ)` stays in `K`. -/
theorem mem_groupLieSubalgebraOfSubgroup {K : Subgroup G} (hK : IsClosed (K : Set G))
    {ξ : GroupLieAlgebra I G} :
    ξ ∈ groupLieSubalgebraOfSubgroup (I := I) K ↔
      ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ K := by
  rw [mem_groupLieSubalgebraOfSubgroup_iff, mem_lieSubalgebraOfSubgroup hK]
  -- `lieExp` of the derivation of `ξ` is `mulInvariantExp ξ`, through the evaluation equivalence.
  simp only [lieExp_eq_mulInvariantExp, map_smul,
    ← leftInvariantDerivationEquivGroupLieAlgebra_symm_apply
      (BoundarylessManifold.isInteriorPoint (I := I) (x := (1 : G))),
    LinearEquiv.apply_symm_apply]

/-- **The Lie algebra of `K` is invariant under the adjoint action of the normalizer of `K`.** -/
theorem adjointRepresentation_apply_mem_groupLieSubalgebraOfSubgroup {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ groupLieSubalgebraOfSubgroup (I := I) K) :
    adjointRepresentation ℝ I G g ξ ∈ groupLieSubalgebraOfSubgroup (I := I) K := by
  rw [mem_groupLieSubalgebraOfSubgroup_iff] at hξ ⊢
  rw [adjointRepresentation_apply, ← tangentAd_apply, tangentToLeftInvariantDerivation_tangentAd]
  exact Ad_mem_lieSubalgebraOfSubgroup hg hξ

/-- The Lie algebra of a normal subgroup is a subrepresentation of the adjoint representation, in
the form consumed by `Representation.quotient` and `Representation.subrepresentation`. -/
theorem groupLieSubalgebraOfSubgroup_le_comap_adjointRepresentation {N : Subgroup G} [N.Normal]
    (g : G) :
    (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule ≤
      (groupLieSubalgebraOfSubgroup (I := I) N).toSubmodule.comap (adjointRepresentation ℝ I G g) :=
  fun _ hξ ↦ adjointRepresentation_apply_mem_groupLieSubalgebraOfSubgroup
    (Subgroup.normalizer_eq_top (H := N) ▸ Subgroup.mem_top g) hξ

/-- **A closed normal subgroup `N` acts trivially on `𝔤 ⧸ 𝔫`**: for `n ∈ N` and every `ξ ∈ 𝔤`,
`Ad_n ξ - ξ` lies in the Lie algebra `𝔫` of `N`. -/
theorem adjointRepresentation_apply_sub_mem_groupLieSubalgebraOfSubgroup {N : Subgroup G}
    [N.Normal] (hN : IsClosed (N : Set G)) {n : G} (hn : n ∈ N) (ξ : GroupLieAlgebra I G) :
    adjointRepresentation ℝ I G n ξ - ξ ∈ groupLieSubalgebraOfSubgroup (I := I) N := by
  rw [mem_groupLieSubalgebraOfSubgroup_iff, map_sub, adjointRepresentation_apply,
    ← tangentAd_apply, tangentToLeftInvariantDerivation_tangentAd]
  exact Ad_sub_mem_lieSubalgebraOfSubgroup hN hn _

namespace EmbeddedLieSubgroupData

variable {K : Subgroup G} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']

/-- **The differential of an embedded inclusion has range the Lie algebra of the subgroup.** For
any finite-dimensional model of an embedded Lie subgroup `K`, the differential at the identity of
the inclusion `K → G` has range `TauCeti.Lie.groupLieSubalgebraOfSubgroup K`. -/
theorem range_groupLieAlgebraMap_subtype (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    LinearMap.range (K.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I).toLinearMap =
      (groupLieSubalgebraOfSubgroup (I := I) K).toSubmodule := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  -- Local names for the evaluation-at-the-identity equivalences of `K` and `G`.
  let eK := leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E')) (G := K)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E')) (n := ∞) (by simp) (1 : K))
  let eG := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have hmap (D : LeftInvariantDerivation 𝓘(ℝ, E') K) :
      K.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I (eK D) = eG (d.lieMapSubtypeVal D) := by
    rw [d.lieMapSubtypeVal_apply, leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap,
      MonoidHom.groupLieAlgebraMap_apply, Subgroup.coe_subtype,
      mfderiv_congr (funext fun k ↦ d.subtypeVal_apply k)]
    -- `eK` and `eG` unfold to the evaluation-at-the-identity equivalences of `K` and `G`.
    rfl
  ext ξ
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨D, rfl⟩ := eK.surjective v
    exact (LieSubalgebra.mem_map _ _ _).2
      ⟨_, d.lieMapSubtypeVal_mem_lieSubalgebraOfSubgroup D, (hmap D).symm⟩
  · rintro ⟨X, hX, rfl⟩
    rw [← d.range_lieMapSubtypeVal_eq] at hX
    obtain ⟨D, rfl⟩ := hX
    exact ⟨eK D, hmap D⟩

/-- **Restriction of a linear form to an embedded subgroup.** A linear form `ν` on `𝔤` vanishes
along the differential `dι` of the inclusion of an embedded Lie subgroup `K` exactly when it
annihilates the Lie algebra `𝔨` of `K`. For a moment map `μ` this identifies the zero level of the
restricted moment map `μ ∘ dι` with the points where `μ` takes values in `𝔨⁰`. -/
theorem comp_groupLieAlgebraMap_subtype_eq_zero_iff (d : EmbeddedLieSubgroupData I K E')
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    let _ : ChartedSpace E' K := d.chartedSpace
    ν.comp (K.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I).toLinearMap = 0 ↔
      ν ∈ (groupLieSubalgebraOfSubgroup (I := I) K).toSubmodule.dualAnnihilator := by
  let _ : ChartedSpace E' K := d.chartedSpace
  dsimp only
  rw [← d.range_groupLieAlgebraMap_subtype, ← LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.mem_ker, LinearMap.dualMap_apply']

end EmbeddedLieSubgroupData

end TauCeti.Lie
