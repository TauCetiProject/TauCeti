/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Basic
public import TauCeti.Geometry.Lie.Subgroup.Differential

/-!
# The differential of an immersed Lie subgroup presentation

An immersed Lie subgroup is presented by a connected Lie group `X` and an injective smooth
immersion `X → G` whose image is the specified subgroup `K`. The Lie functor sends this
presentation to an injective Lie-algebra homomorphism. Naturality of the exponential shows that
its range lies in the ambient Lie algebra associated to `K`: every one-parameter subgroup in the
image comes from a one-parameter subgroup of `X`, hence remains in `K`.

The source has its intrinsic manifold topology, which need not be the subspace topology inherited
from `G`. None of the arguments below identify those topologies. The source Lie-group structure
supplies the Hausdorff instance needed by the exponential API.

## Main results

* `TauCeti.Lie.ImmersedLieSubgroupData.toContMDiffMonoidMorphism`: the presenting homomorphism as
  a smooth monoid morphism.
* `TauCeti.Lie.ImmersedLieSubgroupData.lieMapToHom`: its differential at the identity.
* `TauCeti.Lie.ImmersedLieSubgroupData.injective_lieMapToHom`: the differential is injective.
* `TauCeti.Lie.ImmersedLieSubgroupData.range_lieMapToHom_le`: its range lies in
  `TauCeti.Lie.lieSubalgebraOfSubgroup K`.

* `TauCeti.Lie.ImmersedLieSubgroupData.toHom_lieExp`: exponential naturality.
* `TauCeti.Lie.ImmersedLieSubgroupData.lieHomOfRangeLe`: the canonical Lie-algebra
  factorization, with ambient apply, uniqueness, identity and composition formulas, including
  the applied `TauCeti.Lie.ImmersedLieSubgroupData.lieHomOfRangeLe_lieHomOfRangeLe`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapters 8 and 20.
-/

public section

noncomputable section

open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Lie.ImmersedLieSubgroupData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {K : Subgroup G} [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The homomorphism presenting an immersed Lie subgroup, packaged as a smooth monoid morphism. -/
def toContMDiffMonoidMorphism (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ContMDiffMonoidMorphism d.I' I ∞ d.X G := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  exact { toMonoidHom := d.toHom, contMDiff_toFun := d.contMDiff_toHom }

omit [FiniteDimensional ℝ E] [T2Space G] in
/-- The smooth monoid morphism underlying an immersed presentation is its presenting
homomorphism. -/
@[simp]
theorem toContMDiffMonoidMorphism_apply (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ∀ x : d.X, d.toContMDiffMonoidMorphism x = d.toHom x := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  intro x
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] in
/-- The monoid homomorphism underlying the smooth monoid morphism of an immersed presentation is
its presenting homomorphism. -/
@[simp]
theorem toContMDiffMonoidMorphism_toMonoidHom (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    d.toContMDiffMonoidMorphism.toMonoidHom = d.toHom := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  ext x
  exact d.toContMDiffMonoidMorphism_apply x

/-- The Lie map induced by the homomorphism presenting an immersed Lie subgroup. -/
noncomputable def lieMapToHom (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    LeftInvariantDerivation d.I' d.X →ₗ⁅ℝ⁆ LeftInvariantDerivation I G := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  exact lieMap d.toContMDiffMonoidMorphism

omit [T2Space G] in
/-- The immersed-presentation Lie map is the Lie functor applied to its smooth homomorphism. -/
@[simp]
theorem lieMapToHom_apply (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ∀ X : LeftInvariantDerivation d.I' d.X,
      d.lieMapToHom X = lieMap d.toContMDiffMonoidMorphism X := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  intro X
  rfl

omit [T2Space G] in
/-- The Lie functor applied to the smooth homomorphism of an immersed presentation is its
differential `lieMapToHom`. -/
theorem lieMap_toContMDiffMonoidMorphism (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    lieMap d.toContMDiffMonoidMorphism = d.lieMapToHom := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  apply LieHom.ext
  intro X
  exact (d.lieMapToHom_apply X).symm

omit [T2Space G] in
/-- The Lie map induced by an immersed subgroup presentation is injective. -/
theorem injective_lieMapToHom (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    Function.Injective d.lieMapToHom := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  apply ContMDiffMonoidMorphism.lieMap_injective_of_mfderiv_injective
  exact d.injective_mfderiv_toHom 1

/-- The differential of an immersed presentation takes every source derivation into the ambient
Lie subalgebra associated to its image subgroup. -/
theorem lieMapToHom_mem_lieSubalgebraOfSubgroup (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ∀ X : LeftInvariantDerivation d.I' d.X,
      d.lieMapToHom X ∈ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  intro X
  apply range_lieMap_le_lieSubalgebraOfSubgroup d.toContMDiffMonoidMorphism
  · simpa only [toContMDiffMonoidMorphism] using le_of_eq d.range_eq
  · exact ⟨X, rfl⟩

/-- The range of the differential of an immersed presentation lies in the ambient Lie subalgebra
associated to its image subgroup. -/
theorem range_lieMapToHom_le (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    d.lieMapToHom.range ≤ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  apply range_lieMap_le_lieSubalgebraOfSubgroup d.toContMDiffMonoidMorphism
  simpa only [toContMDiffMonoidMorphism] using le_of_eq d.range_eq


section Factorization

variable {L M : Subgroup G}

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.finiteDimensional
  ImmersedLieSubgroupData.modelTopology ImmersedLieSubgroupData.chartedSpace
  ImmersedLieSubgroupData.isManifold ImmersedLieSubgroupData.lieGroup
  ImmersedLieSubgroupData.connectedSpace

/-- The presenting injection intertwines the Lie-group exponentials. -/
@[simp]
theorem toHom_lieExp (d : ImmersedLieSubgroupData I K)
    (X : LeftInvariantDerivation d.I' d.X) :
    let _ : T2Space d.X := d.I'.t2Space_of_lieGroup ∞
    d.toHom (lieExp X) = lieExp (d.lieMapToHom X) := by
  let _ : T2Space d.X := d.I'.t2Space_of_lieGroup ∞
  simpa only [toContMDiffMonoidMorphism_apply, lieMap_toContMDiffMonoidMorphism] using
    map_lieExp d.toContMDiffMonoidMorphism X

omit [T2Space G] in
/-- The canonical Lie-algebra factorization for included differential ranges. -/
noncomputable def lieHomOfRangeLe (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : d.lieMapToHom.range ≤ e.lieMapToHom.range) :
    LeftInvariantDerivation d.I' d.X →ₗ⁅ℝ⁆ LeftInvariantDerivation e.I' e.X :=
  (e.lieMapToHom.equivRangeOfInjective e.injective_lieMapToHom).symm.toLieHom.comp
    ((LieSubalgebra.inclusion h).comp d.lieMapToHom.rangeRestrict)

omit [T2Space G] in
/-- The canonical Lie-algebra factorization commutes with the ambient differentials. -/
@[simp]
theorem lieMap_lieHomOfRangeLe_apply (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : d.lieMapToHom.range ≤ e.lieMapToHom.range)
    (X : LeftInvariantDerivation d.I' d.X) :
    lieMap e.toContMDiffMonoidMorphism (d.lieHomOfRangeLe e h X) =
      lieMap d.toContMDiffMonoidMorphism X := by
  have hright := congrArg Subtype.val
    ((e.lieMapToHom.equivRangeOfInjective e.injective_lieMapToHom).apply_symm_apply
      ((LieSubalgebra.inclusion h) (d.lieMapToHom.rangeRestrict X)))
  simpa only [lieMap_toContMDiffMonoidMorphism, lieHomOfRangeLe, LieHom.comp_apply,
    LieEquiv.coe_toLieHom, LieHom.equivRangeOfInjective_apply,
    LieSubalgebra.coe_inclusion, LieHom.rangeRestrict_apply] using hright

omit [T2Space G] in
/-- The ambient differential diagram determines the canonical Lie-algebra factorization. -/
theorem eq_lieHomOfRangeLe (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : d.lieMapToHom.range ≤ e.lieMapToHom.range)
    (φ : LeftInvariantDerivation d.I' d.X →ₗ⁅ℝ⁆ LeftInvariantDerivation e.I' e.X)
    (hφ : ∀ X, lieMap e.toContMDiffMonoidMorphism (φ X) =
      lieMap d.toContMDiffMonoidMorphism X) : φ = d.lieHomOfRangeLe e h := by
  apply LieHom.ext
  intro X
  apply e.injective_lieMapToHom
  simpa only [lieMapToHom_apply, lieMap_lieHomOfRangeLe_apply] using hφ X

omit [T2Space G] in
/-- Factoring a differential through itself gives the identity Lie homomorphism. -/
@[simp]
theorem lieHomOfRangeLe_refl (d : ImmersedLieSubgroupData I K) :
    d.lieHomOfRangeLe d le_rfl = LieHom.id := by
  symm
  apply d.eq_lieHomOfRangeLe d le_rfl
  intro X
  simp only [LieHom.id_apply]

omit [T2Space G] in
/-- Canonical Lie-algebra factorizations compose according to range inclusion. -/
@[simp]
theorem lieHomOfRangeLe_comp (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (f : ImmersedLieSubgroupData I M)
    (hKL : d.lieMapToHom.range ≤ e.lieMapToHom.range)
    (hLM : e.lieMapToHom.range ≤ f.lieMapToHom.range) :
    (e.lieHomOfRangeLe f hLM).comp (d.lieHomOfRangeLe e hKL) =
      d.lieHomOfRangeLe f (hKL.trans hLM) := by
  apply d.eq_lieHomOfRangeLe f (hKL.trans hLM)
  intro X
  simp only [LieHom.comp_apply, lieMap_lieHomOfRangeLe_apply]

omit [T2Space G] in
/-- Successive Lie factorizations evaluate as the factorization of the composed inclusion. -/
@[simp]
theorem lieHomOfRangeLe_lieHomOfRangeLe (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (f : ImmersedLieSubgroupData I M)
    (hKL : d.lieMapToHom.range ≤ e.lieMapToHom.range)
    (hLM : e.lieMapToHom.range ≤ f.lieMapToHom.range)
    (X : LeftInvariantDerivation d.I' d.X) :
    e.lieHomOfRangeLe f hLM (d.lieHomOfRangeLe e hKL X) =
      d.lieHomOfRangeLe f (hKL.trans hLM) X := by
  simpa only [LieHom.comp_apply] using
    DFunLike.congr_fun (d.lieHomOfRangeLe_comp e f hKL hLM) X

end Factorization

end TauCeti.Lie.ImmersedLieSubgroupData
