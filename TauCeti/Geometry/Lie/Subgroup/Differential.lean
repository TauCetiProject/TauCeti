/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility
public import TauCeti.Geometry.Lie.Subgroup.Embedded

/-!
# The Lie algebra of an embedded subgroup

The differential of the inclusion of an embedded Lie subgroup is an injective Lie-algebra
homomorphism. Its range is contained in the ambient Lie algebra of the subgroup: naturality of
the exponential map shows that every one-parameter subgroup tangent to the smaller group stays in
the subgroup.

For the smooth structure supplied by the closed-subgroup theorem, the model vector space is
`TauCeti.Lie.lieSubalgebraOfSubgroup K` itself. The differential of inclusion consequently has
the same finite dimension as that subalgebra, so the containment is an equality. This identifies
the Lie algebra of the subgroup, formed from its own left-invariant derivations, with the
one-parameter-subgroup description inside the ambient Lie algebra.

## Main results

* `TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal`: the Lie map induced by inclusion.
* `TauCeti.Lie.EmbeddedLieSubgroupData.coe_lieExp_smul`: the subgroup exponential, coerced to an
  ambient algebra, is its Banach-algebra exponential.
* `TauCeti.Lie.EmbeddedLieSubgroupData.injective_lieMapSubtypeVal`: this Lie map is injective.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_lieMapSubtypeVal_le`: its range lies in
  `lieSubalgebraOfSubgroup K`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup`: when the subgroup model is
  `lieSubalgebraOfSubgroup K`, the inclusion differential is a Lie equivalence onto that
  subalgebra.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapter 20.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Lie.EmbeddedLieSubgroupData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {K : Subgroup G} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothnessThree

/-- The subgroup inclusion as a smooth monoid morphism, using the smooth structure carried by
embedded-Lie-subgroup data. -/
def subtypeVal (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    ContMDiffMonoidMorphism 𝓘(ℝ, E') I ∞ K G := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  exact
    { toMonoidHom := K.subtype
      contMDiff_toFun := d.contMDiff_subtypeVal }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [T2Space G] in
@[simp]
theorem subtypeVal_apply (d : EmbeddedLieSubgroupData I K E') (k : K) :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    d.subtypeVal k = (k : G) := by
  rfl

/-- The differential at the identity of the inclusion of an embedded Lie subgroup. -/
noncomputable def lieMapSubtypeVal (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    LeftInvariantDerivation 𝓘(ℝ, E') K →ₗ⁅ℝ⁆ LeftInvariantDerivation I G := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  exact lieMap d.subtypeVal

omit [T2Space G] in
/-- The subgroup inclusion Lie map is the Lie functor applied to the smooth inclusion. -/
@[simp]
theorem lieMapSubtypeVal_apply (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    ∀ X : LeftInvariantDerivation 𝓘(ℝ, E') K,
      d.lieMapSubtypeVal X = lieMap d.subtypeVal X := by
  dsimp only
  intro X
  rfl

section Units

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
  {K : Subgroup Rˣ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ R] [FiniteDimensional ℝ E']

/-- Coercing the exponential of an embedded subgroup of algebra units to the ambient algebra gives
the Banach-algebra exponential of its inclusion differential. -/
theorem coe_lieExp_smul
    (d : EmbeddedLieSubgroupData (modelWithCornersSelf ℝ R) K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup (modelWithCornersSelf ℝ E') ∞ K := d.lieGroup
    ∀ (X : LeftInvariantDerivation (modelWithCornersSelf ℝ E') K) (t : ℝ),
      (((d.subtypeVal (lieExp (t • X)) : Rˣ) : R)) =
        NormedSpace.exp (t • unitsLieAlgebraEquiv (d.lieMapSubtypeVal X)) := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup (modelWithCornersSelf ℝ E') ∞ K := d.lieGroup
  dsimp only
  intro X t
  have hmap : d.subtypeVal (lieExp (t • X)) =
      lieExp (d.lieMapSubtypeVal (t • X)) := by
    simpa only [lieMapSubtypeVal_apply] using map_lieExp d.subtypeVal (t • X)
  calc
    _ = ((lieExp (d.lieMapSubtypeVal (t • X)) : Rˣ) : R) := congrArg Units.val hmap
    _ = NormedSpace.exp (unitsLieAlgebraEquiv (d.lieMapSubtypeVal (t • X))) := by
      simpa only [TauCeti.expUnit_coe] using congrArg Units.val
        (lieExp_eq_expUnit (d.lieMapSubtypeVal (t • X)))
    _ = NormedSpace.exp (t • unitsLieAlgebraEquiv (d.lieMapSubtypeVal X)) := by
      congr 2
      rw [map_smul, map_smul]

end Units

omit [T2Space G] in
/-- The Lie map induced by an embedded subgroup inclusion is injective. -/
theorem injective_lieMapSubtypeVal (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    Function.Injective d.lieMapSubtypeVal := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  intro X Y hXY
  let sourceEquiv := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E')) (n := ∞) (by simp) (1 : K))
  let targetEquiv := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have h := congrArg targetEquiv hXY
  rw [lieMapSubtypeVal_apply, lieMapSubtypeVal_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap,
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap] at h
  have hderiv :
      mfderiv 𝓘(ℝ, E') I d.subtypeVal 1 =
        mfderiv 𝓘(ℝ, E') I (fun k : K ↦ (k : G)) 1 :=
    mfderiv_congr (funext fun k ↦ d.subtypeVal_apply k)
  rw [hderiv] at h
  exact sourceEquiv.injective (d.injective_mfderiv_subtypeVal 1 h)

/-- The differential of an embedded subgroup inclusion takes values in the ambient Lie
subalgebra associated to the subgroup. -/
theorem lieMapSubtypeVal_mem_lieSubalgebraOfSubgroup
    (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    ∀ X : LeftInvariantDerivation 𝓘(ℝ, E') K,
      d.lieMapSubtypeVal X ∈ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  intro X
  apply mem_lieSubalgebraOfSubgroup_of_forall
  intro t
  rw [lieMapSubtypeVal_apply, ← map_smul, ← map_lieExp d.subtypeVal]
  exact (lieExp (t • X)).property

/-- The range of the differential of an embedded subgroup inclusion is contained in the ambient
Lie subalgebra associated to the subgroup. -/
theorem range_lieMapSubtypeVal_le (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    d.lieMapSubtypeVal.range ≤ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  rintro _ ⟨X, rfl⟩
  exact d.lieMapSubtypeVal_mem_lieSubalgebraOfSubgroup X

section CanonicalModel

noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

variable (d : EmbeddedLieSubgroupData I K
  (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)

/-- When an embedded subgroup is modeled on its ambient Lie subalgebra, the differential of the
inclusion has exactly that subalgebra as its range. -/
theorem range_lieMapSubtypeVal_eq :
    let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ K :=
      d.lieGroup
    d.lieMapSubtypeVal.range = lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ K :=
    d.lieGroup
  dsimp only
  apply LieSubalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_eq d.range_lieMapSubtypeVal_le
  -- `LieHom.range` is definitionally the range of its underlying linear map.
  change Module.finrank ℝ (LinearMap.range d.lieMapSubtypeVal.toLinearMap) = _
  rw [LinearMap.finrank_range_of_inj d.injective_lieMapSubtypeVal]
  exact finrank_leftInvariantDerivation_eq_modelVectorSpace
    (ContMDiffMul.isInteriorPoint
      (I := 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule))
      (n := ∞) (by simp) (1 : K))

/-- For the smooth structure supplied by the closed-subgroup theorem, the differential of the
inclusion identifies the subgroup's Lie algebra with its one-parameter-subgroup Lie subalgebra in
the ambient group. -/
noncomputable def lieEquivLieSubalgebraOfSubgroup :
    let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ K :=
      d.lieGroup
    LeftInvariantDerivation
        𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) K ≃ₗ⁅ℝ⁆
      lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ K :=
    d.lieGroup
  dsimp only
  exact (d.lieMapSubtypeVal.equivRangeOfInjective d.injective_lieMapSubtypeVal).trans
    (LieEquiv.ofEq _ _ (by rw [d.range_lieMapSubtypeVal_eq]))

/-- The Lie equivalence from the subgroup Lie algebra to the ambient subgroup Lie algebra is the
differential of inclusion on underlying elements. -/
@[simp]
theorem lieEquivLieSubalgebraOfSubgroup_apply
    :
    let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ K :=
      d.lieGroup
    ∀ X : LeftInvariantDerivation
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) K,
      (d.lieEquivLieSubalgebraOfSubgroup X : LeftInvariantDerivation I G) =
        d.lieMapSubtypeVal X := by
  dsimp only
  intro X
  simp only [lieEquivLieSubalgebraOfSubgroup, id_eq, LieEquiv.trans_apply,
    LieHom.equivRangeOfInjective_apply, LieEquiv.ofEq_apply]

end CanonicalModel

end TauCeti.Lie.EmbeddedLieSubgroupData
