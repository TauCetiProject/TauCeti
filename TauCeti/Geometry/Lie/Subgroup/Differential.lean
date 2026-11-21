/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.Subgroup.GroupLieAlgebra
import TauCeti.Geometry.Lie.Exponential.Classification

/-!
# The Lie algebra of an embedded subgroup

The differential of the inclusion of a finite-dimensional embedded Lie subgroup is an injective
Lie-algebra homomorphism whose range is `TauCeti.Lie.lieSubalgebraOfSubgroup K`. It identifies
the subgroup's native Lie algebra, formed from its own left-invariant derivations, with the
one-parameter-subgroup description inside the ambient Lie algebra. This identification is
independent of the choice of finite-dimensional model for the subgroup.

## Main results

* `TauCeti.Lie.range_lieMap_le_lieSubalgebraOfSubgroup`: a smooth homomorphism whose image lies in
  a subgroup has Lie-map range in that subgroup's ambient Lie algebra.
* `TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal`: the Lie map induced by inclusion.
* `TauCeti.Lie.EmbeddedLieSubgroupData.coe_lieExp_smul`: the subgroup exponential, coerced to an
  ambient algebra, is its Banach-algebra exponential.
* `TauCeti.Lie.EmbeddedLieSubgroupData.injective_lieMapSubtypeVal`: this Lie map is injective.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_lieMapSubtypeVal_le`: its range lies in
  `lieSubalgebraOfSubgroup K`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_lieMapSubtypeVal_eq`: its range equals the
  ambient subgroup Lie algebra for every finite-dimensional subgroup model.
* `TauCeti.Lie.EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup`: the inclusion differential
  is a Lie equivalence onto that subalgebra.
* `TauCeti.Lie.EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply`: the equivalence is
  the inclusion differential on underlying elements.
* `TauCeti.Lie.EmbeddedLieSubgroupData.finrank_eq_finrank_lieSubalgebraOfSubgroup`: the model
  space of the subgroup has the dimension of that subalgebra.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_subtype`: in the tangent Lie
  algebra, the differential of the inclusion at the identity has range
  `Subgroup.groupLieSubalgebra K`, for any model of `K`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.comp_groupLieAlgebraMap_subtype_eq_zero_iff`: a linear form
  vanishes along that differential exactly when it annihilates `Subgroup.groupLieSubalgebra K`;
  for a moment map `μ`, this identifies the zero level of the restriction `μ ∘ dι` to `K`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 8.46, Proposition 20.3, and Theorem 20.12.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Lie

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- If the image of a smooth homomorphism lies in a subgroup, then the range of its Lie map lies
in the ambient Lie algebra associated to that subgroup. -/
theorem range_lieMap_le_lieSubalgebraOfSubgroup {K : Subgroup G'} [T2Space G']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (hφ : MonoidHom.range φ.toMonoidHom ≤ K) :
    (lieMap φ).range ≤ lieSubalgebraOfSubgroup (I := I') K := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  rintro _ ⟨X, rfl⟩
  apply mem_lieSubalgebraOfSubgroup_of_forall
  intro t
  have hmap : φ (lieExp (t • X)) = lieExp (t • lieMap φ X) := by
    simpa only [map_smul] using map_lieExp φ (t • X)
  exact hmap ▸ hφ ⟨lieExp (t • X), rfl⟩

end TauCeti.Lie

namespace TauCeti.Lie.EmbeddedLieSubgroupData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {K : Subgroup G} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

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
  apply ContMDiffMonoidMorphism.lieMap_injective_of_mfderiv_injective
  have hderiv :
      mfderiv 𝓘(ℝ, E') I d.subtypeVal 1 =
        mfderiv 𝓘(ℝ, E') I (fun k : K ↦ (k : G)) 1 :=
    mfderiv_congr (funext fun k ↦ d.subtypeVal_apply k)
  rw [hderiv]
  exact d.injective_mfderiv_subtypeVal 1

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
  apply range_lieMap_le_lieSubalgebraOfSubgroup d.subtypeVal
  · rintro _ ⟨k, rfl⟩
    -- Expose the bundled morphism's underlying function so the inclusion formula applies.
    change d.subtypeVal k ∈ K
    simpa only [subtypeVal_apply] using k.property
  · exact ⟨X, rfl⟩

/-- The range of the differential of an embedded subgroup inclusion is contained in the ambient
Lie subalgebra associated to the subgroup. -/
theorem range_lieMapSubtypeVal_le (d : EmbeddedLieSubgroupData I K E') :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    d.lieMapSubtypeVal.range ≤ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  apply range_lieMap_le_lieSubalgebraOfSubgroup d.subtypeVal
  rintro _ ⟨k, rfl⟩
  -- Expose the bundled morphism's underlying function so the inclusion formula applies.
  change d.subtypeVal k ∈ K
  simpa only [subtypeVal_apply] using k.property

variable (d : EmbeddedLieSubgroupData I K E')

/-- The differential of an embedded subgroup inclusion has the ambient subgroup Lie algebra as
its range, independently of the finite-dimensional model chosen for the subgroup. -/
theorem range_lieMapSubtypeVal_eq :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    d.lieMapSubtypeVal.range = lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  refine le_antisymm d.range_lieMapSubtypeVal_le ?_
  apply lieSubalgebraOfSubgroup_le_iff.mpr
  intro X hX
  have hline (t : Multiplicative ℝ) : oneParameterSubgroup X t ∈ K := by
    simpa only [← oneParameterSubgroup_apply, ofAdd_toAdd] using hX (Multiplicative.toAdd t)
  let χ : ContinuousMonoidHom (Multiplicative ℝ) K :=
    { toMonoidHom := (oneParameterSubgroup X).toMonoidHom.codRestrict K hline
      continuous_toFun := (oneParameterSubgroup X).continuous.subtype_mk hline }
  -- Codomain restriction retains the values of the ambient one-parameter subgroup.
  have hχcoe (t : Multiplicative ℝ) : (χ t : G) = oneParameterSubgroup X t := rfl
  obtain ⟨Y, hY⟩ := oneParameterSubgroup_surjective (I := 𝓘(ℝ, E')) (G := K) χ
  refine ⟨Y, ?_⟩
  apply oneParameterSubgroup_injective (I := I) (G := G)
  ext t
  calc
    oneParameterSubgroup (d.lieMapSubtypeVal Y) t =
        d.subtypeVal (oneParameterSubgroup Y t) := by
      simpa only [map_smul, ← oneParameterSubgroup_apply, ofAdd_toAdd,
        EmbeddedLieSubgroupData.lieMapSubtypeVal_apply] using
          (map_lieExp d.subtypeVal (Multiplicative.toAdd t • Y)).symm
    _ = d.subtypeVal (χ t) := congrArg d.subtypeVal (DFunLike.congr_fun hY t)
    _ = oneParameterSubgroup X t := (d.subtypeVal_apply (χ t)).trans (hχcoe t)

/-- The differential of an embedded subgroup inclusion identifies its native Lie algebra with
the one-parameter-subgroup Lie subalgebra in the ambient group. -/
noncomputable def lieEquivLieSubalgebraOfSubgroup :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    LeftInvariantDerivation 𝓘(ℝ, E') K ≃ₗ⁅ℝ⁆
      lieSubalgebraOfSubgroup (I := I) K := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  dsimp only
  exact (d.lieMapSubtypeVal.equivRangeOfInjective d.injective_lieMapSubtypeVal).trans
    (LieEquiv.ofEq _ _ (by rw [d.range_lieMapSubtypeVal_eq]))

/-- The Lie equivalence from the subgroup Lie algebra to the ambient subgroup Lie algebra is the
differential of inclusion on underlying elements. -/
@[simp]
theorem lieEquivLieSubalgebraOfSubgroup_apply :
    let _ : ChartedSpace E' K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
    ∀ X : LeftInvariantDerivation 𝓘(ℝ, E') K,
      (d.lieEquivLieSubalgebraOfSubgroup X : LeftInvariantDerivation I G) =
        d.lieMapSubtypeVal X := by
  dsimp only
  intro X
  simp only [lieEquivLieSubalgebraOfSubgroup, id_eq, LieEquiv.trans_apply,
    LieHom.equivRangeOfInjective_apply, LieEquiv.ofEq_apply]

include d in
/-- **The dimension of an embedded Lie subgroup is that of its Lie algebra.** The model vector
space of any finite-dimensional embedded-Lie-subgroup structure on `K` has the dimension of the
ambient Lie subalgebra `TauCeti.Lie.lieSubalgebraOfSubgroup K`. -/
theorem finrank_eq_finrank_lieSubalgebraOfSubgroup :
    Module.finrank ℝ E' = Module.finrank ℝ (lieSubalgebraOfSubgroup (I := I) K) := by
  let _ : ChartedSpace E' K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, E') ∞ K := d.lieGroup
  rw [← finrank_leftInvariantDerivation_eq_modelVectorSpace (I := 𝓘(ℝ, E')) (G := K)
    BoundarylessManifold.isInteriorPoint]
  exact d.lieEquivLieSubalgebraOfSubgroup.toLinearEquiv.finrank_eq

omit [FiniteDimensional ℝ E'] in
/-- **The differential of an embedded inclusion has range the Lie algebra of the subgroup.** For
any model of an embedded Lie subgroup `K`, the differential at the identity of
the inclusion `K → G` has range `Subgroup.groupLieSubalgebra K`. -/
theorem range_groupLieAlgebraMap_subtype :
    let _ : ChartedSpace E' K := d.chartedSpace
    LinearMap.range (K.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I).toLinearMap =
      (K.groupLieSubalgebra (I := I)).toSubmodule := by
  let _ : ChartedSpace E' K := d.chartedSpace
  -- The model of `K` embeds into that of `G` through the injective differential of the inclusion.
  have : FiniteDimensional ℝ E' := FiniteDimensional.of_injective
    (mfderiv 𝓘(ℝ, E') I (fun x : K ↦ (x : G)) 1).toLinearMap (d.injective_mfderiv_subtypeVal 1)
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
  rw [LinearMap.mem_range, LieSubalgebra.mem_toSubmodule, K.groupLieSubalgebra_eq_map
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)),
    ← d.range_lieMapSubtypeVal_eq, LieSubalgebra.mem_map, (EquivLike.surjective eK).exists]
  simp [hmap, eG]

omit [FiniteDimensional ℝ E'] in
/-- **Restriction of a linear form to an embedded subgroup.** A linear form `ν` on `𝔤` vanishes
along the differential `dι` of the inclusion of an embedded Lie subgroup `K` exactly when it
annihilates the Lie algebra `𝔨` of `K`. For a moment map `μ` this identifies the zero level of the
restricted moment map `μ ∘ dι` with the points where `μ` takes values in `𝔨⁰`. -/
theorem comp_groupLieAlgebraMap_subtype_eq_zero_iff (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    let _ : ChartedSpace E' K := d.chartedSpace
    ν.comp (K.subtype.groupLieAlgebraMap 𝓘(ℝ, E') I).toLinearMap = 0 ↔
      ν ∈ (K.groupLieSubalgebra (I := I)).toSubmodule.dualAnnihilator := by
  let _ : ChartedSpace E' K := d.chartedSpace
  dsimp only
  rw [← d.range_groupLieAlgebraMap_subtype, ← LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.mem_ker, LinearMap.dualMap_apply']

end TauCeti.Lie.EmbeddedLieSubgroupData
