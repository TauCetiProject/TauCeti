/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Topology.Algebra.Star.Unitary
import TauCeti.Topology.Algebra.Star.Unitary
public import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# The unitary group of a finite-dimensional real normed star algebra

The unitary elements of a finite-dimensional real normed star algebra form a smooth real Lie
group. Its topology is the subspace topology, and its atlas comes from the closed unitary
subgroup of the ambient group of units. The inclusion into that group is a smooth immersion.

The model space is the Lie subalgebra of the unitary subgroup of the units. The structure is
independent of any polar-factorization map. For matrices it provides the unitary manifold
factor of the smooth Cartan decomposition.

## Main declarations

* `Unitary.model`: the real vector-space model inherited from the embedded subgroup.
* `Unitary.instNormedAddCommGroupModel`, `Unitary.instNormedSpaceModel`: its inherited normed
  real vector-space structure.
* `Unitary.instChartedSpace`, `Unitary.instIsManifold`, `Unitary.instLieGroup`: the native
  smooth Lie-group structure on unitary elements.
* `Unitary.contMDiff_toUnits`, `Unitary.isImmersion_toUnits`: the inclusion into the units.
* `Unitary.finiteDimensional_model`: the model space is finite-dimensional.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 (closed subgroups) and Proposition 7.11 (embedded Lie subgroups).
-/

public section

open scoped ContDiff Manifold
noncomputable section
namespace Unitary

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]
  [StarRing R] [ContinuousStar R]

private local instance : CompleteSpace R := FiniteDimensional.complete ℝ R

local notation "𝕂" => unitarySubgroup Rˣ
local notation "𝔩" => LieSubalgebra.toSubmodule
  (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, R)) 𝕂)

-- Cache the inherited structures at this subgroup: searching through the ambient derivation
-- space again at concrete matrix algebras exceeds the default typeclass search budget.
/-- The norm on the unitary model is inherited from the ambient Lie algebra. -/
instance instNormedAddCommGroupModel : NormedAddCommGroup 𝔩 := inferInstance

/-- The unitary model is a real normed vector subspace of the ambient Lie algebra. -/
instance instNormedSpaceModel : NormedSpace ℝ 𝔩 := inferInstance

variable (R) in
/-- The vector-space model of the unitary group, inherited from its embedded subgroup of units. -/
abbrev model : ModelWithCorners ℝ 𝔩 𝔩 := 𝓘(ℝ, 𝔩)

open TauCeti.Lie in
/-- The unitary elements have a smooth real Lie-group atlas for their inherited topology,
with an immersive inclusion into the group of units. -/
private theorem exists_nativeStructure :
    ∃ c : ChartedSpace 𝔩 (unitary R),
    let _ := c
    IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R) ∧
    ContMDiff 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞ (Unitary.toUnits : unitary R → Rˣ) ∧
    Manifold.IsImmersion 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞
      (Unitary.toUnits : unitary R → Rˣ) ∧
    LieGroup 𝓘(ℝ, 𝔩) ∞ (unitary R) := by
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := 𝓘(ℝ, R)) (K := 𝕂) (TauCeti.isClosed_unitarySubgroup_units R)
  let _ : ChartedSpace 𝔩 𝕂 := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, 𝔩) ∞ 𝕂 := d.lieGroup
  have hc : Continuous (unitarySubgroupUnitsEquiv : 𝕂 → unitary R) := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, unitarySubgroupUnitsEquiv_apply_coe] using
      (Units.continuous_val.comp (continuous_subtype_val (X := Rˣ)))
  have hc' : Continuous (fun u : unitary R ↦ (unitarySubgroupUnitsEquiv.symm u : Rˣ)) := by
    apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
    simpa only [Function.comp_def, val_unitarySubgroupUnitsEquiv_symm_apply_coe] using
      (continuous_subtype_val (X := R))
  let e : 𝕂 ≃ₜ unitary R :=
    { toEquiv := unitarySubgroupUnitsEquiv.toEquiv
      continuous_toFun := hc
      continuous_invFun := continuous_induced_rng.mpr hc' }
  let c := e.symm.pullbackChartedSpace (H := 𝔩)
  let _ : ChartedSpace 𝔩 (unitary R) := c
  have hm : IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R) :=
    e.symm.pullback_isManifold 𝓘(ℝ, 𝔩) ∞
  let φ := e.symm.pullbackDiffeomorph 𝓘(ℝ, 𝔩) ∞
  let _ : IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R) := hm
  have hphi : (fun u : unitary R ↦ (φ u : Rˣ)) = Unitary.toUnits := by
    funext u
    simp only [φ, Homeomorph.coe_pullbackDiffeomorph, e]
    apply Units.ext
    exact (val_unitarySubgroupUnitsEquiv_symm_apply_coe u).trans (val_toUnits_apply u).symm
  have hinc : ContMDiff 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞
      (Unitary.toUnits : unitary R → Rˣ) :=
    (d.contMDiff_subtypeVal.comp φ.contMDiff).congr fun u ↦ (congrFun hphi u).symm
  have hi0 : Manifold.IsImmersion 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞
      (fun x : 𝕂 ↦ (x : Rˣ)) :=
    d.contMDiff_subtypeVal.isImmersion_of_injective_mfderiv (by simp)
      fun x ↦ d.injective_mfderiv_subtypeVal x
  have hi : Manifold.IsImmersion 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞
      (Unitary.toUnits : unitary R → Rˣ) :=
    (TauCeti.isImmersion_comp_isLocalDiffeomorph φ.isLocalDiffeomorph hi0).congr hphi
  exact ⟨c, hm, hinc, hi, e.symm.pullback_lieGroup 𝓘(ℝ, 𝔩) ∞
    fun u v ↦ unitarySubgroupUnitsEquiv.symm.map_mul u v⟩

/-- The native atlas of the unitary group, induced by its closed embedding into the units. -/
instance instChartedSpace : ChartedSpace 𝔩 (unitary R) :=
  -- Fix the choice predicate explicitly so the private theorem is used only in a proof argument.
  Classical.choose (show ∃ c : ChartedSpace 𝔩 (unitary R),
      let _ := c
      IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R) ∧
      ContMDiff 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞ (Unitary.toUnits : unitary R → Rˣ) ∧
      Manifold.IsImmersion 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞ (Unitary.toUnits : unitary R → Rˣ) ∧
      LieGroup 𝓘(ℝ, 𝔩) ∞ (unitary R) from by
    exact exists_nativeStructure (R := R))

/-- The native unitary atlas is a smooth real manifold structure. -/
instance instIsManifold : IsManifold (model R) ∞ (unitary R) :=
  (Classical.choose_spec
    (exists_nativeStructure (R := R))).1

/-- The inclusion of unitary elements into the units is smooth. -/
theorem contMDiff_toUnits : ContMDiff (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  (Classical.choose_spec
    (exists_nativeStructure (R := R))).2.1

/-- The inclusion of unitary elements into the units is an immersion. -/
theorem isImmersion_toUnits :
    Manifold.IsImmersion (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  (Classical.choose_spec
    (exists_nativeStructure (R := R))).2.2.1

/-- The native unitary manifold has smooth multiplication and inversion. -/
instance instLieGroup : LieGroup (model R) ∞ (unitary R) :=
  (Classical.choose_spec
    (exists_nativeStructure (R := R))).2.2.2

/-- The vector-space model of the unitary group is finite-dimensional. -/
instance finiteDimensional_model : FiniteDimensional ℝ 𝔩 := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, R)) (n := ∞) (by simp) (1 : Rˣ))
  infer_instance

end Unitary
