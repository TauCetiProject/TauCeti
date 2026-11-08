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
import TauCeti.Geometry.Manifold.Algebra.LieGroup
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
* `Unitary.IsLieGroupAtlas`: the smooth Lie-group and immersive-inclusion properties of an atlas.
* `Unitary.isLieGroupAtlas_instChartedSpace`: these properties for the chosen native atlas.
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

/-- An atlas making the unitary elements a smooth Lie group with a smooth immersive
inclusion into the ambient group of units. -/
structure IsLieGroupAtlas (c : ChartedSpace 𝔩 (unitary R)) : Prop where
  /-- The atlas is a smooth real manifold structure. -/
  isManifold : let _ := c; IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R)
  /-- The inclusion into the units is smooth. -/
  contMDiff_toUnits : let _ := c
    ContMDiff 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞ (Unitary.toUnits : unitary R → Rˣ)
  /-- The inclusion into the units is an immersion. -/
  isImmersion_toUnits : let _ := c
    Manifold.IsImmersion 𝓘(ℝ, 𝔩) 𝓘(ℝ, R) ∞ (Unitary.toUnits : unitary R → Rˣ)
  /-- Multiplication and inversion are smooth. -/
  lieGroup : let _ := c; LieGroup 𝓘(ℝ, 𝔩) ∞ (unitary R)

open TauCeti.Lie in
/-- The unitary elements have a smooth real Lie-group atlas for their inherited topology,
with an immersive inclusion into the group of units. -/
private theorem exists_nativeStructure :
    ∃ c : ChartedSpace 𝔩 (unitary R), IsLieGroupAtlas c := by
  -- Use Cartan charts on the closed unitary subgroup of the units, then transport them
  -- through the canonical homeomorphism. The pullback diffeomorphism transfers the smooth
  -- inclusion and its immersion, while the group isomorphism transfers the Lie-group laws.
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := 𝓘(ℝ, R)) (K := 𝕂) (TauCeti.isClosed_unitarySubgroup_units R)
  let _ : ChartedSpace 𝔩 𝕂 := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, 𝔩) ∞ 𝕂 := d.lieGroup
  let e := TauCeti.unitarySubgroupUnitsHomeomorph R
  let c := e.symm.pullbackChartedSpace (H := 𝔩)
  let _ : ChartedSpace 𝔩 (unitary R) := c
  have hm : IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R) :=
    e.symm.pullback_isManifold 𝓘(ℝ, 𝔩) ∞
  let φ := e.symm.pullbackDiffeomorph 𝓘(ℝ, 𝔩) ∞
  let _ : IsManifold 𝓘(ℝ, 𝔩) ∞ (unitary R) := hm
  have hphi : (fun u : unitary R ↦ (φ u : Rˣ)) = Unitary.toUnits := by
    funext u
    simp only [φ, Homeomorph.coe_pullbackDiffeomorph, e,
      TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply,
      TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply]
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
  refine ⟨c, { isManifold := hm
               contMDiff_toUnits := hinc
               isImmersion_toUnits := hi
               lieGroup := ?_ }⟩
  have hφsymm : (φ.symm : 𝕂 → unitary R) = unitarySubgroupUnitsEquiv := by
    funext u
    simp only [φ, Homeomorph.coe_pullbackDiffeomorph_symm, Homeomorph.symm_symm, e,
      TauCeti.unitarySubgroupUnitsHomeomorph_apply]
  let f : 𝕂 ≃* unitary R := unitarySubgroupUnitsEquiv
  exact IsLocalDiffeomorph.lieGroup f.toMonoidHom
    (hφsymm ▸ φ.symm.isLocalDiffeomorph) f.surjective

/-- The native atlas of the unitary group, induced by its closed embedding into the units. -/
instance instChartedSpace : ChartedSpace 𝔩 (unitary R) :=
  Classical.choose (show ∃ c : ChartedSpace 𝔩 (unitary R), IsLieGroupAtlas c from by
    exact exists_nativeStructure (R := R))

/-- The chosen native unitary atlas has the smooth Lie-group and immersive-inclusion properties. -/
theorem isLieGroupAtlas_instChartedSpace : IsLieGroupAtlas (instChartedSpace (R := R)) :=
  Classical.choose_spec (exists_nativeStructure (R := R))

/-- The native unitary atlas is a smooth real manifold structure. -/
instance instIsManifold : IsManifold (model R) ∞ (unitary R) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).isManifold

/-- The inclusion of unitary elements into the units is smooth. -/
theorem contMDiff_toUnits : ContMDiff (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).contMDiff_toUnits

/-- The inclusion of unitary elements into the units is an immersion. -/
theorem isImmersion_toUnits :
    Manifold.IsImmersion (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).isImmersion_toUnits

/-- The native unitary manifold has smooth multiplication and inversion. -/
instance instLieGroup : LieGroup (model R) ∞ (unitary R) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).lieGroup

/-- The vector-space model of the unitary group is finite-dimensional. -/
instance finiteDimensional_model : FiniteDimensional ℝ 𝔩 := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, R)) (n := ∞) (by simp) (1 : Rˣ))
  infer_instance

end Unitary
