/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Transport
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Topology.Algebra.Star.Unitary
import TauCeti.Topology.Algebra.Star.Unitary
public import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Topology.Algebra.Star.RealModule

/-!
# The unitary group of a finite-dimensional real normed star algebra

The unitary elements of a finite-dimensional real normed star algebra form a smooth real Lie
group. Its topology is the subspace topology, and its atlas comes from the closed unitary
subgroup of the ambient group of units. The inclusions into that group and into the ambient
algebra are smooth embeddings, so smoothness of maps into `unitary R` can be checked after
coercing to `R`, and any smooth action of `R` restricts to a smooth action of `unitary R`.

The model space is the Lie subalgebra of the unitary subgroup of the units. The structure is
independent of any polar-factorization map. For matrices it provides the unitary manifold
factor of the smooth Cartan decomposition.

## Main declarations

* `Unitary.model`: the real vector-space model inherited from the embedded subgroup.
* `Unitary.instNormedAddCommGroupModel`, `Unitary.instNormedSpaceModel`: its inherited normed
  real vector-space structure.
* `Unitary.isLieGroupAtlas_instChartedSpace`: the chosen native atlas makes the unitary elements a
  smooth Lie group with an immersive inclusion into the units (`TauCeti.Lie.IsLieGroupAtlas`).
* `Unitary.instChartedSpace`, `Unitary.instIsManifold`, `Unitary.instLieGroup`: the native
  smooth Lie-group structure on unitary elements.
* `Unitary.contMDiff_toUnits`, `Unitary.isImmersion_toUnits`,
  `Unitary.isSmoothEmbedding_toUnits`: the inclusion into the units.
* `Unitary.contMDiff_val`, `Unitary.isImmersion_val`, `Unitary.isSmoothEmbedding_val`: the
  inclusion into the ambient normed star algebra.
* `Unitary.contMDiffWithinAt_iff`, `Unitary.contMDiffAt_iff`, `Unitary.contMDiffOn_iff`,
  `Unitary.contMDiff_iff`: smoothness of maps into `unitary R` tested after coercion to `R`.
* `Unitary.instContMDiffSMul`: restriction of a `C^n` action (`n ≤ ∞`) of `R` on a manifold to
  `unitary R`.
* `Unitary.finiteDimensional_model`: the model space is finite-dimensional.
* `Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint`: the differential of the inclusion
  into `R` at the identity takes values in the skew-adjoint elements.

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

private local instance : CompleteSpace R := FiniteDimensional.completeSpace ℝ R

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

/-- The unitary elements have a smooth real Lie-group atlas for their inherited topology,
with an immersive inclusion into the group of units. -/
private theorem exists_nativeStructure :
    ∃ c : ChartedSpace 𝔩 (unitary R),
      TauCeti.Lie.IsLieGroupAtlas 𝓘(ℝ, R) (Unitary.toUnits : unitary R → Rˣ) c :=
  -- Transport the closed-subgroup structure of the unitary subgroup of the units along the
  -- canonical topological group isomorphism.
  TauCeti.Lie.exists_isLieGroupAtlas_of_isClosed (TauCeti.isClosed_unitarySubgroup_units R)
    (ContinuousMulEquiv.mk' (TauCeti.unitarySubgroupUnitsHomeomorph R).symm fun x y ↦ by
      simpa only [TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply] using
        map_mul unitarySubgroupUnitsEquiv.symm x y)
    fun u ↦ by
      simp only [ContinuousMulEquiv.coe_mk', TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply,
        TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply]

/-- The native atlas of the unitary group, induced by its closed embedding into the units. -/
instance instChartedSpace : ChartedSpace 𝔩 (unitary R) :=
  -- The instance body is exposed and may not name the private `exists_nativeStructure`; the
  -- `by exact` moves that reference into an auxiliary proof of the restated proposition.
  Classical.choose (show ∃ c : ChartedSpace 𝔩 (unitary R),
      TauCeti.Lie.IsLieGroupAtlas 𝓘(ℝ, R) (Unitary.toUnits : unitary R → Rˣ) c from by
    exact exists_nativeStructure (R := R))

/-- The chosen native unitary atlas has the smooth Lie-group and immersive-inclusion properties. -/
theorem isLieGroupAtlas_instChartedSpace :
    TauCeti.Lie.IsLieGroupAtlas 𝓘(ℝ, R) (toUnits : unitary R → Rˣ) (instChartedSpace (R := R)) :=
  Classical.choose_spec (exists_nativeStructure (R := R))

/-- The native unitary atlas is a smooth real manifold structure. -/
instance instIsManifold : IsManifold (model R) ∞ (unitary R) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).isManifold

/-- The inclusion of unitary elements into the units is smooth. -/
theorem contMDiff_toUnits : ContMDiff (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).contMDiff

/-- The inclusion of unitary elements into the units is an immersion. -/
theorem isImmersion_toUnits :
    Manifold.IsImmersion (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).isImmersion

/-- The inclusion of unitary elements into the units is a smooth embedding. -/
theorem isSmoothEmbedding_toUnits :
    Manifold.IsSmoothEmbedding (model R) 𝓘(ℝ, R) ∞ (toUnits : unitary R → Rˣ) :=
  ⟨isImmersion_toUnits,
    Topology.IsEmbedding.of_comp continuous_toUnits Units.continuous_val .subtypeVal⟩

/-- The coercion of unitary elements into the ambient algebra is smooth. -/
theorem contMDiff_val : ContMDiff (model R) 𝓘(ℝ, R) ∞ (Subtype.val : unitary R → R) :=
  Units.contMDiff_val.comp contMDiff_toUnits

/-- The coercion of unitary elements into the ambient algebra is an immersion. -/
theorem isImmersion_val :
    Manifold.IsImmersion (model R) 𝓘(ℝ, R) ∞ (Subtype.val : unitary R → R) :=
  Units.isImmersion_val_comp isImmersion_toUnits

/-- The coercion of unitary elements into the ambient algebra is a smooth embedding. -/
theorem isSmoothEmbedding_val :
    Manifold.IsSmoothEmbedding (model R) 𝓘(ℝ, R) ∞ (Subtype.val : unitary R → R) :=
  ⟨isImmersion_val, .subtypeVal⟩

section SmoothnessIff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [ENat.LEInfty n] {f : M → unitary R} {s : Set M} {x : M}

/-- A map into `unitary R` is `C^n` within a set at a point if and only if its coercion to `R` is.
The `ENat.LEInfty n` hypothesis excludes real-analytic regularity `ω`, as the native unitary atlas
is `C^∞`. -/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I (model R) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, R) n (fun y ↦ (f y : R)) s x :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiffWithinAt_iff_comp

/-- A map into `unitary R` is `C^n` at a point if and only if its coercion to `R` is. -/
theorem contMDiffAt_iff :
    ContMDiffAt I (model R) n f x ↔ ContMDiffAt I 𝓘(ℝ, R) n (fun y ↦ (f y : R)) x :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiffAt_iff_comp

/-- A map into `unitary R` is `C^n` on a set if and only if its coercion to `R` is. -/
theorem contMDiffOn_iff :
    ContMDiffOn I (model R) n f s ↔ ContMDiffOn I 𝓘(ℝ, R) n (fun y ↦ (f y : R)) s :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiffOn_iff_comp

/-- A map into `unitary R` is `C^n` if and only if its coercion to `R` is. -/
theorem contMDiff_iff :
    ContMDiff I (model R) n f ↔ ContMDiff I 𝓘(ℝ, R) n (fun y ↦ (f y : R)) :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiff_iff_comp

end SmoothnessIff

/-- The native unitary manifold has smooth multiplication and inversion. -/
instance instLieGroup : LieGroup (model R) ∞ (unitary R) :=
  (isLieGroupAtlas_instChartedSpace (R := R)).lieGroup

/-- Any `C^n` action (`n ≤ ∞`) of the ambient algebra `R` on a manifold restricts to a `C^n` action
of `unitary R`. -/
instance instContMDiffSMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞ω} [ENat.LEInfty n]
    [MulAction R M] [ContMDiffSMul 𝓘(ℝ, R) I n R M] :
    ContMDiffSMul (model R) I n (unitary R) M :=
  MulAction.contMDiffSMul_compHom (f := (unitary R).subtype)
    (contMDiff_val.of_le ENat.LEInfty.out)

/-- The vector-space model of the unitary group is finite-dimensional. -/
instance finiteDimensional_model : FiniteDimensional ℝ 𝔩 := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, R)) (n := ∞) (by simp) (1 : Rˣ))
  infer_instance

/-- **The Lie algebra of the unitary group consists of skew-adjoint elements.** The differential
at the identity of the inclusion `unitary R → R` takes values in `skewAdjoint R`: differentiating
`star u * u = 1` at `u = 1` gives `star X + X = 0`. -/
theorem tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint
    (ξ : GroupLieAlgebra (model R) (unitary R)) :
    tangentSpaceCastModel 𝓘(ℝ, R) (1 : R) (mfderiv (model R) 𝓘(ℝ, R) Subtype.val 1 ξ) ∈
      skewAdjoint R := by
  -- A continuous additive involution is real-linear, so `star` is a continuous linear map.
  have : StarModule ℝ R := ContinuousStar.starModule_real
  have hF := (starL' ℝ : R ≃L[ℝ] R).hasFDerivAt.mul' (hasFDerivAt_id (1 : R))
  have hconst : (⇑(starL' ℝ : R ≃L[ℝ] R) * id) ∘ (Subtype.val : unitary R → R) = fun _ ↦ 1 :=
    funext fun u ↦ by simp
  -- The chain rule computes the derivative of the constant map `u ↦ star u * u` at `1`.
  have h := hF.hasMFDerivAt.comp (1 : unitary R)
    (contMDiff_val.mdifferentiableAt (by simp)).hasMFDerivAt
  rw [hconst] at h
  have key := congrArg (fun L ↦ L ξ)
    ((hasMFDerivAt_const (1 : R) (1 : unitary R)).mfderiv.symm.trans h.mfderiv)
  rw [skewAdjoint.mem_iff, eq_neg_iff_add_eq_zero]
  simp only [zero_apply, starL'_apply, star_one, id_eq, MulOpposite.op_one, one_smul] at key
  -- `key` reads `X + star X = 0` for `X = dval₁(ξ)`, up to the identity casts of tangent spaces.
  exact (add_comm _ _).trans key.symm

end Unitary
