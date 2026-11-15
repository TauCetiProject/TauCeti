/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# The operator norm topology on linear isometry equivalences

Give linear isometry equivalences the topology induced by their underlying continuous linear
maps. This topology permits comparisons between orthogonal groups and groups of geometric
isometries. The instance is scoped as `TauCeti.LinearIsometryEquivOperatorNorm`.

In finite dimension, continuity of a family is equivalent to continuity at each vector.
The linear isometry group of any normed space is a topological group. The inverses of a jointly
continuous family of linear isometry equivalences are jointly continuous
(`LinearIsometryEquiv.continuous_symm_apply_of_continuous_apply`).
-/

public section

namespace LinearIsometryEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The operator norm topology, induced by the underlying continuous linear map. -/
@[instance_reducible]
def operatorNormTopology : TopologicalSpace (E ≃ₗᵢ[𝕜] F) :=
  .induced (fun e : E ≃ₗᵢ[𝕜] F => (e.toContinuousLinearEquiv : E →L[𝕜] F)) inferInstance

scoped[TauCeti.LinearIsometryEquivOperatorNorm] attribute [instance]
  LinearIsometryEquiv.operatorNormTopology

open scoped TauCeti.LinearIsometryEquivOperatorNorm

/-- Linear isometry equivalences form a subspace of the continuous linear maps. -/
theorem isEmbedding_toContinuousLinearMap :
    Topology.IsEmbedding
      (fun e : E ≃ₗᵢ[𝕜] F => (e.toContinuousLinearEquiv : E →L[𝕜] F)) :=
  Function.Injective.isEmbedding_induced fun _ _ h => ext fun x => DFunLike.congr_fun h x

/-- Continuity of a family of linear isometries can be checked on its operator-valued map. -/
theorem continuous_operatorNorm_iff {X : Type*} [TopologicalSpace X]
    {f : X → E ≃ₗᵢ[𝕜] F} :
    Continuous f ↔ Continuous fun x => (f x).toContinuousLinearEquiv.toContinuousLinearMap :=
  isEmbedding_toContinuousLinearMap.continuous_iff

/-- Joint evaluation of linear isometry equivalences is continuous in the operator norm
topology. -/
theorem continuousEval_operatorNorm : ContinuousEval (E ≃ₗᵢ[𝕜] F) E F where
  continuous_eval := by
    simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      coe_toContinuousLinearEquiv] using
      (isEmbedding_toContinuousLinearMap.continuous.comp continuous_fst).clm_apply continuous_snd

scoped[TauCeti.LinearIsometryEquivOperatorNorm] attribute [instance]
  LinearIsometryEquiv.continuousEval_operatorNorm

/-- The operator norm topology on linear isometry equivalences is Hausdorff. -/
theorem t2Space_operatorNorm : T2Space (E ≃ₗᵢ[𝕜] F) :=
  isEmbedding_toContinuousLinearMap.t2Space

scoped[TauCeti.LinearIsometryEquivOperatorNorm] attribute [instance]
  LinearIsometryEquiv.t2Space_operatorNorm

/-- Over a complete field, continuity of a finite-dimensional family of linear isometries
is equivalent to continuity of its value at every vector. -/
theorem continuous_operatorNorm_iff_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {X : Type*} [TopologicalSpace X] {f : X → E ≃ₗᵢ[𝕜] F} :
    Continuous f ↔ ∀ v, Continuous fun x => f x v := by
  simpa only [ContinuousLinearEquiv.coe_coe, coe_toContinuousLinearEquiv] using
    ((continuous_operatorNorm_iff (f := f)).trans continuous_clm_apply)

/-- The linear isometry group of a normed space is a topological group in the operator norm
topology. -/
theorem isTopologicalGroup_operatorNorm : IsTopologicalGroup (E ≃ₗᵢ[𝕜] E) where
  continuous_mul := by
    apply continuous_operatorNorm_iff.mpr
    exact ((isEmbedding_toContinuousLinearMap.continuous.comp continuous_fst).clm_comp
      (isEmbedding_toContinuousLinearMap.continuous.comp continuous_snd)).congr fun p => by
        ext x
        simp
  continuous_inv := by
    refine continuous_operatorNorm_iff.mpr <| continuous_iff_continuousAt.mpr fun e => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun f => ?_) <|
      tendsto_iff_norm_sub_tendsto_zero.mp (isEmbedding_toContinuousLinearMap.continuous.tendsto e)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    calc _ = ‖((f.toContinuousLinearEquiv : E →L[𝕜] E) - e.toContinuousLinearEquiv) (e⁻¹ v)‖ := by
          rw [← f.norm_map, ← norm_neg]
          -- Keep `e⁻¹` and `f⁻¹` as linear isometries so that `coe_inv` applies.
          simp [-toContinuousLinearEquiv_inv, coe_inv]
      _ ≤ _ := (ContinuousLinearMap.le_opNorm _ _).trans_eq (by simp)

scoped[TauCeti.LinearIsometryEquivOperatorNorm] attribute [instance]
  LinearIsometryEquiv.isTopologicalGroup_operatorNorm

/-- If a family of linear isometry equivalences `f x` between normed spaces is jointly continuous
in the parameter and the vector, then so is the family of their inverses: with
`w = (f x₀)⁻¹ v₀`, `‖(f x)⁻¹ v - w‖ ≤ ‖v - v₀‖ + ‖f x w - f x₀ w‖`. -/
theorem continuous_symm_apply_of_continuous_apply {X : Type*} [TopologicalSpace X]
    {f : X → E ≃ₗᵢ[𝕜] F} (hf : Continuous fun q : X × E => f q.1 q.2) :
    Continuous fun q : X × F => (f q.1).symm q.2 := by
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set w := (f q₀.1).symm q₀.2
  have h₁ := tendsto_iff_norm_sub_tendsto_zero.1 (continuous_snd.tendsto q₀)
  have h₂ := tendsto_iff_norm_sub_tendsto_zero.1
    ((hf.comp (continuous_fst.prodMk (continuous_const (y := w)))).tendsto q₀)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) (by simpa using h₁.add h₂)
  calc ‖(f q.1).symm q.2 - w‖
      ≤ ‖(f q.1).symm q.2 - (f q.1).symm q₀.2‖ + ‖(f q.1).symm q₀.2 - w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖q.2 - q₀.2‖ + ‖f q.1 w - f q₀.1 w‖ := by
        have hw : f q₀.1 w = q₀.2 := apply_symm_apply _ _
        rw [← map_sub, norm_map, hw, ← (f q.1).norm_map ((f q.1).symm q₀.2 - w), map_sub,
          apply_symm_apply, norm_sub_rev q₀.2]

end LinearIsometryEquiv
