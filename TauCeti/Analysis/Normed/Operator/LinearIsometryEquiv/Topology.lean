/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# The operator norm topology on linear isometry equivalences

Give linear isometry equivalences the topology induced by their underlying continuous linear
maps. This topology permits comparisons between orthogonal groups and groups of geometric
isometries. The instance is scoped as `TauCeti.LinearIsometryEquivOperatorNorm`.

In finite dimension, continuity of a family is equivalent to continuity at each vector.
For a real or complex Hilbert space the linear isometry group is a topological group:
inversion is the restriction of the continuous adjoint operation.
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
      (fun e : E ≃ₗᵢ[𝕜] F => (e.toContinuousLinearEquiv : E →L[𝕜] F)) := by
  have hinj : Function.Injective
      (fun e : E ≃ₗᵢ[𝕜] F => (e.toContinuousLinearEquiv : E →L[𝕜] F)) :=
    fun _ _ h => LinearIsometryEquiv.ext fun x => DFunLike.congr_fun h x
  exact hinj.isEmbedding_induced

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

end LinearIsometryEquiv

namespace LinearIsometryEquiv

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

open scoped TauCeti.LinearIsometryEquivOperatorNorm

/-- The linear isometry group of a Hilbert space is a topological group in the operator norm
topology. -/
theorem isTopologicalGroup_operatorNorm : IsTopologicalGroup (E ≃ₗᵢ[𝕜] E) where
  continuous_mul := by
    apply continuous_operatorNorm_iff.mpr
    exact ((isEmbedding_toContinuousLinearMap.continuous.comp continuous_fst).clm_comp
      (isEmbedding_toContinuousLinearMap.continuous.comp continuous_snd)).congr fun p => by
        ext x
        simp
  continuous_inv := by
    apply continuous_operatorNorm_iff.mpr
    exact (ContinuousLinearMap.adjoint.continuous.comp
      isEmbedding_toContinuousLinearMap.continuous).congr fun e => by
        exact e.adjoint_eq_symm

scoped[TauCeti.LinearIsometryEquivOperatorNorm] attribute [instance]
  LinearIsometryEquiv.isTopologicalGroup_operatorNorm

end LinearIsometryEquiv
