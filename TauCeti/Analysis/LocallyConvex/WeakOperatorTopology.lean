/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.LocallyConvex.PointwiseConvergence
public import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Comparing the strong and weak operator topologies

The identity from the pointwise-convergence copy of continuous linear maps to the weak
operator copy is continuous. Centralizers of sets of operators are weak-operator closed.
These facts allow strong approximation results to identify weak operator closures without
changing the norm topology on the original operator space.

The two topologies have the same continuous linear functionals: every functional continuous for
pointwise convergence is a finite sum `T ↦ ∑ x ∈ s, g x (T x)` of continuous functionals of
values (`PointwiseConvergenceCLM.exists_finset_sum_eq`, in
`TauCeti.Analysis.LocallyConvex.PointwiseConvergence`), hence weak-operator continuous, and
conversely (`ContinuousLinearMapWOT.exists_finset_sum_eq`). On a Hilbert space, writing each
`g x` as an inner product gives the usual finite sums of matrix coefficients. By locally convex
separation, a convex set of operators therefore has the same closure in both topologies
(`Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`).

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.1.2 and
Corollary 5.1.3.
-/

public section

open scoped Topology

namespace ContinuousLinearMapWOT

variable {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F]

/-- Pointwise (strong operator) convergence is stronger than weak operator convergence. -/
@[fun_prop]
theorem continuous_ofPointwiseConvergenceCLM :
    Continuous (fun T : E →SLₚₜ[σ] F => ofCLM (T : E →SL[σ] F)) := by
  apply continuous_of_dual_apply_continuous
  intro x y
  exact y.continuous.comp (continuous_eval_const x)

end ContinuousLinearMapWOT

namespace Set

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
    [SeparatingDual 𝕜 E]

/-- The commutant of any set of operators is closed in the weak operator topology. -/
theorem isClosed_image_ofCLM_centralizer (s : Set (E →L[𝕜] E)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' s.centralizer) := by
  have h : ContinuousLinearMapWOT.ofCLM '' s.centralizer =
      (ContinuousLinearMapWOT.ofCLM '' s).centralizer := by
    ext T
    obtain ⟨T, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective T
    rw [ContinuousLinearMapWOT.ofCLM_injective.mem_set_image]
    simp only [mem_centralizer_iff, forall_mem_image,
      ← ContinuousLinearMapWOT.ofCLM_mul, ContinuousLinearMapWOT.ofCLM_injective.eq_iff]
  rw [h]
  exact isClosed_centralizer _

end Set

namespace ContinuousLinearMapWOT

variable {𝕜₁ 𝕜 E F : Type*} [NormedField 𝕜₁] [RCLike 𝕜] {σ : 𝕜₁ →+* 𝕜} [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]

/-- A linear functional on operators which is continuous for the topology of pointwise
convergence is continuous for the weak operator topology. -/
theorem continuous_strongDual_apply_toPointwiseConvergenceCLM
    (φ : StrongDual 𝕜 (E →SLₚₜ[σ] F)) :
    Continuous fun A : E →SWOT[σ] F ↦
      φ (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F A.toCLM) := by
  obtain ⟨s, g, hg⟩ := PointwiseConvergenceCLM.exists_finset_sum_eq φ
  simp only [hg]
  exact continuous_finsetSum _ fun x _ ↦ continuous_dual_apply x (g x)

/-- **Continuous functionals in the weak operator topology.** A linear functional on operators
which is continuous for the weak operator topology is a finite sum of functionals
`A ↦ g x (A x)`. -/
theorem exists_finset_sum_eq (φ : StrongDual 𝕜 (E →SWOT[σ] F)) :
    ∃ (s : Finset E) (g : E → StrongDual 𝕜 F), ∀ A : E →SWOT[σ] F,
      φ A = ∑ x ∈ s, g x (A x) := by
  -- Precompose `φ` with the continuous identity map from the strong to the weak operator topology.
  obtain ⟨s, g, hg⟩ := PointwiseConvergenceCLM.exists_finset_sum_eq
    (φ.comp ⟨(linearEquiv 𝕜).symm.toLinearMap ∘ₗ
      (ContinuousLinearMap.toUniformConvergenceCLM _ F _).symm.toLinearMap,
      continuous_ofPointwiseConvergenceCLM⟩)
  -- The composite is `φ` itself on underlying operators.
  exact ⟨s, g, fun A ↦ hg (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F A.toCLM)⟩

variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- For a convex set of operators, the closures in the topology of pointwise convergence (the
strong operator topology) and in the weak operator topology contain the same operators. -/
theorem _root_.Convex.toPointwiseConvergenceCLM_mem_closure_image_iff {s : Set (E →SL[σ] F)}
    (hs : Convex ℝ s) {T : E →SL[σ] F} :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F T ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F '' s) ↔
      ofCLM T ∈ closure (ofCLM '' s) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 σ E F
  refine ⟨fun h ↦ map_mem_closure (f := fun A : E →SLₚₜ[σ] F ↦ ofCLM (A : E →SL[σ] F))
    continuous_ofPointwiseConvergenceCLM h ?_, fun h ↦ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · -- `e` is the identity on underlying operators, from the weak to the strong operator copy.
    let e : (E →SWOT[σ] F) →ₗ[𝕜] (E →SLₚₜ[σ] F) := q.toLinearMap ∘ₗ (linearEquiv 𝕜).toLinearMap
    have he (a : E →SL[σ] F) : e (ofCLM a) = q a := rfl
    have hconv : Convex ℝ (ofCLM '' s) := hs.linear_image (linearEquiv ℝ).symm.toLinearMap
    have himage : e '' (ofCLM '' s) = q '' s := by
      simp only [Set.image_image, he]
    exact himage ▸ he T ▸ e.image_closure_of_convex hconv
      (fun f ↦ continuous_strongDual_apply_toPointwiseConvergenceCLM f) ⟨_, h, rfl⟩

end ContinuousLinearMapWOT
