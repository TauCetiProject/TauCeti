/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Regularity of the Hilbert–Schmidt pairing of vector-valued one-forms

For a Riemannian manifold `M` and a Riemannian vector bundle `V` over it, the pointwise
Hilbert–Schmidt inner product `⟪A, B⟫ = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of two sections `A`, `B` of the bundle
`Hom(TM, V)` of `V`-valued one-forms, for any orthonormal basis `eᵢ` of the tangent space, is as
regular as `A` and `B`. In a chart it is read off with the inverse Gram matrix of the chart frame.

## Main results

* `ContMDiffAt.hilbertSchmidtInner_bundle`: the pairing of two `V`-valued one-forms that are `C^n`
  at a point is `C^n` at that point.
* `ContMDiff.hilbertSchmidtInner_bundle`: the pairing of two `C^n` `V`-valued one-forms is `C^n`.
-/

public section

open Bundle FiberBundle Riemannian.Tensor
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle I n F V]
  {A B : Π x : M, TangentSpace I x →L[ℝ] V x}

/-- The pointwise Hilbert–Schmidt inner product `⟪A, B⟫ = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of two sections `A`,
`B` of the bundle `Hom(TM, V)` of `V`-valued one-forms that are `C^n` at `x`, for any orthonormal
basis `eᵢ` of the tangent space, is `C^n` at `x`. -/
theorem ContMDiffAt.hilbertSchmidtInner_bundle {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (A y)) x)
    (hB : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (B y)) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ (A y).hilbertSchmidtInner (B y)) x := by
  have hbase : (trivializationAt E (TangentSpace I) x).baseSet ∈ 𝓝 x :=
    (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds (by simp)
  have hframe (j) : CMDiffAt n (T% (chartLocalFrame (I := I) x j)) x :=
    contMDiffAt_chartLocalFrame (I := I) (n := n) x j
  -- On the chart source, the metric trace is read off with the inverse Gram matrix.
  have heq : (fun y ↦ ∑ i, ∑ j, chartInvGramMatrix (I := I) x y i j *
      ⟪A y (chartLocalFrame (I := I) x i y), B y (chartLocalFrame (I := I) x j y)⟫)
      =ᶠ[𝓝 x] fun y ↦ (A y).hilbertSchmidtInner (B y) := by
    filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
    simp only [ContinuousLinearMap.hilbertSchmidtInner_def,
      metricTrace_eq_sum_chartInvGramMatrix x hy, LinearMap.compl₁₂_apply, innerₗ_apply_apply,
      ContinuousLinearMap.coe_coe, smul_eq_mul]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq.symm
  refine contMDiffAt_finsetSum fun i _ ↦ contMDiffAt_finsetSum fun j _ ↦ ?_
  exact ((contMDiffOn_chartInvGramMatrix_entry (I := I) (n := n) x i j).contMDiffAt hbase).mul
    ((hA.clm_bundle_apply (hframe i)).inner_bundle (hB.clm_bundle_apply (hframe j)))

/-- The pointwise Hilbert–Schmidt inner product `⟪A, B⟫ = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of two `C^n` sections
`A`, `B` of the bundle `Hom(TM, V)` of `V`-valued one-forms, for any orthonormal basis `eᵢ` of the
tangent space, is a `C^n` function. -/
theorem ContMDiff.hilbertSchmidtInner_bundle
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (A x)))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (B x))) :
    ContMDiff I 𝓘(ℝ) n fun x ↦ (A x).hilbertSchmidtInner (B x) :=
  fun x ↦ (hA x).hilbertSchmidtInner_bundle (hB x)
