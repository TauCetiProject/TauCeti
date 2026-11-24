/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.RankOne
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace

/-!
# Induced Hom connections of metric connections

For connections on bundles `V` and `W`, this module records consequences of metric
compatibility for the induced connection on `Hom(V, W)`.

* If the connection on the Riemannian bundle `W` is metric and the sections `σ` of `W` and `τ`
  of `V` are parallel at `x`, then the matrix entry `⟪σ, (∇_v A) τ⟫` at `x` is the ordinary
  derivative of `y ↦ ⟪σ y, A y (τ y)⟫`
  (`CovariantDerivative.IsMetricCompatible.inner_hom_apply_eq_mvfderiv_inner`).
* If the connection on the Riemannian bundle `W` is metric, then covariant differentiation
  preserves skew-adjointness of differentiable endomorphism sections
  (`CovariantDerivative.IsMetricCompatible.inner_hom_eq_neg`) and of differentiable bilinear
  sections `V →L[ℝ] W →L[ℝ] W` skew-adjoint in their last two slots
  (`CovariantDerivative.IsMetricCompatible.inner_hom_hom_eq_neg`).
* If the connection on the Riemannian bundle `V` is metric, then the rank-one homomorphisms
  `v ↦ ⟪τ, v⟫ • σ` satisfy the Leibniz rule
  `∇(rankOne σ τ) = rankOne (∇σ) τ + rankOne σ (∇τ)`
  (`CovariantDerivative.IsMetricCompatible.hom_rankOne_apply`).
  In particular they are parallel wherever `σ` and `τ` are.
* If the connections on the tangent bundle of a Riemannian manifold and on the Riemannian bundle
  `V` are metric, then the Hilbert–Schmidt pairing `⟪A, B⟫ = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of sections of
  `Hom(TM, V)` is parallel for the induced connection:
  `d⟪A, B⟫(v) = ⟪∇_v A, B⟫ + ⟪A, ∇_v B⟫`
  (`CovariantDerivative.IsMetricCompatible.mvfderiv_hilbertSchmidtInner`). In the chart frame `Fᵢ`
  and its metric-dual frame `Dᵢ`, `⟪A, B⟫ = ∑ᵢ ⟪A Fᵢ, B Dᵢ⟫` near the point, and the terms
  carrying `∇Fᵢ` and `∇Dᵢ` cancel
  (`CovariantDerivative.IsMetricCompatible.sum_apply_chartDualFrame_cancel`).

The first three items are the comparisons for the frames induced on `Hom(V, W)` by frames
parallel at a point; the last uses the chart frame and its metric-dual frame instead. The module
follows J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4–5.
-/

public section

open Bundle FiberBundle InnerProductSpace
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section Endomorphism

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle 1 G W I]
  [IsContMDiffRiemannianBundle I 1 G W]
  {covW : CovariantDerivative I G W}

/-- Skew-adjointness of a differentiable endomorphism section near `x` passes to its covariant
derivative under the induced Hom connection of a metric-compatible connection. -/
theorem IsMetricCompatible.inner_hom_eq_neg (hcov : covW.IsMetricCompatible)
    {A : Π x : M, W x →L[ℝ] W x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (G →L[ℝ] G) (E := fun z ↦ W z →L[ℝ] W z) y (A y)) x)
    (hskew : ∀ᶠ y in 𝓝 x, ∀ a b, ⟪A y a, b⟫_ℝ = -⟪a, A y b⟫_ℝ)
    (v : TangentSpace I x) (a b : W x) :
    ⟪covW.hom covW A x v a, b⟫_ℝ = -⟪a, covW.hom covW A x v b⟫_ℝ := by
  have hσ := mdifferentiableAt_extend I G a
  have hτ := mdifferentiableAt_extend I G b
  have hAσ := hA.clm_bundle_apply hσ
  have hAτ := hA.clm_bundle_apply hτ
  have hzero : (fun y ↦ ⟪A y (extend G a y), extend G b y⟫_ℝ +
      ⟪extend G a y, A y (extend G b y)⟫_ℝ) =ᶠ[𝓝 x] fun _ ↦ 0 :=
    hskew.mono fun y hy ↦ by dsimp only; rw [hy, neg_add_cancel]
  have hd : mvfderiv I (fun y ↦ ⟪A y (extend G a y), extend G b y⟫_ℝ +
      ⟪extend G a y, A y (extend G b y)⟫_ℝ) x v = 0 := by
    rw [hzero.mvfderiv_eq, mvfderiv_const, zero_apply]
  rw [mvfderiv_fun_add (hAσ.inner_bundle hτ) (hσ.inner_bundle hAτ), add_apply,
    hcov.mvfderiv_inner_eq (fun _ ↦ v) hAσ hτ,
    hcov.mvfderiv_inner_eq (fun _ ↦ v) hσ hAτ] at hd
  have hevA := hom_apply_eq_extend covW covW hA v a
  have hevB := hom_apply_eq_extend covW covW hA v b
  have hskewx := hskew.self_of_nhds
  simp only [extend_apply_self, hskewx] at hd hevA hevB
  rw [hevA, hevB]
  simp only [inner_sub_left, inner_sub_right, hskewx]
  linarith

end Endomorphism

section InnerTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle 1 G W I]
  [IsContMDiffRiemannianBundle I 1 G W]
  {covV : CovariantDerivative I F V} {covW : CovariantDerivative I G W}

/-- For a metric connection on the target, the matrix entries of the induced Hom connection
against sections parallel at `x` are the ordinary derivatives of the matrix entries. -/
theorem IsMetricCompatible.inner_hom_apply_eq_mvfderiv_inner (hcov : covW.IsMetricCompatible)
    {A : Π x : M, V x →L[ℝ] W x} {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun z ↦ V z →L[ℝ] W z) y (A y)) x)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (hσ₀ : covW σ x = 0) (hτ₀ : covV τ x = 0) (v : TangentSpace I x) :
    ⟪σ x, covV.hom covW A x v (τ x)⟫_ℝ =
      mvfderiv I (fun y ↦ ⟪σ y, A y (τ y)⟫_ℝ) x v := by
  have hp := hcov.mvfderiv_inner_eq (fun _ ↦ v) hσ (hA.clm_bundle_apply hτ)
  simp only [hσ₀, zero_apply, inner_zero_left, zero_add] at hp
  rw [hom_apply covV covW hA hτ, hτ₀, zero_apply, map_zero, sub_zero]
  exact hp.symm

/-- Skew-adjointness of a differentiable bilinear bundle section in its last two slots near `x`
passes to its covariant derivative under the iterated induced Hom connection when the target
connection is metric-compatible. The connection on the first slot is arbitrary. -/
theorem IsMetricCompatible.inner_hom_hom_eq_neg (hcov : covW.IsMetricCompatible)
    {S : Π x : M, V x →L[ℝ] W x →L[ℝ] W x} {x : M}
    (hS : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] G →L[ℝ] G)
        (E := fun z ↦ V z →L[ℝ] W z →L[ℝ] W z) y (S y)) x)
    (hskew : ∀ᶠ y in 𝓝 x, ∀ u a b, ⟪S y u a, b⟫_ℝ = -⟪a, S y u b⟫_ℝ)
    (v : TangentSpace I x) (u : V x) (a b : W x) :
    ⟪covV.hom (covW.hom covW) S x v u a, b⟫_ℝ =
      -⟪a, covV.hom (covW.hom covW) S x v u b⟫_ℝ := by
  have hU := mdifferentiableAt_extend I F u
  rw [hom_apply_eq_extend covV (covW.hom covW) hS v u, sub_apply, sub_apply,
    inner_sub_left, inner_sub_right,
    hcov.inner_hom_eq_neg (hS.clm_bundle_apply hU) (hskew.mono fun y hy ↦ hy (extend F u y)),
    hskew.self_of_nhds]
  ring

end InnerTarget

section RankOne

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [targetNorm : ∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W]
  {covV : CovariantDerivative I F V} {covW : CovariantDerivative I G W}

/-- For a metric connection on the source, the induced Hom connection satisfies the Leibniz
rule on rank-one homomorphisms `v ↦ ⟪τ, v⟫ • σ` formed from `C¹` sections. -/
theorem IsMetricCompatible.hom_rankOne_apply (hcov : covV.IsMetricCompatible)
    {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}
    (hσ : CMDiffAt 1 (T% σ) x) (hτ : CMDiffAt 1 (T% τ) x) (v : TangentSpace I x) :
    covV.hom covW (fun y ↦ rankOne ℝ (σ y) (τ y)) x v =
      rankOne ℝ (covW σ x v) (τ x) + rankOne ℝ (σ x) (covV τ x v) := by
  have hA := (hσ.rankOne_bundle hτ).mdifferentiableAt one_ne_zero
  have hσ' := hσ.mdifferentiableAt one_ne_zero
  have hτ' := hτ.mdifferentiableAt one_ne_zero
  ext u
  have hs : MDiffAt (T% (extend F u)) x := mdifferentiableAt_extend I F u
  have hfun : (fun y ↦ rankOne ℝ (σ y) (τ y) (extend F u y)) =
      (fun y ↦ ⟪τ y, extend F u y⟫_ℝ) • σ := by
    ext y
    simp
  have hp := hcov.mvfderiv_inner_eq (fun _ ↦ v) hτ' hs
  rw [hom_apply_eq_extend covV covW hA, hfun,
    covW.isCovariantDerivativeOnUniv.leibniz hσ' (hτ'.inner_bundle hs)]
  simp only [extend_apply_self] at hp
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    extend_apply_self, rankOne_apply, hp]
  module

/-- Rank-one homomorphisms formed from `C¹` sections parallel at `x` are parallel at `x` for
the induced Hom connection of a metric connection on the source. -/
theorem IsMetricCompatible.hom_rankOne_eq_zero (hcov : covV.IsMetricCompatible)
    {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}
    (hσ : CMDiffAt 1 (T% σ) x) (hτ : CMDiffAt 1 (T% τ) x)
    (hσ₀ : covW σ x = 0) (hτ₀ : covV τ x = 0) :
    covV.hom covW (fun y ↦ rankOne ℝ (σ y) (τ y)) x = 0 := by
  ext v : 1
  simp [hcov.hom_rankOne_apply hσ hτ, hσ₀, hτ₀]

end RankOne

section HilbertSchmidt

open Riemannian.Tensor
open scoped RealInnerProductSpace

variable [IsManifold I 2 M] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V}
  {covT : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- **The Hilbert–Schmidt metric is parallel.** For metric connections `∇ᵀ` on the tangent bundle
and `∇` on `V`, and sections `A`, `B` of `Hom(TM, V)` differentiable at `x`, the derivative of their
Hilbert–Schmidt pairing is `d⟪A, B⟫(v) = ⟪∇_v A, B⟫ + ⟪A, ∇_v B⟫`, for the connection on
`Hom(TM, V)` induced by `∇ᵀ` and `∇`. -/
theorem IsMetricCompatible.mvfderiv_hilbertSchmidtInner
    (hcovT : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) covT)
    (hcov : cov.IsMetricCompatible) {A B : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (A y)) x)
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (B y)) x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ (A y).hilbertSchmidtInner (B y)) x v =
      (covT.hom cov A x v).hilbertSchmidtInner (B x) +
        (A x).hilbertSchmidtInner (covT.hom cov B x v) := by
  have hxb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hxc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hF := mdifferentiableAt_chartLocalFrame (I := I) x hxb
  have hD := mdifferentiableAt_chartDualFrame (I := I) x hxb
  -- Near `x`, the pairing is `∑ᵢ ⟪A Fᵢ, B Dᵢ⟫` in the chart frame `Fᵢ` and its metric-dual frame
  -- `Dᵢ`.
  have htr : (fun y ↦ (A y).hilbertSchmidtInner (B y)) =ᶠ[𝓝 x] fun y ↦
      ∑ i, ⟪A y (chartLocalFrame (I := I) x i y), B y (chartDualFrame (I := I) x i y)⟫ :=
    (eventually_metricTrace_eq_sum_chartDualFrame x hxc
      fun y ↦ (innerₗ (V y)).compl₁₂ (A y : TangentSpace I y →ₗ[ℝ] V y)
        (B y : TangentSpace I y →ₗ[ℝ] V y)).mono fun y hy ↦ by
      simpa only [ContinuousLinearMap.hilbertSchmidtInner_def, LinearMap.compl₁₂_apply,
        innerₗ_apply_apply, ContinuousLinearMap.coe_coe] using hy
  have hAF (i) : MDiffAt (T% fun y ↦ A y (chartLocalFrame (I := I) x i y)) x :=
    hA.clm_bundle_apply (hF i)
  have hBD (i) : MDiffAt (T% fun y ↦ B y (chartDualFrame (I := I) x i y)) x :=
    hB.clm_bundle_apply (hD i)
  -- Differentiate each term with the metric and the Leibniz rule for `Hom(TM, V)`; the terms
  -- carrying `∇Fᵢ` and `∇Dᵢ` cancel in the sum, since the metric is parallel.
  have hterm (i) : mvfderiv I (fun y ↦
      ⟪A y (chartLocalFrame (I := I) x i y), B y (chartDualFrame (I := I) x i y)⟫) x v =
      ⟪covT.hom cov A x v (chartLocalFrame (I := I) x i x), B x (chartDualFrame (I := I) x i x)⟫ +
        ⟪A x (chartLocalFrame (I := I) x i x), covT.hom cov B x v (chartDualFrame (I := I) x i x)⟫ +
        (⟪A x (covT (chartLocalFrame (I := I) x i) x v), B x (chartDualFrame (I := I) x i x)⟫ +
          ⟪A x (chartLocalFrame (I := I) x i x),
            B x (covT (chartDualFrame (I := I) x i) x v)⟫) := by
    have h := hcov.mvfderiv_inner_eq (FiberBundle.extend E v) (hAF i) (hBD i)
    simp only [FiberBundle.extend_apply_self] at h
    rw [h, covariantDerivative_clm_apply covT cov hA (hF i),
      covariantDerivative_clm_apply covT cov hB (hD i), inner_add_left, inner_add_right]
    ring
  have hcancel := hcovT.sum_apply_chartDualFrame_cancel x
    ((innerₗ (V x)).compl₁₂ (A x : TangentSpace I x →ₗ[ℝ] V x)
      (B x : TangentSpace I x →ₗ[ℝ] V x)) v
  simp only [LinearMap.compl₁₂_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe] at hcancel
  rw [htr.mvfderiv_eq, TauCeti.mvfderiv_fun_sum fun i _ ↦ (hAF i).inner_bundle (hBD i), sum_apply]
  simp only [hterm, Finset.sum_add_distrib, hcancel, add_neg_cancel, add_zero,
    ContinuousLinearMap.hilbertSchmidtInner_def, metricTrace_eq_sum_chartDualFrame x hxc,
    LinearMap.compl₁₂_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe]

end HilbertSchmidt

end CovariantDerivative
