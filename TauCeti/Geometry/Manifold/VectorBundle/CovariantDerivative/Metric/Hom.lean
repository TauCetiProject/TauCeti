/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.RankOne

/-!
# Induced Hom connections of metric connections

For connections on bundles `V` and `W`, this module records two consequences of metric
compatibility for the induced connection on `Hom(V, W)`.

* If the connection on the Riemannian bundle `W` is metric and the sections `σ` of `W` and `τ`
  of `V` are parallel at `x`, then the matrix entry `⟪σ, (∇_v A) τ⟫` at `x` is the ordinary
  derivative of `y ↦ ⟪σ y, A y (τ y)⟫`
  (`CovariantDerivative.IsMetricCompatible.inner_hom_apply_eq_mvfderiv_inner`).
* If the connection on the Riemannian bundle `V` is metric, then the rank-one homomorphisms
  `v ↦ ⟪τ, v⟫ • σ` satisfy the Leibniz rule
  `∇(rankOne σ τ) = rankOne (∇σ) τ + rankOne σ (∇τ)`
  (`CovariantDerivative.IsMetricCompatible.hom_rankOne_apply`).
  In particular they are parallel wherever `σ` and `τ` are.

These are the comparisons for the frames induced on `Hom(V, W)` by frames parallel at a point,
following J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4–5.
-/

public section

open Bundle FiberBundle InnerProductSpace
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

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

end CovariantDerivative
