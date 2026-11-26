/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Composition
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Second covariant derivatives of composed bundle maps

The second covariant derivative of a composition is the sum of two pure second-derivative
terms and two mixed first-derivative terms. The tangent connection is arbitrary, and no metric
on any bundle is needed. This product rule allows scalar contraction identities to be applied
to compositions without repeating their second-order differentiation.
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W I]
  {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  {U : M → Type*} [TopologicalSpace (TotalSpace K U)]
  [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)]
  [∀ x, TopologicalSpace (U x)] [∀ x, IsTopologicalAddGroup (U x)]
  [∀ x, ContinuousSMul ℝ (U x)] [FiberBundle K U] [VectorBundle ℝ K U]
  [ContMDiffVectorBundle ∞ K U I]

/-- The second covariant derivative obeys the four-term product rule for composition of
smooth bundle maps, with respect to any tangent connection. -/
theorem secondCovariantDerivative_comp
    (covV : CovariantDerivative I F V) [ContMDiffCovariantDerivative covV ∞]
    (covW : CovariantDerivative I G W) [ContMDiffCovariantDerivative covW ∞]
    (covU : CovariantDerivative I K U) [ContMDiffCovariantDerivative covU ∞]
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    {A : Π x : M, V x →L[ℝ] W x} {B : Π x : M, W x →L[ℝ] U x}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun z ↦ V z →L[ℝ] W z) y (A y)))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] K)) ∞
      (fun y ↦ TotalSpace.mk' (G →L[ℝ] K) (E := fun z ↦ W z →L[ℝ] U z) y (B y)))
    (x : M) (u v : TangentSpace I x) :
    (covV.hom covU).secondCovariantDerivative covT (fun y ↦ (B y).comp (A y)) x u v =
      ((covW.hom covU).secondCovariantDerivative covT B x u v).comp (A x) +
        (covW.hom covU B x v).comp (covV.hom covW A x u) +
        (covW.hom covU B x u).comp (covV.hom covW A x v) +
        (B x).comp ((covV.hom covW).secondCovariantDerivative covT A x u v) := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  have hDA := (covV.hom covW).contMDiff_apply hY hA
  have hDB := (covW.hom covU).contMDiff_apply hY hB
  have heq : (fun y ↦ covV.hom covU (fun z ↦ (B z).comp (A z)) y (Y y)) =
      (fun y ↦ (covW.hom covU B y (Y y)).comp (A y)) +
        fun y ↦ (B y).comp (covV.hom covW A y (Y y)) := by
    funext y
    exact hom_comp covV covW covU (hA.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp)) (Y y)
  rw [secondCovariantDerivative_apply (covV.hom covU) covT (hB.clm_bundle_comp hA) x hY,
    secondCovariantDerivative_apply (covW.hom covU) covT hB x hY,
    secondCovariantDerivative_apply (covV.hom covW) covT hA x hY, heq,
    (covV.hom covU).isCovariantDerivativeOnUniv.add
      ((hDB.clm_bundle_comp hA).mdifferentiableAt (by simp))
      ((hB.clm_bundle_comp hDA).mdifferentiableAt (by simp)), add_apply,
    hom_comp covV covW covU (hA.mdifferentiableAt (by simp))
      (hDB.mdifferentiableAt (by simp)),
    hom_comp covV covW covU (hDA.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp)),
    hom_comp covV covW covU (hA.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  abel

end CovariantDerivative
