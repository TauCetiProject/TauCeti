/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
import TauCeti.Analysis.InnerProductSpace.Complex
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Formal adjoints of complex-linear operators and the complex pairings

Let `V` and `W` be complex vector bundles over a manifold `M` whose fibres carry real inner
products, and let `μ` be a measure on `M`. Formal adjunction (`LinearMap.IsFormalAdjoint`) is
defined with the real inner products. For complex-linear operators `P : Γ(V) → Γ(W)` and
`Q : Γ(W) → Γ(V)` it also gives the adjoint identity for the complex pairings
`⟪s x, r x⟫_ℂ = ⟪s x, r x⟫ - i ⟪s x, i r x⟫` (`ContMDiffSection.complexInnerSection`), the
Hermitian metrics whose real parts are the given inner products when multiplication by `i`
preserves them: the imaginary part of `⟪s, r⟫_ℂ` is `-⟪s, i r⟫`, and `Q (i r) = i Q r`.

## Main results

* `LinearMap.IsFormalAdjoint.integral_complexInnerSection_eq`: if `Q` is a formal adjoint of `P`
  for the real inner products, then `∫ ⟪P a, b⟫_ℂ dμ = ∫ ⟪a, Q b⟫_ℂ dμ` for compactly supported
  sections `a` and `b`.
-/

public section

noncomputable section

open MeasureTheory Bundle
open scoped ContDiff Manifold RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, IsScalarTower ℝ ℂ (W x)] [FiberBundle F' W] [VectorBundle ℝ F' W] [VectorBundle ℂ F' W]
  [IsContMDiffRiemannianBundle I ∞ F' W]

namespace LinearMap

/-- **Integration by parts for the complex pairings.** If the complex-linear operator `Q` is a
formal adjoint of the complex-linear operator `P` for the real inner products, then
`∫ ⟪P a, b⟫_ℂ dμ = ∫ ⟪a, Q b⟫_ℂ dμ` for the complex pairings
(`ContMDiffSection.complexInnerSection`) of compactly supported sections `a` and `b`. -/
theorem IsFormalAdjoint.integral_complexInnerSection_eq [MeasurableSpace M]
    [OpensMeasurableSpace M] {μ : Measure M} [IsFiniteMeasureOnCompacts μ]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℂ] Cₛ^∞⟮I; F', W⟯} {Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℂ] Cₛ^∞⟮I; F, V⟯}
    (hPQ : (P.restrictScalars ℝ).IsFormalAdjoint (Q.restrictScalars ℝ) μ)
    {a : Cₛ^∞⟮I; F, V⟯} (ha : IsCompact a.tsupport) {b : Cₛ^∞⟮I; F', W⟯}
    (hb : IsCompact b.tsupport) :
    ∫ x, ContMDiffSection.complexInnerSection (P a) b x ∂μ =
      ∫ x, ContMDiffSection.complexInnerSection a (Q b) x ∂μ := by
  have hb' : IsCompact (Complex.I • b).tsupport := by
    rwa [ContMDiffSection.tsupport_smul_of_normedAlgebra _ _ Complex.I_ne_zero]
  -- The real pairings are continuous with compact support, hence integrable.
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F')
    (V := W)
  have hP' (x : M) : ContMDiffSection.complexInnerSection (P a) b x =
      (⟪P a x, b x⟫ : ℂ) - Complex.I * (⟪P a x, (Complex.I • b) x⟫ : ℂ) := by
    rw [ContMDiffSection.complexInnerSection_apply, TauCeti.extendRCLike_innerₗ_apply,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply]
  have hQ' (x : M) : ContMDiffSection.complexInnerSection a (Q b) x =
      (⟪a x, Q b x⟫ : ℂ) - Complex.I * (⟪a x, Q (Complex.I • b) x⟫ : ℂ) := by
    rw [ContMDiffSection.complexInnerSection_apply, TauCeti.extendRCLike_innerₗ_apply, map_smul,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply]
  simp only [hP', hQ']
  rw [integral_sub (ContMDiffSection.integrable_inner (Or.inr hb)).ofReal
      ((ContMDiffSection.integrable_inner (Or.inr hb')).ofReal.const_mul _),
    integral_sub (ContMDiffSection.integrable_inner (Or.inl ha)).ofReal
      ((ContMDiffSection.integrable_inner (Or.inl ha)).ofReal.const_mul _),
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]
  have h₁ := hPQ.integral_inner_eq (s := a) (t := b) (Or.inl ha)
  have h₂ := hPQ.integral_inner_eq (s := a) (t := Complex.I • b) (Or.inl ha)
  simp only [LinearMap.coe_restrictScalars] at h₁ h₂
  rw [h₁, h₂]

end LinearMap
