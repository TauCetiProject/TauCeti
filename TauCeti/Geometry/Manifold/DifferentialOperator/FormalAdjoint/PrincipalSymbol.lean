/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The principal symbol of a formal adjoint

Let `V` and `W` be smooth real vector bundles of finite rank over a manifold `M`, with continuous
fibre metrics, and let `μ` be a locally finite measure on `M` that is positive on open sets. If
`Q : Γ(W) → Γ(V)` is a formal adjoint (`LinearMap.IsFormalAdjoint`) of a differential operator
`P : Γ(V) → Γ(W)` of order at most `m`, and both are differential operators of order at most `m`,
then the geometric principal symbol (`TauCeti.sectionPrincipalSymbol`) of `Q` is `(-1) ^ m` times
the fibrewise adjoint of that of `P`:

`⟪σ_geom(P)(ξ) v, w⟫ = (-1) ^ m ⟪v, σ_geom(Q)(ξ) w⟫` for `ξ ∈ T_x*M`, `v ∈ V_x`, `w ∈ W_x`.

In the Fourier convention, where `∂ⱼ` has symbol `i ξⱼ` and an operator of order `m` has Fourier
symbol `i ^ m σ_geom`, the factor `(-1) ^ m` is absorbed by complex conjugation of `i ^ m`, and the
statement reads `σ_F(Q) = σ_F(P)*`. The measure `μ` affects only the lower-order terms of `Q`, not
its principal symbol. This is the vector bundle version of
`LinearMap.IsFormalTranspose.smoothPrincipalSymbol_eq` for operators on the smooth functions.

The proof reads the symbols off the iterated commutators. With `ξ = df_x`, the `m`-fold commutator
`[⋯[P, f], …, f]` is an operator of order zero whose fibre map at `x` is `m!` times
`σ_geom(P)(ξ)`, and its formal adjoint is the `m`-fold commutator `[⋯[Q, -f], …, -f]`
(`LinearMap.IsFormalAdjoint.smulCommutator_pow`), whose fibre map is `m!` times
`σ_geom(Q)(-ξ) = (-1) ^ m σ_geom(Q)(ξ)`. Formal adjoints of operators of order zero are pointwise
adjoints (`LinearMap.IsFormalAdjoint.inner_apply_eq_of_mem_differentialOperators_zero`).

## Main results

* `LinearMap.IsFormalAdjoint.inner_sectionPrincipalSymbol_apply`: the identity above.

## References

* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (the symbol of the adjoint operator).
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti
open scoped ContDiff Manifold RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContinuousRiemannianBundle F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]
  [IsContinuousRiemannianBundle F' W]
  {μ : Measure M} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {x : M} {m : ℕ}

/-- **The principal symbol of a formal adjoint.** If the differential operator `Q : Γ(W) → Γ(V)`
of order at most `m` is a formal adjoint of the differential operator `P : Γ(V) → Γ(W)` of order at
most `m`, then at every interior point the geometric principal symbol of `Q` is `(-1) ^ m` times the
fibrewise adjoint of that of `P`: `⟪σ_geom(P)(ξ) v, w⟫ = (-1) ^ m ⟪v, σ_geom(Q)(ξ) w⟫`. -/
theorem IsFormalAdjoint.inner_sectionPrincipalSymbol_apply
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m}
    (h : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ)
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) (w : W x) :
    ⟪sectionPrincipalSymbol I hx P ξ v, w⟫ =
      (-1) ^ m * ⟪v, sectionPrincipalSymbol I hx Q ξ w⟫ := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  obtain ⟨t, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F') ∞ x w
  simp only [ContMDiffSection.evalLinearMap_apply]
  -- The `m`-fold commutators of `P` with `f` and of `Q` with `-f` are formal adjoints of each
  -- other, and the first has order zero, so they are pointwise adjoints.
  have hPs := tsupport_differentialOperators_section_apply_subset P.property
  have hQs := tsupport_differentialOperators_section_apply_subset Q.property
  have hC := (h.smulCommutator_pow hPs hQs f m).inner_apply_eq_of_mem_differentialOperators_zero
    (smulCommutator_pow_mem_differentialOperators (m := 0) (by simp [P.property]) f) s t x
  -- The symbol of `Q` at `d(-f)_x = -df_x` is `(-1) ^ m` times its symbol at `df_x`.
  have hQ : sectionPrincipalSymbol I hx Q (mvfderiv I f x) =
      (-1 : ℝ) ^ m • sectionPrincipalSymbol I hx Q (mvfderiv I (-f : C^∞⟮I, M; ℝ⟯) x) := by
    rw [ContMDiffMap.coe_neg, mvfderiv_neg, ← neg_one_smul ℝ (mvfderiv I f x),
      sectionPrincipalSymbol_smul_covector, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
      one_smul]
  rw [hQ, LinearMap.smul_apply, real_inner_smul_right, sectionPrincipalSymbol_mvfderiv,
    sectionPrincipalSymbol_mvfderiv, real_inner_smul_left, real_inner_smul_right, hC, ← mul_assoc,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end LinearMap
