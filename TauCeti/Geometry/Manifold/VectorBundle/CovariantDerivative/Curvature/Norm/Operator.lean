/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Norm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# Bounding the curvature endomorphism by the full curvature norm

The full Riemann curvature norm bounds the quadratic form of the curvature endomorphism on
every bivector. The bound uses the native orthonormal basis of the second exterior power.

The curvature estimates are adapted from the formalizations in
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- Every coefficient of the native exterior-square curvature operator in an orthonormal
wedge basis is bounded by the full Riemann curvature norm. -/
theorem abs_inner_curvatureEndomorphism_exteriorPower_le {ι : Type*}
    [Fintype ι] [LinearOrder ι] (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (i j : Set.powersetCard ι 2) :
    |⟪cov.curvatureEndomorphism hcov x (b.exteriorPower 2 i), b.exteriorPower 2 j⟫| ≤
      cov.riemannCurvatureNorm x := by
  have hbi (s : Set.powersetCard ι 2) :
      b.exteriorPower 2 s = exteriorPower.ιMulti ℝ 2
        (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
    rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower,
      exteriorPower.coe_basis]
    simp only [exteriorPower.ιMulti_family, OrthonormalBasis.coe_toBasis]
  simp only [hbi, cov.inner_curvatureEndomorphism_ιMulti,
    ← riemannCurvatureTensor_apply]
  simpa only [Function.comp_apply, b.orthonormal.1, mul_one] using
    cov.abs_riemannCurvatureTensor_le x
      (b (Set.powersetCard.ofFinEmbEquiv.symm i 0))
      (b (Set.powersetCard.ofFinEmbEquiv.symm i 1))
      (b (Set.powersetCard.ofFinEmbEquiv.symm j 1))
      (b (Set.powersetCard.ofFinEmbEquiv.symm j 0))

/-- A dimension-dependent operator-norm bound in terms of the full Riemann curvature norm.
No curvature sign or torsion-free hypothesis is needed. -/
theorem norm_curvatureEndomorphism_le (x : M) :
    ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ ≤
      ((Module.finrank ℝ E).choose 2 : ℝ) ^ 2 * cov.riemannCurvatureNorm x := by
  classical
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let e := b.exteriorPower 2
  let A := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  have hentry i j : |⟪A (e i), e j⟫| ≤ cov.riemannCurvatureNorm x :=
    cov.abs_inner_curvatureEndomorphism_exteriorPower_le hcov x b i j
  have hcolumn i : ‖A (e i)‖ ≤
      (Fintype.card (Set.powersetCard (Fin (Module.finrank ℝ (TangentSpace I x))) 2) : ℝ) *
        cov.riemannCurvatureNorm x := by
    calc
      ‖A (e i)‖ = ‖∑ j, ⟪e j, A (e i)⟫ • e j‖ := by rw [e.sum_repr']
      _ ≤ ∑ j, ‖⟪e j, A (e i)⟫ • e j‖ := norm_sum_le _ _
      _ = ∑ j, |⟪A (e i), e j⟫| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_smul, e.orthonormal.1 j, mul_one, Real.norm_eq_abs, real_inner_comm]
      _ ≤ ∑ _j, cov.riemannCurvatureNorm x := Finset.sum_le_sum fun j _ ↦ hentry i j
      _ = _ := by simp
  have h := A.opNorm_le_sum_norm_apply_orthonormalBasis e
  apply h.trans
  calc
    ∑ i, ‖A (e i)‖ ≤ ∑ _i,
        (Fintype.card (Set.powersetCard (Fin (Module.finrank ℝ (TangentSpace I x))) 2) : ℝ) *
          cov.riemannCurvatureNorm x := Finset.sum_le_sum fun i _ ↦ hcolumn i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
        Fintype.card_fin, VectorBundle.finrank_eq ℝ E (TangentSpace I) x]
      ring

/-- The full Riemann norm controls the curvature quadratic form on arbitrary bivectors. -/
theorem abs_inner_curvatureEndomorphism_le (x : M)
    (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    |⟪cov.curvatureEndomorphism hcov x z, z⟫| ≤
      ((Module.finrank ℝ E).choose 2 : ℝ) ^ 2 * cov.riemannCurvatureNorm x * ‖z‖ ^ 2 := by
  calc
    _ ≤ ‖cov.curvatureEndomorphism hcov x z‖ * ‖z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ * ‖z‖ * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        ((LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)).le_opNorm z)
        (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, ← pow_two]
      exact mul_le_mul_of_nonneg_right (cov.norm_curvatureEndomorphism_le hcov x) (sq_nonneg _)

end CovariantDerivative
