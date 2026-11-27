/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Second
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci.Contraction
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Differentiating the Ricci contractions

Differentiating the metric trace of Ricci and the twice contracted Bianchi identity gives
the two contractions of the second covariant derivative which occur in the Ricci evolution
equation. The proof differentiates scalar metric traces with a smooth extension of the
remaining tangent argument, so the derivative of that argument is retained and canceled.

## References

* P. Topping, *Lectures on the Ricci Flow*, CUP (2006), §§2.3–2.5.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public noncomputable section

open Bundle CovariantDerivative FiberBundle TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- On a differentiable Ricci section, the induced bilinear connection agrees with the
native covariant derivative of Ricci, whose differentiation direction is last. -/
theorem bilinear_ricciTensor_apply {y : M}
    (hRic : MDiffAt (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun q : M ↦ TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) z
      (cov.ricciTensor z).toContinuousBilinearMap) y)
    (w u v : TangentSpace I y) :
    cov.bilinear (fun z ↦ (cov.ricciTensor z).toContinuousBilinearMap) y w u v =
      cov.derivRicciTensor y u v w := by
  rw [derivRicciTensor_def]
  exact cov.bilinear_apply hRic w u v

/-- The second covariant derivative of Ricci is symmetric in its two Ricci inputs,
with both derivative directions fixed. -/
theorem IsMetricCompatible.secondCovariantDerivative_ricciTensor_comm
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (a b u v : TangentSpace I x) :
    cov.bilinear.secondCovariantDerivative cov
      (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x a b u v =
      cov.bilinear.secondCovariantDerivative cov
        (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x a b v u := by
  apply cov.secondCovariantDerivative_bilinear_apply_comm cov
  intro y p q
  simpa only [LinearMap.toContinuousBilinearMap_apply] using
    IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht y p q

/-- Differentiating the Ricci metric trace gives the scalar Hessian, with the two
derivative directions kept outside the trace. -/
theorem IsMetricCompatible.sum_secondCovariantDerivative_ricciTensor_self_eq_hessian
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (a c : TangentSpace I x) :
    ∑ i, cov.bilinear.secondCovariantDerivative cov
      (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x a c (b i) (b i) =
      hessian I cov.scalarCurvature x a c := by
  have hRic := cov.contMDiff_ricciTensor
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ c
  let B := fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap
  let D := fun y ↦ cov.bilinear B y (Y y)
  have hK (y : M) (u v w : TangentSpace I y) :
      cov.bilinear B y w u v = cov.derivRicciTensor y u v w :=
    cov.bilinear_ricciTensor_apply (hRic.mdifferentiableAt (by simp)) w u v
  have hD := contMDiff_apply cov.bilinear hY (by simpa using hRic)
  have hpair ⦃σ τ : Π y : M, TangentSpace I y⦄ (hσ : MDiffAt (T% σ) x)
      (hτ : MDiffAt (T% τ) x) : MDiffAt (fun y ↦ D y (σ y) (τ y)) x :=
    (hD.mdifferentiableAt (by simp)).clm_bundle_apply₂_trivial hσ hτ
  have htrace (y : M) :
      LinearMap.BilinMap.metricTrace (D y).toLinearMap₁₂ =
        mvfderiv I cov.scalarCurvature y (Y y) := by
    rw [LinearMap.BilinMap.metricTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I y))]
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, D]
    simp_rw [hK]
    exact hcov.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature y
      (stdOrthonormalBasis ℝ (TangentSpace I y)) (Y y)
  have hd := hcov.mvfderiv_metricTrace_apply_eq_sum hpair b a
  simp_rw [htrace] at hd
  have hh := hessian_apply_eq_mvfderiv_sub_of_isLeviCivitaConnection ⟨hcov, ht⟩
    (((cov.contMDiff_scalarCurvature (n := ⊤)) x).of_le (by simp)) a Y
    (hY.mdifferentiableAt (by simp))
  have hterm (i : ι) :
      cov.bilinear.secondCovariantDerivative cov B x a (Y x) (b i) (b i) =
        cov.derivBilinearTensor D x (b i) (b i) a -
          cov.derivRicciTensor x (b i) (b i) (cov Y x a) := by
    rw [secondCovariantDerivative_apply _ _ hRic x hY]
    simp only [sub_apply, D]
    rw [cov.bilinear_apply (hD.mdifferentiableAt (by simp)),
      cov.bilinear_apply (hRic.mdifferentiableAt (by simp)), ← derivRicciTensor_def]
  have heq : (∑ i, cov.bilinear.secondCovariantDerivative cov B x a (Y x) (b i) (b i)) =
      (∑ i, cov.derivBilinearTensor D x (b i) (b i) a) -
        mvfderiv I cov.scalarCurvature x (cov Y x a) := by
    calc
      _ = ∑ i, (cov.derivBilinearTensor D x (b i) (b i) a -
          cov.derivRicciTensor x (b i) (b i) (cov Y x a)) :=
        Finset.sum_congr rfl fun i _ ↦ hterm i
      _ = _ := by
        rw [Finset.sum_sub_distrib,
          hcov.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature]
  exact heq.trans (by linarith)

/-- Differentiating twice contracted Bianchi gives half the scalar Hessian. The trace
contains the inner derivative direction and the first Ricci input. -/
theorem IsMetricCompatible.two_mul_sum_secondCovariantDerivative_ricciTensor_eq_hessian
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (a c : TangentSpace I x) :
    2 * ∑ i, cov.bilinear.secondCovariantDerivative cov
      (fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap) x a (b i) (b i) c =
      hessian I cov.scalarCurvature x a c := by
  have hRic := cov.contMDiff_ricciTensor
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E ∞ c
  let B := fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap
  have hKRic (y : M) (u v w : TangentSpace I y) :
      cov.bilinear B y w u v = cov.derivRicciTensor y u v w :=
    cov.bilinear_ricciTensor_apply (hRic.mdifferentiableAt (by simp)) w u v
  let D := cov.bilinearDerivativeApplyRight B W
  have hpair ⦃σ τ : Π y : M, TangentSpace I y⦄ (hσ : MDiffAt (T% σ) x)
      (hτ : MDiffAt (T% τ) x) : MDiffAt (fun y ↦ D y (σ y) (τ y)) x :=
    cov.mdifferentiableAt_bilinearDerivativeApplyRight hRic hW hσ hτ
  have htrace (y : M) : LinearMap.BilinMap.metricTrace (D y).toLinearMap₁₂ =
      (1 / 2 : ℝ) * mvfderiv I cov.scalarCurvature y (W y) := by
    rw [LinearMap.BilinMap.metricTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I y))]
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, D,
      bilinearDerivativeApplyRight_apply]
    simp_rw [hKRic]
    have h := hcov.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature ht y
      (stdOrthonormalBasis ℝ (TangentSpace I y)) (W y)
    linarith
  have hd := hcov.mvfderiv_metricTrace_apply_eq_sum hpair b a
  simp_rw [htrace] at hd
  have hR : ContMDiff I 𝓘(ℝ) ∞ cov.scalarCurvature := cov.contMDiff_scalarCurvature
  have hdf : MDiffAt (fun y ↦ mvfderiv I cov.scalarCurvature y (W y)) x := by
    have hsection := hR.contMDiff_totalSpaceMk_mvfderiv.clm_bundle_apply hW
    exact Bundle.Trivial.mdifferentiableAt_section_iff.mp
      (hsection.mdifferentiableAt (by simp))
  rw [mvfderiv_fun_mul mdifferentiableAt_const hdf] at hd
  simp only [mvfderiv_const, smul_zero, add_zero, smul_apply, smul_eq_mul] at hd
  have hh := hessian_apply_eq_mvfderiv_sub_of_isLeviCivitaConnection ⟨hcov, ht⟩
    ((hR x).of_le (by simp)) a W (hW.mdifferentiableAt (by simp))
  have hterm := cov.derivBilinearTensor_bilinearDerivativeApplyRight_apply hRic hW x a
  simp_rw [D, B, hterm] at hd
  rw [Finset.sum_add_distrib] at hd
  have hdiv : 2 * ∑ i, cov.bilinear B x (b i) (b i) (cov W x a) =
      mvfderiv I cov.scalarCurvature x (cov W x a) := by
    simp_rw [hKRic]
    exact hcov.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature ht x b (cov W x a)
  linarith

end CovariantDerivative
