/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Existence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Metric correction on the real line

The correction of `d + a dx` for the constant metric is `d`, for every real `a`. For the
varying metric `exp(2x)`, the correction of `d` is `d + dx`, and `exp(-x)` is a nowhere-zero
parallel section. These are native covariant derivatives on native trivial vector bundles;
the correction identities hold on arbitrary input sections. The existence examples also
include arbitrary regularity, zero fibre rank, zero-dimensional base and an empty base.
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace TauCeti.Examples.MetricConnection

/-- The native flat connection on the trivial real line over the real line. -/
def flatConnection := CovariantDerivative.trivial (I := 𝓘(ℝ)) (M := ℝ) ℝ

/-- The native flat connection preserves smoothness at every regularity order. -/
instance flatConnection.contMDiffCovariantDerivative (n : ℕ∞ω) :
    flatConnection.ContMDiffCovariantDerivative n :=
  inferInstanceAs (CovariantDerivative.ContMDiffCovariantDerivative
    (CovariantDerivative.trivial (I := 𝓘(ℝ)) (M := ℝ) ℝ) n)

/-- The constant scalar endomorphism-valued one-form `a dx`. -/
def constantOneForm (a : ℝ) (x : ℝ) :
    ℝ →L[ℝ] TangentSpace 𝓘(ℝ) x →L[ℝ] ℝ :=
  a • StrongDual.smulRightL ℝ (TangentSpace 𝓘(ℝ) x) ℝ
    (NormedSpace.fromTangentSpace x).toContinuousLinearMap

/-- The native connection `d + a dx` on the trivial real line. -/
def constantConnection (a : ℝ) := flatConnection.addOneForm (constantOneForm a)

private theorem constantConnection_defect (a x u v : ℝ) (X : TangentSpace 𝓘(ℝ) x) :
    (constantConnection a).derivMetricTensor x u v X =
      - (a * ((NormedSpace.fromTangentSpace x) X * u)) * v -
        u * (a * ((NormedSpace.fromTangentSpace x) X * v)) := by
  have hu : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun y : ℝ ↦ TotalSpace.mk' ℝ y (u : Trivial ℝ ℝ y)) x := by
    simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply]
    exact mdifferentiableAt_const
  have hv : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun y : ℝ ↦ TotalSpace.mk' ℝ y (v : Trivial ℝ ℝ y)) x := by
    simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_apply]
    exact mdifferentiableAt_const
  rw [(constantConnection a).derivMetricTensor_apply (X := fun _ ↦ X) x hu hv]
  simp [constantConnection, constantOneForm, flatConnection, CovariantDerivative.trivial_apply]
  ring

/-- The metric correction removes every constant scalar connection form. -/
theorem constantConnection_metricCorrected (a : ℝ) :
    (constantConnection a).metricCorrected = flatConnection := by
  apply CovariantDerivative.ext
  funext σ x
  apply ContinuousLinearMap.ext
  intro X
  have hc : (constantConnection a).metricCorrection x (σ x) X = -constantOneForm a x (σ x) X := by
    apply ext_inner_right ℝ
    intro v
    rw [CovariantDerivative.inner_metricCorrection, constantConnection_defect]
    simp [constantOneForm, ContinuousLinearMap.smulRightL_apply_apply]
    ring
  rw [CovariantDerivative.metricCorrected_apply]
  simp only [constantConnection, CovariantDerivative.addOneForm_apply, add_apply] at hc ⊢
  rw [hc]
  simp

example : flatConnection.IsMetricCompatible := by
  have h := (constantConnection 0).isMetricCompatible_metricCorrected
  rw [constantConnection_metricCorrected] at h
  exact h

example (cov : CovariantDerivative 𝓘(ℝ) ℝ (Trivial ℝ ℝ))
    (h : cov.IsMetricCompatible) : cov.metricCorrected = cov := h.metricCorrected_eq

private def standardMetric : ContMDiffRiemannianMetric 𝓘(ℝ) ∞ ℝ (Trivial ℝ ℝ) where
  inner _ := innerSL ℝ
  symm _ _ _ := by rw [innerSL_apply_apply, innerSL_apply_apply]; exact real_inner_comm _ _
  pos _ _ hv := by rw [innerSL_apply_apply]; exact real_inner_self_pos.mpr hv
  isVonNBounded _ :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).mem_setOfPred_symm_pos_isVonNBounded_of_inner
      (g := innerSL ℝ) (by
        intro u v
        calc
          innerSL ℝ u v = u * v := by rw [innerSL_apply_apply, Real.inner_apply]
          _ = inner ℝ ((ContinuousLinearEquiv.refl ℝ ℝ) u)
              ((ContinuousLinearEquiv.refl ℝ ℝ) v) := by
            rw [ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.refl_apply,
              Real.inner_apply])).2.2
  contMDiff := IsContMDiffRiemannianBundle.contMDiff_innerSL

private def scaledStandardMetric := standardMetric.rescale (fun x : ℝ ↦ Real.exp (2*x))
  (ContDiff.contMDiff (by fun_prop)) (fun x ↦ Real.exp_pos _)


-- The automatic instance also matches the literal continuity order.
example : flatConnection.metricCorrected.ContMDiffCovariantDerivative 0 := by
  infer_instance

-- Automatic correction regularity for every finite or smooth order, including zero.
example (n : ℕ∞) : flatConnection.metricCorrected.ContMDiffCovariantDerivative n := by
  infer_instance

example (n : ℕ∞) : ∃ cov : CovariantDerivative 𝓘(ℝ) ℝ (Trivial ℝ ℝ),
    cov.ContMDiffCovariantDerivative n ∧ cov.IsMetricCompatible :=
  CovariantDerivative.exists_contMDiffCovariantDerivative_isMetricCompatible
    (I := 𝓘(ℝ)) (F := ℝ) (V := Trivial ℝ ℝ) (k := ∞) (by simp)

example : ∃ cov : CovariantDerivative 𝓘(ℝ) (EuclideanSpace ℝ (Fin 0))
      (Trivial ℝ (EuclideanSpace ℝ (Fin 0))),
    cov.ContMDiffCovariantDerivative 0 ∧ cov.IsMetricCompatible :=
  CovariantDerivative.exists_contMDiffCovariantDerivative_isMetricCompatible
    (I := 𝓘(ℝ)) (F := EuclideanSpace ℝ (Fin 0))
    (V := Trivial ℝ (EuclideanSpace ℝ (Fin 0))) (k := ∞) (by simp)

example : ∃ cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ℝ
      (Trivial (EuclideanSpace ℝ (Fin 0)) ℝ),
    cov.ContMDiffCovariantDerivative ∞ ∧ cov.IsMetricCompatible :=
  CovariantDerivative.exists_contMDiffCovariantDerivative_isMetricCompatible
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (F := ℝ)
    (V := Trivial (EuclideanSpace ℝ (Fin 0)) ℝ) (k := ∞) (by simp)

example : ∃ cov : CovariantDerivative 𝓘(ℝ) ℝ (Trivial (⊥ : TopologicalSpace.Opens ℝ) ℝ),
    cov.ContMDiffCovariantDerivative ∞ ∧ cov.IsMetricCompatible := by
  let : IsEmpty (⊥ : TopologicalSpace.Opens ℝ) := ⟨fun x ↦ x.property⟩
  exact CovariantDerivative.exists_contMDiffCovariantDerivative_isMetricCompatible
    (I := 𝓘(ℝ)) (F := ℝ) (V := Trivial (⊥ : TopologicalSpace.Opens ℝ) ℝ)
    (k := ∞) (by simp)

/-- A trivial real line whose norm is supplied by the varying metric below.
Keeping the native fibre norm unset avoids identifying that metric with the Euclidean norm. -/
def MetricLine (_x : ℝ) := ℝ
  deriving TopologicalSpace, AddCommGroup, Module ℝ, IsTopologicalAddGroup,
    ContinuousSMul ℝ, ContinuousConstSMul ℝ, IsNormableSpace ℝ

instance metricLineSmul (x : ℝ) : ContinuousSMul ℝ (MetricLine x) :=
  inferInstanceAs (ContinuousSMul ℝ ℝ)

/-- Read a vector in the underlying real trivialization. -/
def MetricLine.toReal {x : ℝ} (u : MetricLine x) : ℝ := u

instance metricLineTotal : TopologicalSpace (TotalSpace ℝ MetricLine) :=
  inferInstanceAs (TopologicalSpace (TotalSpace ℝ (Trivial ℝ ℝ)))
instance metricLineFiber : FiberBundle ℝ MetricLine :=
  inferInstanceAs (FiberBundle ℝ (Trivial ℝ ℝ))
instance metricLineVector : VectorBundle ℝ ℝ MetricLine :=
  inferInstanceAs (VectorBundle ℝ ℝ (Trivial ℝ ℝ))
instance metricLineSmoothBundle : ContMDiffVectorBundle ∞ ℝ MetricLine 𝓘(ℝ) :=
  inferInstanceAs (ContMDiffVectorBundle ∞ ℝ (Trivial ℝ ℝ) 𝓘(ℝ))

/-- The smooth positive metric with squared length `exp(2x)`. -/
def exponentialMetric : ContMDiffRiemannianMetric 𝓘(ℝ) ∞ ℝ MetricLine := scaledStandardMetric

/-- The flat connection in the underlying trivialization, before metric correction. -/
def exponentialFlatConnection : CovariantDerivative 𝓘(ℝ) ℝ MetricLine := flatConnection

/-- The flat connection on the metric line preserves smoothness at every order. -/
instance exponentialFlatConnection.contMDiffCovariantDerivative (n : ℕ∞ω) :
    exponentialFlatConnection.ContMDiffCovariantDerivative n :=
  inferInstanceAs (flatConnection.ContMDiffCovariantDerivative n)

instance metricLineRiemannian : RiemannianBundle MetricLine :=
  ⟨exponentialMetric.toRiemannianMetric⟩

private theorem exp_inner (x : ℝ) (u v : MetricLine x) :
    inner ℝ u v = Real.exp (2*x) * (MetricLine.toReal v * MetricLine.toReal u) := by
  calc
    inner ℝ u v = exponentialMetric.inner x u v :=
      Bundle.ContMDiffRiemannianMetric.inner_eq exponentialMetric x u v
    _ = Real.exp (2*x) * (MetricLine.toReal v * MetricLine.toReal u) := by
      unfold exponentialMetric scaledStandardMetric
      -- Unfold the normed-fibre projections installed by `metricLineRiemannian`; the
      -- rescaling theorem uses the original topological/module bundle structures.
      erw [Bundle.ContMDiffRiemannianMetric.rescale_inner]
      dsimp only [standardMetric]
      -- Express the trivial-fibre Riesz map through `toReal`; evaluate the real inner
      -- product by `Real.inner_apply` rather than unfolding it.
      change Real.exp (2*x) * (innerSL ℝ (MetricLine.toReal u) (MetricLine.toReal v)) =
        Real.exp (2*x) * (MetricLine.toReal v * MetricLine.toReal u)
      rw [innerSL_apply_apply, Real.inner_apply, mul_comm (MetricLine.toReal u)]


private theorem MetricLine.toReal_injective {x : ℝ} :
    Function.Injective (@MetricLine.toReal x) := fun _ _ h ↦ h

private theorem MetricLine.toReal_zero {x : ℝ} : (0 : MetricLine x).toReal = 0 := rfl

private theorem MetricLine.toReal_add {x : ℝ} (u v : MetricLine x) :
    (u + v).toReal = u.toReal + v.toReal := rfl

private theorem MetricLine.toReal_smul {x : ℝ} (a : ℝ) (u : MetricLine x) :
    (a • u).toReal = a * u.toReal := by rfl

private theorem exponentialFlatConnection_apply (u : Π x, MetricLine x) (x : ℝ)
    (X : TangentSpace 𝓘(ℝ) x) :
    (exponentialFlatConnection u x X).toReal = (NormedSpace.fromTangentSpace x) X *
      deriv (fun y ↦ (u y).toReal) x := by
  -- Definitional transport through `MetricLine.toReal`, which is the identity on the
  -- fibres: both connections use the same underlying trivialization and module structure.
  -- This uses no identification of the exponential metric norm with the Euclidean norm.
  change flatConnection (fun y ↦ (u y).toReal) x X = _
  simp [flatConnection, CovariantDerivative.trivial_apply]

private theorem real_mvfderiv_apply (f : ℝ → ℝ) (x : ℝ)
    (X : TangentSpace 𝓘(ℝ) x) :
    mvfderiv 𝓘(ℝ) f x X = (NormedSpace.fromTangentSpace x) X * deriv f x := by
  simp

private theorem exponentialFlatConnection_defect (x : ℝ) (u v : MetricLine x)
    (X : TangentSpace 𝓘(ℝ) x) :
    exponentialFlatConnection.derivMetricTensor x u v X =
      2 * Real.exp (2*x) * ((NormedSpace.fromTangentSpace x) X) *
        (v.toReal * u.toReal) := by
  let su : Π y, MetricLine y := fun _ ↦ u.toReal
  let sv : Π y, MetricLine y := fun _ ↦ v.toReal
  have hu : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun y ↦ TotalSpace.mk' ℝ y (su y)) x := by
    simp only [mdifferentiableAt_section]
    exact mdifferentiableAt_const
  have hv : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun y ↦ TotalSpace.mk' ℝ y (sv y)) x := by
    simp only [mdifferentiableAt_section]
    exact mdifferentiableAt_const
  have hp : (fun y ↦ inner ℝ (su y) (sv y)) =
      fun y ↦ Real.exp (2*y) * (v.toReal * u.toReal) := by
    funext y
    exact exp_inner y (su y) (sv y)
  have hd : deriv (fun y ↦ Real.exp (2*y) * (v.toReal * u.toReal)) x =
      2 * Real.exp (2*x) * (v.toReal * u.toReal) := by
    simp [mul_assoc, mul_comm]
  have hsu : deriv (fun y ↦ (su y).toReal) x = 0 := deriv_const x u.toReal
  have hsv : deriv (fun y ↦ (sv y).toReal) x = 0 := deriv_const x v.toReal
  -- The constant sections live in the norm-free trivialization, while the metric tensor
  -- reads the metric-induced normed fibres. `erw` aligns those definitionally equal modules.
  erw [exponentialFlatConnection.derivMetricTensor_apply (X := fun _ ↦ X) x hu hv]
  rw [hp]
  dsimp only
  -- The same metric-induced fibre projections occur in these scalar evaluations.
  erw [exp_inner, exp_inner]
  erw [exponentialFlatConnection_apply, exponentialFlatConnection_apply]
  rw [real_mvfderiv_apply, hd, hsu, hsv]
  simp only [mul_zero, zero_mul, sub_zero]
  ring

/-- For the metric `exp(2x)`, correcting the flat connection adds the one-form `dx`.
The formula holds on all sections, including nondifferentiable sections. -/
theorem exponentialFlatConnection_metricCorrected_apply (u : Π x, MetricLine x) (x : ℝ)
    (X : TangentSpace 𝓘(ℝ) x) :
    exponentialFlatConnection.metricCorrected u x X =
      exponentialFlatConnection u x X + (NormedSpace.fromTangentSpace x) X • u x := by
  rw [CovariantDerivative.metricCorrected_apply]
  simp only [add_apply]
  congr 1
  apply ext_inner_right ℝ
  intro v
  rw [CovariantDerivative.inner_metricCorrection, exponentialFlatConnection_defect, exp_inner]
  simp only [MetricLine.toReal_smul]
  ring

example : exponentialFlatConnection.metricCorrected.ContMDiffCovariantDerivative ∞ := by
  have : ContMDiffVectorBundle (∞ + 1) ℝ MetricLine 𝓘(ℝ) :=
    .of_le (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  have : IsContMDiffRiemannianBundle 𝓘(ℝ) (∞ + 1) ℝ MetricLine :=
    .of_le (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  infer_instance

/-- The nowhere-zero section `exp(-x)`, parallel for the corrected exponential metric. -/
def parallelSection (y : ℝ) : MetricLine y := Real.exp (-y)

/-- The parallel section vanishes nowhere. -/
theorem parallelSection_ne_zero (x : ℝ) : parallelSection x ≠ 0 := Real.exp_ne_zero _

/-- The section `exp(-x)` is parallel for the corrected connection. -/
theorem parallelSection_parallel (x : ℝ) (X : TangentSpace 𝓘(ℝ) x) :
    exponentialFlatConnection.metricCorrected parallelSection x X = 0 := by
  apply MetricLine.toReal_injective
  rw [MetricLine.toReal_zero, exponentialFlatConnection_metricCorrected_apply,
    MetricLine.toReal_add, exponentialFlatConnection_apply, MetricLine.toReal_smul]
  have hd : deriv (fun y ↦ (parallelSection y).toReal) x = -Real.exp (-x) := by
    simpa [parallelSection, MetricLine.toReal] using ((hasDerivAt_id x).neg.exp).deriv
  rw [hd]
  simp only [parallelSection, MetricLine.toReal]
  ring

end TauCeti.Examples.MetricConnection
