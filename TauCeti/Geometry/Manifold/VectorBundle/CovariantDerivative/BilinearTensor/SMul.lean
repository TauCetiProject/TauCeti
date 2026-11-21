/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Constant scaling of the covariant bilinear-tensor derivative

The native total bilinear-tensor derivative commutes with real constant scaling, on arbitrary
finite-dimensional real vector bundles. Nondifferentiable fields are included: invertible
constant scaling preserves pairing differentiability, and both derivatives otherwise vanish.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), §2.3.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ F]
  (cov : CovariantDerivative I F V)
  {b : (x : M) → V x →L[ℝ] V x →L[ℝ] ℝ} {x : M}

/-- Covariant differentiation of a differentiable bilinear field commutes with
constant real scaling on an arbitrary finite-dimensional real vector bundle. -/
private theorem derivBilinearTensor_const_smul_of_mdifferentiable
    (hb : ∀ ⦃σ τ : Π x : M, V x⦄,
      MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    (c : ℝ) (u v : V x) (w : TangentSpace I x) :
    cov.derivBilinearTensor (c • b) x u v w = c * cov.derivBilinearTensor b x u v w := by
  have hcb : ∀ ⦃σ τ : Π x : M, V x⦄,
      MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        MDiffAt (fun y ↦ (c • b) y (σ y) (τ y)) x := by
    intro σ τ hσ hτ
    exact (hb hσ hτ).const_smul c
  rw [cov.derivBilinearTensor_apply_eq_extend hcb,
    cov.derivBilinearTensor_apply_eq_extend hb]
  simp only [Pi.smul_apply, smul_apply]
  rw [TauCeti.mvfderiv_const_smul (hb (mdifferentiableAt_extend I F u)
    (mdifferentiableAt_extend I F v)) c]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The total covariant bilinear derivative sends the zero field to zero. -/
@[simp]
theorem derivBilinearTensor_zero :
    cov.derivBilinearTensor (0 : (y : M) → V y →L[ℝ] V y →L[ℝ] ℝ) x = 0 := by
  have hb : ∀ ⦃σ τ : Π x : M, V x⦄,
      MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        MDiffAt (fun _ : M ↦ (0 : ℝ)) x := fun _ _ _ _ ↦ mdifferentiableAt_const
  ext u v w
  rw [cov.derivBilinearTensor_apply_eq_extend hb]
  simp only [Pi.zero_apply, zero_apply, mvfderiv_apply_eq_mfderiv_apply, mfderiv_const, sub_zero]
  exact sub_self _

/-- The total covariant derivative of a bilinear field commutes with constant
real scaling, including fields whose pairings fail to be differentiable. -/
@[simp] theorem derivBilinearTensor_const_smul (c : ℝ) (u v : V x) (w : TangentSpace I x) :
    cov.derivBilinearTensor (c • b) x u v w = c * cov.derivBilinearTensor b x u v w := by
  classical
  by_cases hc : c = 0
  · subst c
    have hz : (0 : ℝ) • b = 0 := by
      funext y
      ext a d
      -- Scalar multiplication of the section evaluates by scalar multiplication of its value.
      change (0 : ℝ) • b y a d = 0
      exact zero_smul ℝ _
    rw [hz, cov.derivBilinearTensor_zero]
    simp only [zero_apply, zero_mul]
  by_cases hb : ∀ ⦃σ τ : Π x : M, V x⦄,
      MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (fun y ↦ b y (σ y) (τ y)) x
  · exact cov.derivBilinearTensor_const_smul_of_mdifferentiable hb c u v w
  have hcb : ¬ ∀ ⦃σ τ : Π x : M, V x⦄,
      MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        MDiffAt (fun y ↦ (c • b) y (σ y) (τ y)) x := by
    intro hcb
    apply hb
    intro σ τ hσ hτ
    have h := (hcb hσ hτ).const_smul c⁻¹
    have heq : (c⁻¹ • fun y ↦ (c • b) y (σ y) (τ y)) =
        (fun y ↦ b y (σ y) (τ y)) := by
      funext y
      -- Evaluate the section and both bilinear arguments before cancelling the scalar.
      change c⁻¹ • (c • b y (σ y) (τ y)) = _
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact heq ▸ h
  simp [cov.derivBilinearTensor_eq_zero_of_not hb,
    cov.derivBilinearTensor_eq_zero_of_not hcb]

end CovariantDerivative
