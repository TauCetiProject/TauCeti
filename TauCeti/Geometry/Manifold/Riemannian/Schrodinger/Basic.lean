/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DirichletEnergy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic

/-!
# Scalar Schrödinger forms

The scalar quadratic form of `-Δ_g + P` is the native Dirichlet energy on `WithMetric g`
plus the potential energy. This module supplies its defining equation, scaling law and
Dirichlet-energy decompositions, including compactly supported `C¹` tests.
-/

public noncomputable section

open Bundle Manifold MeasureTheory
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti TauCeti.Manifold

variable [LindelofSpace M]

/-- The quadratic form of `-Δ_g + P`. The potential and the test are functions on the underlying
manifold. -/
def scalarSchrodingerForm
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (P φ : M → ℝ) : ℝ :=
  ∫ x : WithMetric g, (‖mgradient I (φ ∘ WithMetric.ofWithMetric) x‖ ^ 2 +
    P x.ofWithMetric * φ x.ofWithMetric ^ 2) ∂riemannianVolume I (WithMetric g)

/-- The scalar Schrödinger form evaluated on the metric-indexed copy of the manifold. -/
theorem scalarSchrodingerForm_def
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (P φ : M → ℝ) :
    scalarSchrodingerForm g P φ =
      ∫ x : WithMetric g, (‖mgradient I (φ ∘ WithMetric.ofWithMetric) x‖ ^ 2 +
        P x.ofWithMetric * φ x.ofWithMetric ^ 2) ∂riemannianVolume I (WithMetric g) := (rfl)

/-- The scalar Schrödinger form is the Dirichlet energy plus the potential energy when
both integrands are integrable. -/
theorem scalarSchrodingerForm_eq_dirichletEnergy_add
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (P φ : M → ℝ)
    (hD : Integrable (fun x : WithMetric g ↦
      ‖mgradient I (φ ∘ WithMetric.ofWithMetric) x‖ ^ 2)
      (riemannianVolume I (WithMetric g)))
    (hP : Integrable (fun x : WithMetric g ↦ P x.ofWithMetric * φ x.ofWithMetric ^ 2)
      (riemannianVolume I (WithMetric g))) :
    scalarSchrodingerForm g P φ =
      dirichletEnergy I (φ ∘ (WithMetric.ofWithMetric : WithMetric g → M)) +
        ∫ x : WithMetric g, P x.ofWithMetric * φ x.ofWithMetric ^ 2
          ∂riemannianVolume I (WithMetric g) := by
  rw [scalarSchrodingerForm_def, dirichletEnergy_def, integral_add hD hP]

/-- For continuous potentials, every compactly supported `C¹` test admits the
Dirichlet-energy decomposition of the scalar Schrödinger form. -/
theorem scalarSchrodingerForm_eq_dirichletEnergy_add_of_hasCompactSupport
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {P φ : M → ℝ} (hP : Continuous P) (hφ : ContMDiff I 𝓘(ℝ) 1 φ)
    (hc : HasCompactSupport φ) :
    scalarSchrodingerForm g P φ =
      dirichletEnergy I (φ ∘ (WithMetric.ofWithMetric : WithMetric g → M)) +
        ∫ x : WithMetric g, P x.ofWithMetric * φ x.ofWithMetric ^ 2
          ∂riemannianVolume I (WithMetric g) := by
  have hφ' : ContMDiff I 𝓘(ℝ) 1 (φ ∘ (WithMetric.ofWithMetric : WithMetric g → M)) :=
    hφ.comp WithMetric.contMDiff_ofWithMetric
  have hc' : HasCompactSupport (φ ∘ (WithMetric.ofWithMetric : WithMetric g → M)) := by
    simpa only [WithMetric.coe_homeomorph] using hc.comp_homeomorph (WithMetric.homeomorph g)
  have hcSq : HasCompactSupport (fun x : WithMetric g ↦ φ x.ofWithMetric ^ 2) :=
    hc'.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hcP : HasCompactSupport (fun x : WithMetric g ↦ P x.ofWithMetric * φ x.ofWithMetric ^ 2) :=
    hcSq.mul_left
  have hP' : Continuous (fun x : WithMetric g ↦ P x.ofWithMetric * φ x.ofWithMetric ^ 2) :=
    (hP.comp WithMetric.continuous_ofWithMetric).mul (hφ'.continuous.pow 2)
  exact scalarSchrodingerForm_eq_dirichletEnergy_add g P φ
    (integrable_norm_sq_mgradient hφ' hc') (hP'.integrable_of_hasCompactSupport hcP)

/-- Multiplying a test by a real constant scales the scalar Schrödinger form by its square. -/
@[simp]
theorem scalarSchrodingerForm_smul
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (P φ : M → ℝ) (c : ℝ) :
    scalarSchrodingerForm g P (c • φ) = c ^ 2 * scalarSchrodingerForm g P φ := by
  have hcomp : (c • φ) ∘ (WithMetric.ofWithMetric : WithMetric g → M) =
      c • (φ ∘ WithMetric.ofWithMetric) := rfl
  rw [scalarSchrodingerForm_def, scalarSchrodingerForm_def, ← integral_const_mul, hcomp]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [mgradient_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, smul_eq_mul,
    mul_pow, sq_abs]
  ring

/-- With zero potential the scalar Schrödinger form is the Dirichlet energy. -/
@[simp]
theorem scalarSchrodingerForm_zero_potential
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (φ : M → ℝ) :
    scalarSchrodingerForm g 0 φ =
      dirichletEnergy I (φ ∘ (WithMetric.ofWithMetric : WithMetric g → M)) := by
  simp [scalarSchrodingerForm_def, dirichletEnergy_def]

/-- The zero test has zero scalar Schrödinger form for every potential. -/
@[simp]
theorem scalarSchrodingerForm_zero
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (P : M → ℝ) :
    scalarSchrodingerForm g P 0 = 0 := by
  simp [scalarSchrodingerForm_def, Function.comp_def]

end Bundle.ContMDiffRiemannianMetric
