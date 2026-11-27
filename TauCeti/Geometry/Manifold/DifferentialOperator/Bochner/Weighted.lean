/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Bochner.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Riemannian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Exp
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.InnerProductSpace

/-!
# The weighted Laplacian and its Bochner connection

Let `M` be a Riemannian manifold without boundary with Riemannian volume `dV`, and let `φ` be a
smooth function. The **weighted Laplacian** of the density `e^φ dV` is

`Δ_φ f = Δ f + ⟪grad φ, grad f⟫ = e^(-φ) div (e^φ grad f)`

(`TauCeti.smoothWeightedLaplacian`, `TauCeti.exp_mul_smoothWeightedLaplacian_apply`). It plays for
the density `e^φ dV` the role that the Laplace–Beltrami operator `Δ = div ∘ grad` plays for `dV`:
the divergence theorem gives the weighted Green identity

`∫ (Δ_φ f) g e^φ dV = -∫ ⟪grad f, grad g⟫ e^φ dV`

whenever `f` or `g` has compact support (`TauCeti.integral_smoothWeightedLaplacian_mul`), so
`Δ_φ` is formally self-adjoint for `e^φ dV`
(`TauCeti.isFormalTranspose_smoothWeightedLaplacian`). The operator `-Δ_φ` is of Laplace type with
constant `1`, since it differs from `-Δ` by a vector field.

Its **Bochner connection** is computed by the formula for the rough Laplacian of `d + ⟪Y, ·⟫`
on the trivial line bundle (`CovariantDerivative.roughLaplacian_trivialAddInner`): with
`Y = ½ grad φ`,

`-Δ_φ f = ∇*∇ f + (½ Δφ + ¼ ‖grad φ‖²) f`

(`TauCeti.neg_smoothWeightedLaplacian_apply_eq`). The connection `d + ⟪Y, ·⟫` is metric only for
`Y = 0`, and the Bochner connection is unique, so the Bochner connection of `-Δ_φ` is compatible
with the standard fibre metric exactly when `dφ = 0`
(`TauCeti.isMetricCompatible_trivialAddInner_iff_of_neg_smoothWeightedLaplacian_eq`).

This shows that the metric compatibility of the Bochner connection of a formally self-adjoint
operator of Laplace type (`CovariantDerivative.isMetricCompatible_bochnerConnection`) depends on
the density being the Riemannian volume. For instance, for the weight `φ = sin` on the real line,
the operator `-Δ_φ = -∂ₓ² - cos x ∂ₓ` is formally self-adjoint for the density `e^(sin x) dx`, but
its Bochner connection `d + ½ cos x dx` is not metric
(`TauCeti.not_isMetricCompatible_trivialAddInner_of_neg_smoothWeightedLaplacian_sin_eq`).

## Main definitions

* `TauCeti.smoothWeightedLaplacian φ`: the weighted Laplacian `Δ + ⟪grad φ, grad ·⟫`.

## Main results

* `TauCeti.integral_smoothWeightedLaplacian_mul`: the weighted Green identity.
* `TauCeti.isFormalTranspose_smoothWeightedLaplacian`: `Δ_φ` is formally self-adjoint for the
  density `e^φ dV`.
* `TauCeti.isLaplaceType_neg_smoothWeightedLaplacian`: `-Δ_φ` is of Laplace type with
  constant `1`.
* `TauCeti.neg_smoothWeightedLaplacian_apply_eq`: the Bochner connection of `-Δ_φ` is
  `d + ½ ⟪grad φ, ·⟫`, with remainder `½ Δφ + ¼ ‖grad φ‖²`.
* `TauCeti.isMetricCompatible_trivialAddInner_iff_of_neg_smoothWeightedLaplacian_eq`: the
  Bochner connection of `-Δ_φ` is metric if and only if `dφ = 0`.
* `TauCeti.smoothWeightedLaplacian_real_apply`,
  `TauCeti.not_isMetricCompatible_trivialAddInner_of_neg_smoothWeightedLaplacian_sin_eq`: on the
  real line `Δ_φ f = f'' + φ' f'`, and for `φ = sin` the Bochner connection is not metric.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2, Lemma 2.1 and the paragraph following it.
* A. Grigor'yan, *Heat Kernel and Analysis on Manifolds*, AMS/IP Studies in Advanced
  Mathematics 47, 2009, §3.6 (weighted manifolds and the weighted Laplacian).
-/

public section

noncomputable section

open Bundle MeasureTheory TauCeti.Manifold CovariantDerivative
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### The weighted Laplacian -/

/-- The **weighted Laplacian** `Δ_φ f = Δ f + ⟪grad φ, grad f⟫` of the density `e^φ dV`, where
`Δ = div ∘ grad` is the Laplace–Beltrami operator. It equals `e^(-φ) div (e^φ grad f)`
(`TauCeti.exp_mul_smoothWeightedLaplacian_apply`) and is formally self-adjoint for `e^φ dV`
(`TauCeti.isFormalTranspose_smoothWeightedLaplacian`). -/
def smoothWeightedLaplacian (φ : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  smoothLaplaceBeltrami I M +
    (vectorFieldDerivation (smoothGradient I M φ) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯)

@[simp]
theorem smoothWeightedLaplacian_apply (φ f : C^∞⟮I, M; ℝ⟯) (x : M) :
    smoothWeightedLaplacian φ f x = laplaceBeltrami I f x + mvfderiv I f x (mgradient I φ x) := by
  simp [smoothWeightedLaplacian]

/-- For `φ = 0` the weighted Laplacian is the Laplace–Beltrami operator. -/
@[simp]
theorem smoothWeightedLaplacian_zero : smoothWeightedLaplacian (0 : C^∞⟮I, M; ℝ⟯) =
    smoothLaplaceBeltrami I M := by
  simp [smoothWeightedLaplacian]

/-- The weighted Laplacian differs from the Laplace–Beltrami operator by differentiation along the
gradient of the weight. -/
theorem smoothWeightedLaplacian_sub_smoothLaplaceBeltrami (φ : C^∞⟮I, M; ℝ⟯) :
    smoothWeightedLaplacian φ - smoothLaplaceBeltrami I M =
      (vectorFieldDerivation (smoothGradient I M φ) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) := by
  simp [smoothWeightedLaplacian]

/-- The weighted Laplacian is a differential operator of order at most two. -/
theorem smoothWeightedLaplacian_mem_differentialOperators_two (φ : C^∞⟮I, M; ℝ⟯) :
    smoothWeightedLaplacian φ ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 2 := by
  have hX := (vectorFieldDerivation (smoothGradient I M φ)).mem_differentialOperators_one
  exact add_mem smoothLaplaceBeltrami_mem_differentialOperators_two
    (differentialOperators_le_succ 1 hX)

/-- **The divergence form of the weighted Laplacian**: `e^φ Δ_φ f = div (e^φ grad f)`. -/
theorem exp_mul_smoothWeightedLaplacian_apply (φ f : C^∞⟮I, M; ℝ⟯) (x : M) :
    Real.exp (φ x) * smoothWeightedLaplacian φ f x =
      divergence I (fun y ↦ Real.exp (φ y) • mgradient I f y) x := by
  have hφ : MDifferentiableAt I 𝓘(ℝ) φ x := φ.contMDiff.mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ Real.exp (φ y)) x :=
    (ContDiff.comp_contMDiff Real.contDiff_exp φ.contMDiff).mdifferentiableAt (by simp)
  have hgrad := (contMDiff_mgradient_infty (I := I) f.contMDiff).mdifferentiableAt
    (x := x) (by simp)
  -- Write the vector field as a function times a vector field, the form of
  -- `divergence_smul_function`.
  have hX : (fun y ↦ Real.exp (φ y) • mgradient I f y) =
      (fun y ↦ Real.exp (φ y)) • mgradient I f :=
    rfl
  rw [hX, divergence_smul_function I _ _ x hρ hgrad, mvfderiv_exp hφ]
  simp only [smoothWeightedLaplacian_apply, laplaceBeltrami_def, smul_apply, smul_eq_mul]
  rw [← inner_mgradient_right (f := φ), inner_mgradient (f := f)]
  ring

variable [T2Space M]

/-- **The weighted Laplacian is of Laplace type**: `-Δ_φ` is of Laplace type with constant `1`. -/
theorem isLaplaceType_neg_smoothWeightedLaplacian (φ : C^∞⟮I, M; ℝ⟯) :
    IsLaplaceType
      (-⟨smoothWeightedLaplacian φ, smoothWeightedLaplacian_mem_differentialOperators_two φ⟩)
      1 := by
  have hX := (vectorFieldDerivation (smoothGradient I M φ)).mem_differentialOperators_one
  have h := isLaplaceType_neg_smoothLaplaceBeltrami.add_of_mem_differentialOperators_one
    (Q := -⟨_, differentialOperators_le_succ 1 hX⟩) (neg_mem hX)
  convert h using 1
  ext1
  simp only [NegMemClass.coe_neg, AddMemClass.coe_add, smoothWeightedLaplacian, neg_add]

/-! ### The Bochner connection -/

/-- **The Bochner connection of the weighted Laplacian.** With the connection
`∇ = d + ½ ⟪grad φ, ·⟫` on the trivial line bundle and the Levi-Civita connection on the tangent
bundle, `-Δ_φ f = ∇*∇ f + (½ Δφ + ¼ ‖grad φ‖²) f`. -/
theorem neg_smoothWeightedLaplacian_apply_eq (φ f : C^∞⟮I, M; ℝ⟯) (x : M) :
    -smoothWeightedLaplacian φ f x =
      (trivialAddInner ⇑((2⁻¹ : ℝ) • smoothGradient I M φ)).roughLaplacian
          (leviCivitaConnection I M) f x +
        (2⁻¹ * laplaceBeltrami I φ x + 4⁻¹ * ⟪mgradient I φ x, mgradient I φ x⟫) * f x := by
  have hgrad := (contMDiff_mgradient_infty (I := I) φ.contMDiff).mdifferentiableAt
    (x := x) (by simp)
  rw [roughLaplacian_trivialAddInner _ f.contMDiff, ContMDiffSection.coe_smul,
    coe_smoothGradient, divergence_smul I _ _ x hgrad]
  simp only [smoothWeightedLaplacian_apply, laplaceBeltrami_def I φ, Pi.smul_apply, map_smul,
    smul_eq_mul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

/-- **The Bochner connection of the weighted Laplacian is not metric.** If a connection
`∇ = d + ⟪Y, ·⟫` on the trivial line bundle, for a smooth vector field `Y`, and a smooth function
`V` satisfy `-Δ_φ f = ∇*∇ f + V f` for every smooth `f`, then `∇` is compatible with the standard
fibre metric if and only if `dφ = 0`. Indeed `Y = ½ grad φ` by the uniqueness of the Bochner
connection. So although `Δ_φ` is formally self-adjoint for the density `e^φ dV`
(`TauCeti.isFormalTranspose_smoothWeightedLaplacian`), its Bochner connection is metric only when
the density is a constant multiple of the Riemannian volume on each component. -/
theorem isMetricCompatible_trivialAddInner_iff_of_neg_smoothWeightedLaplacian_eq
    (φ : C^∞⟮I, M; ℝ⟯) (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (V : M → ℝ)
    (h : ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M), -smoothWeightedLaplacian φ f x =
      (trivialAddInner (Y : Π x : M, TangentSpace I x)).roughLaplacian
        (leviCivitaConnection I M) f x + V x * f x) :
    (trivialAddInner (Y : Π x : M, TangentSpace I x)).IsMetricCompatible ↔
      ∀ x, mvfderiv I φ x = 0 := by
  -- By uniqueness of the Bochner connection, `Y = ½ grad φ`.
  obtain ⟨hcov, -⟩ := eq_of_mul_roughLaplacian_add_mul_eq
    (trivialAddInner (Y : Π x : M, TangentSpace I x))
    (trivialAddInner ⇑((2⁻¹ : ℝ) • smoothGradient I M φ))
    one_ne_zero (V := V)
    (V' := fun x ↦ 2⁻¹ * laplaceBeltrami I φ x + 4⁻¹ * ⟪mgradient I φ x, mgradient I φ x⟫)
    fun f x ↦ by rw [one_mul, one_mul, ← h, neg_smoothWeightedLaplacian_apply_eq]
  have hY (x : M) : Y x = (2⁻¹ : ℝ) • mgradient I φ x := by
    have h1 := hcov 1 x mdifferentiableAt_const
    rw [trivialAddInner_one, trivialAddInner_one] at h1
    refine ext_inner_right ℝ fun v ↦ ?_
    have h2 := congrArg (fun L ↦ L v) h1
    simp only [innerSL_apply_apply] at h2
    rw [h2, ContMDiffSection.coe_smul, coe_smoothGradient, Pi.smul_apply]
  rw [isMetricCompatible_trivialAddInner_iff, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [hY, Pi.zero_apply, smul_eq_zero, ← mgradient_eq_zero_iff]
  simp

/-! ### Formal self-adjointness for the weighted density -/

section Integral

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance instIsContinuousRiemannianBundleTangentSpaceWeighted :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **The weighted Green identity.** For smooth functions `f` and `g`, one of which has compact
support, `∫ (Δ_φ f) g e^φ dV = -∫ ⟪grad f, grad g⟫ e^φ dV`. -/
theorem integral_smoothWeightedLaplacian_mul (φ f g : C^∞⟮I, M; ℝ⟯)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    ∫ x, smoothWeightedLaplacian φ f x * g x
        ∂((riemannianVolume I M).withDensity fun x ↦ ENNReal.ofReal (Real.exp (φ x))) =
      -∫ x, Real.exp (φ x) * ⟪mgradient I f x, mgradient I g x⟫ ∂riemannianVolume I M := by
  have hρm : Measurable fun x ↦ ENNReal.ofReal (Real.exp (φ x)) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp φ.contMDiff.continuous).measurable
  have hρt : ∀ᵐ x ∂riemannianVolume I M, ENNReal.ofReal (Real.exp (φ x)) < ⊤ :=
    .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hρm hρt]
  -- The integrand is `g div X` for the vector field `X = e^φ grad f`.
  set X : (x : M) → TangentSpace I x := fun y ↦ Real.exp (φ y) • mgradient I f y
  have hX : ContMDiff I I.tangent 1 (T% X) :=
    ((ContDiff.comp_contMDiff Real.contDiff_exp φ.contMDiff).smul_section
      (contMDiff_mgradient_infty (I := I) f.contMDiff)).of_le (by simp)
  have hpt (x : M) : (ENNReal.ofReal (Real.exp (φ x))).toReal •
      (smoothWeightedLaplacian φ f x * g x) = g x * divergence I X x := by
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← mul_assoc,
      exp_mul_smoothWeightedLaplacian_apply, mul_comm]
  have hg1 : ContMDiff I 𝓘(ℝ) 1 g := g.contMDiff.of_le (by simp)
  have hdiv : ∫ x, g x * divergence I X x ∂riemannianVolume I M =
      -∫ x, mvfderiv I g x (X x) ∂riemannianVolume I M := by
    rcases hfg with hf | hg
    · refine integral_mul_divergence_of_hasCompactSupport_right hg1 hX ?_
      exact (hf.mgradient I).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_smul_subset_right _ _)
    · exact integral_mul_divergence hg1 hg hX
  simp_rw [hpt]
  rw [hdiv]
  refine congrArg Neg.neg (integral_congr_ae (.of_forall fun x ↦ ?_))
  simp only [X, map_smul, smul_eq_mul, inner_mgradient_right]

/-- **The weighted Laplacian is formally self-adjoint** for the density `e^φ dV`:
`∫ (Δ_φ f) g e^φ dV = ∫ f (Δ_φ g) e^φ dV` whenever `f` or `g` has compact support. -/
theorem isFormalTranspose_smoothWeightedLaplacian (φ : C^∞⟮I, M; ℝ⟯) :
    (smoothWeightedLaplacian φ).IsFormalTranspose (smoothWeightedLaplacian φ)
      ((riemannianVolume I M).withDensity fun x ↦ ENNReal.ofReal (Real.exp (φ x))) := by
  rw [LinearMap.isFormalTranspose_iff]
  intro f g hfg
  simp_rw [mul_comm (f _)]
  rw [integral_smoothWeightedLaplacian_mul φ f g hfg,
    integral_smoothWeightedLaplacian_mul φ g f hfg.symm]
  simp_rw [real_inner_comm (mgradient I f _)]

end Integral

/-! ### The weighted line -/

section Line

/-- On the real line with its Euclidean metric, the weighted Laplacian is
`Δ_φ f = f'' + φ' f'`. -/
theorem smoothWeightedLaplacian_real_apply (φ f : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (x : ℝ) :
    smoothWeightedLaplacian φ f x = iteratedDeriv 2 f x + deriv φ x * deriv f x := by
  rw [smoothWeightedLaplacian_apply,
    laplaceBeltrami_eq_laplacian (f.contMDiff.contDiff.of_le (by simp)),
    InnerProductSpace.laplacian_eq_iteratedDeriv_real, mvfderiv_eq_fderiv_apply,
    mgradient_eq_gradient]
  simp [gradient_eq_deriv']

/-- On the real line, the weighted Laplacian `Δ_φ f = f'' + φ' f'` is formally self-adjoint for
the density `e^(φ x) dx`. -/
theorem isFormalTranspose_smoothWeightedLaplacian_real (φ : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) :
    (smoothWeightedLaplacian φ).IsFormalTranspose (smoothWeightedLaplacian φ)
      (volume.withDensity fun x ↦ ENNReal.ofReal (Real.exp (φ x))) := by
  simpa using isFormalTranspose_smoothWeightedLaplacian φ

/-- **A formally self-adjoint operator of Laplace type whose Bochner connection is not metric.**
On the real line take the weight `φ = sin`. The operator `-Δ_φ f = -f'' - cos x f'`
(`TauCeti.smoothWeightedLaplacian_real_apply`) is formally self-adjoint for the density
`e^(sin x) dx` (`TauCeti.isFormalTranspose_smoothWeightedLaplacian_real`), but no connection
`d + ⟪Y, ·⟫` absorbing its first-order part, `-Δ_φ = ∇*∇ + V`, is compatible with the standard
fibre metric. Its Bochner connection is `d + ½ cos x dx`
(`TauCeti.neg_smoothWeightedLaplacian_apply_eq`). -/
theorem not_isMetricCompatible_trivialAddInner_of_neg_smoothWeightedLaplacian_sin_eq
    (φ : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (hφ : ⇑φ = Real.sin)
    (Y : Cₛ^∞⟮𝓘(ℝ); ℝ, (TangentSpace 𝓘(ℝ) : ℝ → Type _)⟯) (V : ℝ → ℝ)
    (h : ∀ (f : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) (x : ℝ), -smoothWeightedLaplacian φ f x =
      (trivialAddInner (Y : Π x : ℝ, TangentSpace 𝓘(ℝ) x)).roughLaplacian
        (leviCivitaConnection 𝓘(ℝ) ℝ) f x + V x * f x) :
    ¬(trivialAddInner (Y : Π x : ℝ, TangentSpace 𝓘(ℝ) x)).IsMetricCompatible := by
  rw [isMetricCompatible_trivialAddInner_iff_of_neg_smoothWeightedLaplacian_eq φ Y V h]
  intro h0
  -- The derivative of `sin` at `0` is `cos 0 = 1`.
  have h1 := mgradient_eq_zero_iff.2 (h0 0)
  rw [mgradient_eq_gradient, gradient_eq_deriv', hφ, Real.deriv_sin, Real.cos_zero] at h1
  exact one_ne_zero (α := ℝ) h1

end Line

end TauCeti
