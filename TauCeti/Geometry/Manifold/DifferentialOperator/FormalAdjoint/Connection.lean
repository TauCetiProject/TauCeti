/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.DifferentialOperator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The formal adjoint of a covariant derivative along a vector field

Let `∇` be a smooth connection on a vector bundle `V` over a smooth manifold `M`, and let `X` be a
smooth vector field. The covariant derivative along `X`, `∇_X σ = ∇σ(X)`
(`CovariantDerivative.alongVectorField`), is a first-order differential operator on the smooth
sections of `V` (`CovariantDerivative.alongVectorField_mem_differentialOperators_one`).

If `M` is a Riemannian manifold without boundary, `V` carries a smooth fibre metric and `∇` is
compatible with it, then with respect to the Riemannian volume `dV` the formal adjoint of `∇_X` is

`(∇_X)* = -∇_X - div X`

(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField`). Indeed metric
compatibility gives `X ⟪σ, τ⟫ = ⟪∇_X σ, τ⟫ + ⟪σ, ∇_X τ⟫`, and integrating by parts against the
divergence, `∫ X(f) dV = -∫ f div X dV` for compactly supported `f`
(`TauCeti.Manifold.integral_mul_divergence`), moves `∇_X` to the other side. For the trivial line
bundle with the flat connection this is the formula `-X - div X` for the formal transpose of a
vector field acting on functions. Merely negating `∇_X` is wrong unless `X` is divergence-free.

For an arbitrary smooth connection the same computation gives

`∫ ⟪∇_X σ, τ⟫ dV = -∫ ⟪σ, ∇_X τ + (div X) τ⟫ dV - ∫ T(σ, τ, X) dV`,

where `T(σ, τ, X) = X ⟪σ, τ⟫ - ⟪∇_X σ, τ⟫ - ⟪σ, ∇_X τ⟫` is the metric defect
(`CovariantDerivative.derivMetricTensor`). Hence the integration by parts characterizes metric
connections, and it suffices to know it for the gradient fields `X = grad f`, for which
`div X = Δ f`. Applied to `φ σ` for test functions `φ`, it gives `∫ φ T(σ, τ, grad f) dV = 0`, so
the continuous function `T(σ, τ, grad f)` vanishes; and every tangent vector is the value of the
gradient of a smooth function. This is how formal self-adjointness detects metric compatibility:
the commutator of `c ∇*∇ + P`, with `P` of order zero, with multiplication by `f` is
`-c (2 ∇_{grad f} + Δ f)`.

## Main results

* `CovariantDerivative.integral_inner_apply_eq_neg_integral_inner_sub_integral_derivMetricTensor`:
  integration by parts for `∇_X`, with the metric defect of `∇` as error term.
* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField`,
  `CovariantDerivative.IsMetricCompatible.formalAdjoint_alongVectorField_apply`: the formal
  adjoint of `∇_X` for the Riemannian volume is `-∇_X - div X`.
* `CovariantDerivative.isMetricCompatible_of_forall_integral_inner_apply_mgradient_eq`,
  `CovariantDerivative.isMetricCompatible_iff_forall_integral_inner_apply_mgradient_eq`: a smooth
  connection is metric if and only if `∫ ⟪∇_{grad f} σ, τ⟫ dV = -∫ ⟪σ, ∇_{grad f} τ + (Δ f) τ⟫ dV`
  for every smooth function `f` and all smooth sections `σ`, `τ` with `σ` compactly supported.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §8 (formal adjoints of connections and the connection Laplacian).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence theorem).
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

/-! ### The formal adjoint for the Riemannian volume -/

section Adjoint

variable [FiniteDimensional ℝ E] [T2Space M] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Integration by parts for a connection.** For a smooth connection `∇` on a Riemannian vector
bundle over a Riemannian manifold without boundary, and a smooth vector field `X`,

`∫ ⟪∇_X σ, τ⟫ dV = -∫ ⟪σ, ∇_X τ + (div X) τ⟫ dV - ∫ T(σ, τ, X) dV`

whenever `σ` or `τ` has compact support, where `T(σ, τ, X) = X ⟪σ, τ⟫ - ⟪∇_X σ, τ⟫ - ⟪σ, ∇_X τ⟫`
is the metric defect of `∇` (`CovariantDerivative.derivMetricTensor`). -/
theorem integral_inner_apply_eq_neg_integral_inner_sub_integral_derivMetricTensor
    {σ τ : Cₛ^∞⟮I; F, V⟯} (hστ : IsCompact σ.tsupport ∨ IsCompact τ.tsupport) :
    ∫ x, ⟪cov σ x (X x), τ x⟫ ∂riemannianVolume I M =
      -∫ x, ⟪σ x, cov τ x (X x) + divergence I (fun y ↦ X y) x • τ x⟫ ∂riemannianVolume I M -
        ∫ x, cov.derivMetricTensor x (σ x) (τ x) (X x) ∂riemannianVolume I M := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  set μ := riemannianVolume I M
  set f : M → ℝ := fun x ↦ ⟪σ x, τ x⟫
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := σ.contMDiff.inner_bundle τ.contMDiff
  have hfc : HasCompactSupport f := ContMDiffSection.hasCompactSupport_inner hστ
  have hdiv := X.contMDiff_divergence
  have hX : ContMDiff I I.tangent ∞ (T% fun x ↦ X x) := by simpa using X.contMDiff
  have h₀ : Integrable (fun x ↦ mvfderiv I f x (X x)) μ := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hf.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hX).continuous
      (hfc.mono' fun x hx ↦ ?_)
    by_contra hxf
    apply Function.mem_support.1 hx
    rw [Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ (0 : ℝ))
      (notMem_tsupport_iff_eventuallyEq.1 hxf), mvfderiv_const, zero_apply]
  have h₁ : Integrable (fun x ↦ ⟪cov.alongVectorField X σ x, τ x⟫) μ :=
    LinearMap.integrable_inner_apply_left (cov.tsupport_alongVectorField_apply_subset X) hστ
  have h₂ : Integrable (fun x ↦ ⟪σ x, cov.alongVectorField X τ x⟫) μ :=
    LinearMap.integrable_inner_apply_right (cov.tsupport_alongVectorField_apply_subset X) hστ
  have h₃ : Integrable (fun x ↦ f x * divergence I (fun y ↦ X y) x) μ :=
    (hf.continuous.mul hdiv.continuous).integrable_of_hasCompactSupport hfc.mul_right
  -- The defect is `X ⟪σ, τ⟫ - ⟪∇_X σ, τ⟫ - ⟪σ, ∇_X τ⟫`, and `∫ X ⟪σ, τ⟫ = -∫ ⟪σ, τ⟫ div X`.
  have hT : ∫ x, cov.derivMetricTensor x (σ x) (τ x) (X x) ∂μ =
      -∫ x, f x * divergence I (fun y ↦ X y) x ∂μ - ∫ x, ⟪cov.alongVectorField X σ x, τ x⟫ ∂μ -
        ∫ x, ⟪σ x, cov.alongVectorField X τ x⟫ ∂μ := by
    have e₁ := integral_sub (h₀.sub h₁) h₂
    simp only [Pi.sub_apply] at e₁
    rw [integral_mul_divergence (hf.of_le (by simp)) hfc (hX.of_le (by simp)), neg_neg,
      ← integral_sub h₀ h₁, ← e₁]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    beta_reduce
    rw [cov.derivMetricTensor_apply (X := fun y ↦ X y) x σ.mdifferentiableAt τ.mdifferentiableAt]
    simp [f]
  have hsplit : ∫ x, ⟪σ x, cov τ x (X x) + divergence I (fun y ↦ X y) x • τ x⟫ ∂μ =
      ∫ x, ⟪σ x, cov.alongVectorField X τ x⟫ ∂μ + ∫ x, f x * divergence I (fun y ↦ X y) x ∂μ := by
    rw [← integral_add h₂ h₃]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [alongVectorField_apply, inner_add_right, real_inner_smul_right, f]
    ring
  have hleft : ∫ x, ⟪cov σ x (X x), τ x⟫ ∂μ = ∫ x, ⟪cov.alongVectorField X σ x, τ x⟫ ∂μ := by
    simp only [alongVectorField_apply]
  rw [hT, hsplit, hleft]
  ring

/-- **The formal adjoint of a covariant derivative along a vector field.** For a metric connection
`∇` on a Riemannian vector bundle over a Riemannian manifold without boundary, and a smooth vector
field `X`, an operator `Q` acting by `Q τ = -∇_X τ - (div X) τ` is the formal adjoint of `∇_X` with
respect to the Riemannian volume: `∫ ⟪∇_X σ, τ⟫ dV = ∫ ⟪σ, Q τ⟫ dV` whenever `σ` or `τ` has compact
support. -/
theorem IsMetricCompatible.isFormalAdjoint_alongVectorField (hcov : cov.IsMetricCompatible)
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hQ : ∀ τ x, Q τ x = -cov τ x (X x) - divergence I (fun y ↦ X y) x • τ x) :
    (cov.alongVectorField X).IsFormalAdjoint Q (riemannianVolume I M) := by
  refine LinearMap.isFormalAdjoint_iff.2 fun σ τ hστ ↦ ?_
  have h := integral_inner_apply_eq_neg_integral_inner_sub_integral_derivMetricTensor (cov := cov) X
    hστ
  simp only [isMetricCompatible_iff_derivMetricTensor_eq_zero.1 hcov, zero_apply, integral_zero,
    sub_zero, ← integral_neg] at h
  simp only [alongVectorField_apply, h, hQ]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [inner_add_right, inner_sub_right, inner_neg_right]
  ring

/-- **The formal adjoint of a covariant derivative along a vector field.** For a metric connection
on a Riemannian vector bundle over a Riemannian manifold without boundary, the formal adjoint of
`∇_X` with respect to the Riemannian volume is `-∇_X - div X`. -/
theorem IsMetricCompatible.formalAdjoint_alongVectorField_apply (hcov : cov.IsMetricCompatible)
    (τ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (cov.alongVectorField X).formalAdjoint (riemannianVolume I M) τ x =
      -cov τ x (X x) - divergence I (fun y ↦ X y) x • τ x := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  let d : C^∞⟮I, M; ℝ⟯ := ⟨divergence I fun y ↦ X y, X.contMDiff_divergence⟩
  have hd : ⇑d = divergence I fun y ↦ X y := ContMDiffMap.coeFn_mk _ _
  have h := hcov.isFormalAdjoint_alongVectorField X
    (Q := -cov.alongVectorField X - Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ d) fun τ x ↦ by simp [hd]
  rw [h.formalAdjoint_eq]
  simp [hd]


/-! ### Metric compatibility from integration by parts -/

/-- **Integration by parts detects metric connections.** If a smooth connection `∇` on a
Riemannian bundle over a manifold without boundary satisfies
`∫ ⟪∇_{grad f} σ, τ⟫ dV = -∫ ⟪σ, ∇_{grad f} τ + (Δ f) τ⟫ dV` for every smooth function `f` and
all smooth sections `σ`, `τ` with `σ` compactly supported, then `∇` is compatible with the fibre
metric. -/
theorem isMetricCompatible_of_forall_integral_inner_apply_mgradient_eq
    (h : ∀ (f : C^∞⟮I, M; ℝ⟯) (σ τ : Cₛ^∞⟮I; F, V⟯), IsCompact σ.tsupport →
      ∫ x, ⟪cov σ x (mgradient I f x), τ x⟫ ∂riemannianVolume I M =
        -∫ x, ⟪σ x, cov τ x (mgradient I f x) + laplaceBeltrami I f x • τ x⟫
          ∂riemannianVolume I M) :
    cov.IsMetricCompatible := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  -- Evaluate the defect tensor on smooth extensions and on a gradient field.
  refine isMetricCompatible_iff_derivMetricTensor_eq_zero.2 (funext fun x ↦ ?_)
  ext σ₀ τ₀ X₀
  obtain ⟨f, -, hfx⟩ := TauCeti.exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (innerSL ℝ X₀)
  have hgrad : mgradient I f x = X₀ := by
    refine (eq_mgradient_iff.2 fun v ↦ ?_).symm
    rw [hfx, innerSL_apply_apply]
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x σ₀
  obtain ⟨τ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x τ₀
  let Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨mgradient I (f : M → ℝ), contMDiff_mgradient_infty f.contMDiff⟩
  have hΔ (y : M) : divergence I (fun z ↦ mgradient I f z) y = laplaceBeltrami I f y :=
    (laplaceBeltrami_def I _ y).symm
  -- The defect `g = T(σ, τ, grad f)` is continuous, since `T` is the tensor
  -- `X ⟪σ, τ⟫ - ⟪∇_X σ, τ⟫ - ⟪σ, ∇_X τ⟫`.
  set g : M → ℝ := fun y ↦ cov.derivMetricTensor y (σ y) (τ y) (Y y)
  have hg : Continuous g := by
    refine ((((σ.contMDiff.inner_bundle τ.contMDiff).contMDiff_mvfderiv_apply (m := ∞)
      (by simp)).comp Y.contMDiff).continuous.sub
      (ContMDiffSection.continuous_inner (cov.alongVectorField Y σ) τ) |>.sub
      (ContMDiffSection.continuous_inner σ (cov.alongVectorField Y τ))).congr fun y ↦ ?_
    simp only [g, cov.derivMetricTensor_apply (X := fun z ↦ Y z) y σ.mdifferentiableAt
      τ.mdifferentiableAt, Pi.sub_apply, Function.comp_apply, alongVectorField_apply]
  -- Comparing the hypothesis for `φ σ` with the integration by parts identity, `∫ φ g dV = 0`.
  have hae : ∀ᵐ y ∂riemannianVolume I M, g y = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hg.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    let ψ : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have hs : IsCompact (ψ • σ).tsupport := ContMDiffSection.mem_compactlySupported.1 <|
      ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport ψ hφc σ
    have h₁ := integral_inner_apply_eq_neg_integral_inner_sub_integral_derivMetricTensor
      (cov := cov) Y (τ := τ) (.inl hs)
    simp only [show ∀ y, Y y = mgradient I f y from fun _ ↦ rfl] at h₁
    simp only [hΔ] at h₁
    have h₂ := h f (ψ • σ) τ hs
    have hT : ∫ y, cov.derivMetricTensor y ((ψ • σ) y) (τ y) (mgradient I f y)
        ∂riemannianVolume I M = 0 := by
      linarith
    rw [← hT]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    beta_reduce
    rw [ContMDiffSection.smul_apply, map_smul, smul_apply, smul_apply]
    rfl
  have hgx := congr_fun ((hg.ae_eq_iff_eq _ continuous_const).1 hae) x
  have hYx : Y x = X₀ := hgrad
  simp only [g, hYx] at hgx
  simpa [ContMDiffSection.evalLinearMap_apply] using hgx

/-- **Metric connections are characterized by integration by parts.** A smooth connection on a
Riemannian bundle over a manifold without boundary is compatible with the fibre metric if and only
if `∫ ⟪∇_{grad f} σ, τ⟫ dV = -∫ ⟪σ, ∇_{grad f} τ + (Δ f) τ⟫ dV` for every smooth function `f`
and all smooth sections `σ`, `τ` with `σ` compactly supported. -/
theorem isMetricCompatible_iff_forall_integral_inner_apply_mgradient_eq :
    cov.IsMetricCompatible ↔ ∀ (f : C^∞⟮I, M; ℝ⟯) (σ τ : Cₛ^∞⟮I; F, V⟯), IsCompact σ.tsupport →
      ∫ x, ⟪cov σ x (mgradient I f x), τ x⟫ ∂riemannianVolume I M =
        -∫ x, ⟪σ x, cov τ x (mgradient I f x) + laplaceBeltrami I f x • τ x⟫
          ∂riemannianVolume I M := by
  refine ⟨fun hcov f σ τ hσ ↦ ?_, isMetricCompatible_of_forall_integral_inner_apply_mgradient_eq⟩
  have h := integral_inner_apply_eq_neg_integral_inner_sub_integral_derivMetricTensor (cov := cov)
    ⟨mgradient I (f : M → ℝ), contMDiff_mgradient_infty f.contMDiff⟩ (τ := τ) (.inl hσ)
  simpa [isMetricCompatible_iff_derivMetricTensor_eq_zero.1 hcov, ← laplaceBeltrami_def] using h

end Adjoint

end CovariantDerivative
