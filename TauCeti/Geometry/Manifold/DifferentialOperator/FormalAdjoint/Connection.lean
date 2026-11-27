/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.DifferentialOperator
import TauCeti.Geometry.Manifold.MFDeriv.Exp
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

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
For the weighted density `e^φ dV` the formal adjoint acquires the extra term `-(X φ)`:
it is `-∇_X - (div X + X φ)`
(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField_withDensity_exp`).

When `X` is divergence-free, for instance a Killing field
(`TauCeti.Manifold.IsKillingField.divergence_eq_zero`), `∇_X` is formally skew-adjoint, and so
`∫ ⟪∇_X ∇_X σ, σ⟫ dV = -∫ ‖∇_X σ‖² dV` for compactly supported `σ`. If moreover `A` is a bundle
map which is skew-adjoint at every point and commutes with `∇_X`, then `A ∇_X` is formally
self-adjoint: `(A ∇_X)* = (∇_X)* A* = (-∇_X)(-A) = A ∇_X`. On a product `S¹ × Y` with the product
metric, the Dirac operator of a Clifford module splits as `D = c(T) ∇_T + B_T` along the parallel
unit field `T = ∂ₛ`, which is Killing
(`CovariantDerivative.IsMetricCompatible.isKillingField_of_forall_eq_zero`). Clifford
multiplication `c(T)` is skew-adjoint, and it commutes with `∇_T` when the connection is
compatible with Clifford multiplication, since `∇_T T = 0`. So the summand `c(T) ∇_T` of the
split Dirac operator is formally self-adjoint, and `-∇_T²` is a nonnegative operator; these are
the integrations by parts in the `T` direction behind the energy identity
`0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [S¹ × Y]⟩` for the unperturbed
Seiberg–Witten equations on `S¹ × Y`.

## Main results

* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField`,
  `CovariantDerivative.IsMetricCompatible.formalAdjoint_alongVectorField_apply`: the formal
  adjoint of `∇_X` for the Riemannian volume is `-∇_X - div X`.
* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField_withDensity_exp`: for
  the density `e^φ dV` it is `-∇_X - (div X + X φ)`.
* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField_neg`: along a
  divergence-free field, in particular along a Killing field, `∇_X` is formally skew-adjoint.
* `CovariantDerivative.IsMetricCompatible.integral_inner_alongVectorField_alongVectorField`:
  `∫ ⟪∇_X ∇_X σ, σ⟫ dV = -∫ ‖∇_X σ‖² dV` along a divergence-free field.
* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_comp_alongVectorField`: for a pointwise
  skew-adjoint bundle map `A` commuting with `∇_X`, `A ∇_X` is formally self-adjoint along a
  divergence-free field.

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

/-- **The formal adjoint of a covariant derivative along a vector field.** For a metric connection
`∇` on a Riemannian vector bundle over a Riemannian manifold without boundary, and a smooth vector
field `X`, an operator `Q` acting by `Q τ = -∇_X τ - (div X) τ` is the formal adjoint of `∇_X` with
respect to the Riemannian volume: `∫ ⟪∇_X σ, τ⟫ dV = ∫ ⟪σ, Q τ⟫ dV` whenever `σ` or `τ` has compact
support. -/
theorem IsMetricCompatible.isFormalAdjoint_alongVectorField (hcov : cov.IsMetricCompatible)
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hQ : ∀ τ x, Q τ x = -cov τ x (X x) - divergence I (fun y ↦ X y) x • τ x) :
    (cov.alongVectorField X).IsFormalAdjoint Q (riemannianVolume I M) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  refine LinearMap.isFormalAdjoint_iff.2 fun σ τ hστ ↦ ?_
  set μ := riemannianVolume I M
  set f : M → ℝ := fun x ↦ ⟪σ x, τ x⟫
  have hfc : HasCompactSupport f := ContMDiffSection.hasCompactSupport_inner hστ
  have hdiv := X.contMDiff_divergence
  have h₁ : Integrable (fun x ↦ ⟪cov.alongVectorField X σ x, τ x⟫) μ :=
    LinearMap.integrable_inner_apply_left (cov.tsupport_alongVectorField_apply_subset X) hστ
  have h₂ : Integrable (fun x ↦ ⟪σ x, cov.alongVectorField X τ x⟫) μ :=
    LinearMap.integrable_inner_apply_right (cov.tsupport_alongVectorField_apply_subset X) hστ
  have h₃ : Integrable (fun x ↦ f x * divergence I (fun y ↦ X y) x) μ :=
    ((ContMDiffSection.continuous_inner σ τ).mul hdiv.continuous).integrable_of_hasCompactSupport
      hfc.mul_right
  -- Metric compatibility and integration by parts against the divergence:
  -- `∫ ⟪∇_X σ, τ⟫ + ⟪σ, ∇_X τ⟫ = ∫ X ⟪σ, τ⟫ = -∫ ⟪σ, τ⟫ div X`.
  have hparts : ∫ x, ⟪cov.alongVectorField X σ x, τ x⟫ ∂μ +
      ∫ x, ⟪σ x, cov.alongVectorField X τ x⟫ ∂μ = -∫ x, f x * divergence I (fun y ↦ X y) x ∂μ := by
    rw [← integral_add h₁ h₂, integral_mul_divergence
      ((σ.contMDiff.inner_bundle τ.contMDiff).of_le (by simp)) hfc
      ((by simpa using X.contMDiff : ContMDiff I I.tangent ∞ (T% fun x ↦ X x)).of_le (by simp)),
      neg_neg]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [alongVectorField_apply]
    exact (hcov.mvfderiv_inner_eq (fun y ↦ X y) σ.mdifferentiableAt τ.mdifferentiableAt).symm
  calc ∫ x, ⟪cov.alongVectorField X σ x, τ x⟫ ∂μ =
        -∫ x, ⟪σ x, cov.alongVectorField X τ x⟫ ∂μ -
          ∫ x, f x * divergence I (fun y ↦ X y) x ∂μ := by
        linarith
    _ = ∫ x, (-⟪σ x, cov.alongVectorField X τ x⟫ - f x * divergence I (fun y ↦ X y) x) ∂μ := by
        have h := integral_sub h₂.neg h₃
        simp only [Pi.neg_apply, integral_neg] at h
        linarith
    _ = ∫ x, ⟪σ x, Q τ x⟫ ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [hQ, alongVectorField_apply, inner_sub_right, inner_neg_right,
          real_inner_smul_right, f]
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

/-- **The formal adjoint of `∇_X` for a weighted density.** For a metric connection on a
Riemannian vector bundle over a Riemannian manifold without boundary, a smooth vector field `X`
and a smooth function `φ`, an operator `Q` acting by `Q τ = -∇_X τ - (div X + X φ) τ` is the
formal adjoint of `∇_X` with respect to the density `e^φ dV`. -/
theorem IsMetricCompatible.isFormalAdjoint_alongVectorField_withDensity_exp
    (hcov : cov.IsMetricCompatible) (φ : C^∞⟮I, M; ℝ⟯) {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hQ : ∀ τ x, Q τ x =
      -cov τ x (X x) - (divergence I (fun y ↦ X y) x + mvfderiv I φ x (X x)) • τ x) :
    (cov.alongVectorField X).IsFormalAdjoint Q
      ((riemannianVolume I M).withDensity fun x ↦ ENNReal.ofReal (Real.exp (φ x))) := by
  -- The weight `e^φ`; `Real.exp ∘ φ` is by definition `fun y ↦ Real.exp (φ y)`.
  let ρ : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ Real.exp (φ y), Real.contDiff_exp.comp_contMDiff φ.contMDiff⟩
  have hρ : ⇑ρ = fun y ↦ Real.exp (φ y) := ContMDiffMap.coeFn_mk _ _
  let d : C^∞⟮I, M; ℝ⟯ := ⟨divergence I fun y ↦ X y, X.contMDiff_divergence⟩
  have hd : ⇑d = divergence I fun y ↦ X y := ContMDiffMap.coeFn_mk _ _
  -- The chain rule `X (e^φ) = e^φ X φ`.
  have hXρ (x : M) : mvfderiv I ρ x (X x) = ρ x * mvfderiv I φ x (X x) := by
    have hφ : MDifferentiableAt I 𝓘(ℝ) φ x := φ.contMDiff.mdifferentiableAt (by simp)
    rw [hρ, mvfderiv_exp hφ, _root_.smul_apply, smul_eq_mul]
  -- Change the density of the unweighted formal adjoint `-∇_X - div X`.
  refine (hcov.isFormalAdjoint_alongVectorField X
    (Q := -cov.alongVectorField X - Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ d) fun τ x ↦ by
      simp [hd]).withDensity (ρ := ρ) (fun x ↦ (Real.exp_pos _).le) fun τ ↦
    ContMDiffSection.ext fun x ↦ ?_
  simp only [ContMDiffSection.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    Algebra.lsmul_coe, ContMDiffSection.coe_sub, ContMDiffSection.coe_neg, Pi.sub_apply,
    Pi.neg_apply, alongVectorField_smul, hXρ]
  simp only [alongVectorField_apply, hQ, hd]
  module

/-- **`∇_X` is formally skew-adjoint along a divergence-free field.** For a metric connection on a
Riemannian vector bundle over a Riemannian manifold without boundary, and a smooth vector field
`X` with `div X = 0`, the formal adjoint of `∇_X` for the Riemannian volume is `-∇_X`. -/
theorem IsMetricCompatible.isFormalAdjoint_alongVectorField_neg (hcov : cov.IsMetricCompatible)
    (hX : ∀ x, divergence I (fun y ↦ X y) x = 0) :
    (cov.alongVectorField X).IsFormalAdjoint (-cov.alongVectorField X) (riemannianVolume I M) :=
  hcov.isFormalAdjoint_alongVectorField X fun τ x ↦ by simp [hX x]

/-- **The energy identity along a divergence-free field.** For a metric connection on a
Riemannian vector bundle over a Riemannian manifold without boundary, a smooth vector field `X`
with `div X = 0` and a compactly supported smooth section `σ`,
`∫ ⟪∇_X ∇_X σ, σ⟫ dV = -∫ ‖∇_X σ‖² dV`. -/
theorem IsMetricCompatible.integral_inner_alongVectorField_alongVectorField
    (hcov : cov.IsMetricCompatible) (hX : ∀ x, divergence I (fun y ↦ X y) x = 0)
    {σ : Cₛ^∞⟮I; F, V⟯} (hσ : IsCompact σ.tsupport) :
    ∫ x, ⟪cov.alongVectorField X (cov.alongVectorField X σ) x, σ x⟫ ∂riemannianVolume I M =
      -∫ x, ‖cov.alongVectorField X σ x‖ ^ 2 ∂riemannianVolume I M := by
  rw [(hcov.isFormalAdjoint_alongVectorField_neg X hX).integral_inner_eq (Or.inr hσ),
    ← integral_neg]
  simp

/-- **Formal self-adjointness of a skew-adjoint bundle map composed with `∇_X`.** Let `X` be a
smooth vector field with `div X = 0` and let `A` act on smooth sections by a bundle map `a`,
`(A s)(x) = a(x) (s x)`, which is skew-adjoint at every point and commutes with `∇_X`. Then, for a
metric connection on a Riemannian vector bundle over a Riemannian manifold without boundary,
`A ∇_X` is its own formal adjoint for the Riemannian volume. For Clifford multiplication
`A = c(T)` by a parallel unit field `T`, this is the formal self-adjointness of the summand
`c(T) ∇_T` of the split Dirac operator. -/
theorem IsMetricCompatible.isFormalAdjoint_comp_alongVectorField (hcov : cov.IsMetricCompatible)
    (hX : ∀ x, divergence I (fun y ↦ X y) x = 0) {A : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (a : Π x : M, V x →L[ℝ] V x) (hA : ∀ s x, A s x = a x (s x))
    (ha : ∀ x v w, ⟪a x v, w⟫ = -⟪v, a x w⟫)
    (hAX : ∀ s, cov.alongVectorField X (A s) = A (cov.alongVectorField X s)) :
    (A ∘ₗ cov.alongVectorField X).IsFormalAdjoint (A ∘ₗ cov.alongVectorField X)
      (riemannianVolume I M) := by
  -- `A` is pointwise skew-adjoint, so its formal adjoint is `-A`, which does not enlarge supports.
  have hAadj : A.IsFormalAdjoint (-A) (riemannianVolume I M) :=
    LinearMap.isFormalAdjoint_of_forall_inner_eq fun s t x ↦ by simp [hA, ha]
  have hAs (t : Cₛ^∞⟮I; F, V⟯) : ((-A) t).tsupport ⊆ t.tsupport := by
    simp only [ContMDiffSection.tsupport_def]
    exact closure_mono fun x hx h0 ↦ hx (by simp [hA, h0])
  have h := hAadj.comp (hcov.isFormalAdjoint_alongVectorField_neg X hX)
    (cov.tsupport_alongVectorField_apply_subset X) hAs
  -- The adjoint `(-∇_X) ∘ (-A) = ∇_X ∘ A` is `A ∘ ∇_X`, since `A` commutes with `∇_X`.
  convert h using 1
  ext s : 1
  simp [hAX]

end Adjoint

end CovariantDerivative
