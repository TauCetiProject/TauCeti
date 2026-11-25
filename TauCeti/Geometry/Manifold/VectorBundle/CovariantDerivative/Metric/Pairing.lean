/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.HilbertSchmidt
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The pointwise inner product of covariant derivatives

For a covariant derivative `∇` on a Riemannian vector bundle `V` over a Riemannian manifold, this
file defines the pointwise inner product

`⟪∇σ, ∇τ⟫ = ∑ᵢ ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫`

of the covariant derivatives of two sections, for any orthonormal basis `eᵢ` of the tangent
space. It is the Hilbert–Schmidt inner product `ContinuousLinearMap.hilbertSchmidtInner` of
`∇σ` and `∇τ` at each point, so it does not depend on a basis, and `⟪∇σ, ∇σ⟫ = |∇σ|²`. For
smooth sections of a smooth bundle with a smooth connection it is a smooth function, read off in
a chart with the inverse Gram matrix of the chart frame.

## Main results

* `CovariantDerivative.innerCovariantDerivative`: the pointwise inner product `⟪∇σ, ∇τ⟫`.
* `CovariantDerivative.innerCovariantDerivative_eq_zero_of_notMem_closure_left` and
  `CovariantDerivative.innerCovariantDerivative_eq_zero_of_notMem_closure_right`: `⟪∇σ, ∇τ⟫`
  vanishes off the closure of the nonzero locus of `σ`, and of `τ`.
* `CovariantDerivative.innerCovariantDerivative_self_eq_zero_iff`: `⟪∇σ, ∇σ⟫` vanishes exactly
  where `∇σ` does.
* `CovariantDerivative.norm_le_sqrt_innerCovariantDerivative`: the operator norm of `∇σ` is at
  most its Hilbert–Schmidt norm.
* `CovariantDerivative.norm_apply_le_sqrt_innerCovariantDerivative` and
  `CovariantDerivative.norm_apply_orthonormalBasis_le_sqrt_innerCovariantDerivative`: the
  covariant derivative of `σ` in a direction is bounded by the Hilbert–Schmidt norm of `∇σ`.
* `CovariantDerivative.contMDiff_innerCovariantDerivative`: `⟪∇σ, ∇τ⟫` is smooth for smooth
  sections.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V]
  (cov : CovariantDerivative I F V) {σ τ : Π x : M, V x}

/-- The pointwise inner product `⟪∇σ, ∇τ⟫ = ∑ᵢ ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫` of the covariant
derivatives of two sections at `x`, for any orthonormal basis `eᵢ` of the tangent space
(`CovariantDerivative.innerCovariantDerivative_eq_sum`): the Hilbert–Schmidt inner product of
`∇σ` and `∇τ` at `x`. It is the inner product of `∇σ` and `∇τ` as sections of `T*M ⊗ V`, and
`⟪∇σ, ∇σ⟫ = |∇σ|²` is the squared Hilbert–Schmidt norm of `∇σ` at `x`. -/
def innerCovariantDerivative (σ τ : Π x : M, V x) (x : M) : ℝ :=
  (cov σ x).hilbertSchmidtInner (cov τ x)

/-- The inner product of covariant derivatives is the Hilbert–Schmidt inner product of `∇σ` and
`∇τ`. -/
theorem innerCovariantDerivative_def (σ τ : Π x : M, V x) (x : M) :
    cov.innerCovariantDerivative σ τ x = (cov σ x).hilbertSchmidtInner (cov τ x) :=
  (rfl)

/-- The inner product of covariant derivatives in an orthonormal basis:
`⟪∇σ, ∇τ⟫ = ∑ᵢ ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫`. -/
theorem innerCovariantDerivative_eq_sum (σ τ : Π x : M, V x) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.innerCovariantDerivative σ τ x = ∑ i, ⟪cov σ x (b i), cov τ x (b i)⟫ :=
  (cov σ x).hilbertSchmidtInner_eq_sum _ b

/-- The inner product of covariant derivatives is symmetric: `⟪∇σ, ∇τ⟫ = ⟪∇τ, ∇σ⟫`. -/
theorem innerCovariantDerivative_comm (σ τ : Π x : M, V x) (x : M) :
    cov.innerCovariantDerivative σ τ x = cov.innerCovariantDerivative τ σ x :=
  (cov σ x).hilbertSchmidtInner_comm _

/-- `⟪∇σ, ∇σ⟫ = |∇σ|²` is nonnegative. -/
theorem innerCovariantDerivative_self_nonneg (σ : Π x : M, V x) (x : M) :
    0 ≤ cov.innerCovariantDerivative σ σ x :=
  (cov σ x).hilbertSchmidtInner_self_nonneg

/-- `⟪∇σ, ∇σ⟫` vanishes at `x` exactly when the covariant derivative of `σ` vanishes at `x`. -/
@[simp]
theorem innerCovariantDerivative_self_eq_zero_iff (σ : Π x : M, V x) (x : M) :
    cov.innerCovariantDerivative σ σ x = 0 ↔ cov σ x = 0 :=
  (cov σ x).hilbertSchmidtInner_self_eq_zero_iff

/-- The operator norm of `∇σ` at `x` is at most its Hilbert–Schmidt norm `√⟪∇σ, ∇σ⟫`. -/
theorem norm_le_sqrt_innerCovariantDerivative (σ : Π x : M, V x) (x : M) :
    ‖cov σ x‖ ≤ √(cov.innerCovariantDerivative σ σ x) := by
  refine (Real.le_sqrt (norm_nonneg (cov σ x)) (cov.innerCovariantDerivative_self_nonneg σ x)).2 ?_
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [cov.innerCovariantDerivative_eq_sum σ σ x b]
  simpa only [real_inner_self_eq_norm_sq] using
    (cov σ x).opNorm_sq_le_sum_norm_apply_sq_orthonormalBasis b

/-- The covariant derivative of `σ` in the direction `v` is bounded by the Hilbert–Schmidt norm:
`‖∇_v σ‖ ≤ √⟪∇σ, ∇σ⟫ ‖v‖`. -/
theorem norm_apply_le_sqrt_innerCovariantDerivative (σ : Π x : M, V x) (x : M)
    (v : TangentSpace I x) :
    ‖cov σ x v‖ ≤ √(cov.innerCovariantDerivative σ σ x) * ‖v‖ :=
  (cov σ x).le_of_opNorm_le (cov.norm_le_sqrt_innerCovariantDerivative σ x) v

/-- The covariant derivative of `σ` along a vector of an orthonormal basis is bounded by the
Hilbert–Schmidt norm: `‖∇_{eᵢ} σ‖ ≤ √⟪∇σ, ∇σ⟫`. -/
theorem norm_apply_orthonormalBasis_le_sqrt_innerCovariantDerivative (σ : Π x : M, V x) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (i : ι) :
    ‖cov σ x (b i)‖ ≤ √(cov.innerCovariantDerivative σ σ x) := by
  simpa only [b.orthonormal.1 i, mul_one] using
    cov.norm_apply_le_sqrt_innerCovariantDerivative σ x (b i)

/-- `⟪∇σ, ∇τ⟫` vanishes where `∇σ` does. -/
theorem innerCovariantDerivative_eq_zero_of_apply_eq_zero_left {x : M} (h : cov σ x = 0) :
    cov.innerCovariantDerivative σ τ x = 0 := by
  simp [innerCovariantDerivative_def, h]

/-- `⟪∇σ, ∇τ⟫` vanishes where `∇τ` does. -/
theorem innerCovariantDerivative_eq_zero_of_apply_eq_zero_right {x : M} (h : cov τ x = 0) :
    cov.innerCovariantDerivative σ τ x = 0 := by
  simp [innerCovariantDerivative_def, h]

variable [VectorBundle ℝ F V]

/-- `⟪∇σ, ∇τ⟫` vanishes off the closure of the nonzero locus of `σ`. -/
theorem innerCovariantDerivative_eq_zero_of_notMem_closure_left {x : M}
    (hx : x ∉ closure {y | σ y ≠ 0}) : cov.innerCovariantDerivative σ τ x = 0 :=
  cov.innerCovariantDerivative_eq_zero_of_apply_eq_zero_left
    (cov.apply_eq_zero_of_notMem_closure hx)

/-- `⟪∇σ, ∇τ⟫` vanishes off the closure of the nonzero locus of `τ`. -/
theorem innerCovariantDerivative_eq_zero_of_notMem_closure_right {x : M}
    (hx : x ∉ closure {y | τ y ≠ 0}) : cov.innerCovariantDerivative σ τ x = 0 :=
  cov.innerCovariantDerivative_eq_zero_of_apply_eq_zero_right
    (cov.apply_eq_zero_of_notMem_closure hx)

variable [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ F V] [ContMDiffCovariantDerivative cov ∞]

/-- The inner product `⟪∇σ, ∇τ⟫` of the covariant derivatives of two smooth sections is a smooth
function. -/
theorem contMDiff_innerCovariantDerivative (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) :
    ContMDiff I 𝓘(ℝ) ∞ (cov.innerCovariantDerivative σ τ) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)).hilbertSchmidtInner_bundle
    (cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hτ))

end CovariantDerivative
