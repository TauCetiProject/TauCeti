/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

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
* `CovariantDerivative.contMDiff_innerCovariantDerivative`: `⟪∇σ, ∇τ⟫` is smooth for smooth
  sections.
-/

public section

open Bundle FiberBundle Riemannian.Tensor
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
  intro x
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hbase : (trivializationAt E (TangentSpace I) x).baseSet ∈ 𝓝 x :=
    (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds (by simp)
  have hframe (j) : CMDiffAt ∞ (T% (chartLocalFrame (I := I) x j)) x :=
    contMDiffAt_chartLocalFrame (I := I) (n := ∞) x j
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have hτ' : CMDiff (∞ + 1) (T% τ) := by simpa using hτ
  -- On the chart source, the metric trace is read off with the inverse Gram matrix.
  have heq : (fun y ↦ ∑ i, ∑ j, chartInvGramMatrix (I := I) x y i j *
      ⟪cov σ y (chartLocalFrame (I := I) x i y), cov τ y (chartLocalFrame (I := I) x j y)⟫)
      =ᶠ[𝓝 x] cov.innerCovariantDerivative σ τ := by
    filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
    simp only [innerCovariantDerivative_def, ContinuousLinearMap.hilbertSchmidtInner_def,
      bilinFormTrace_eq_sum_chartInvGramMatrix x hy, LinearMap.compl₁₂_apply, innerₗ_apply_apply,
      ContinuousLinearMap.coe_coe]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq.symm
  refine contMDiffAt_finsetSum fun i _ ↦ contMDiffAt_finsetSum fun j _ ↦ ?_
  exact ((contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) x i j).contMDiffAt hbase).mul
    ((cov.contMDiffAt_apply (hframe i) hσ').inner_bundle (cov.contMDiffAt_apply (hframe j) hτ'))

end CovariantDerivative
