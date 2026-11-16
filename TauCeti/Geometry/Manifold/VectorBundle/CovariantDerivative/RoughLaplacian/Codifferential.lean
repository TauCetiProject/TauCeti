/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import TauCeti.Analysis.InnerProductSpace.CanonicalTensor
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The covariant codifferential on bundle-valued one-forms and coordinate formulas for `∇*∇`

Let `∇` be a connection on a vector bundle `V` over a Riemannian manifold `M`, and `∇ᵀ` a
connection on the tangent bundle. Together they induce the connection `∇ᵀ.hom ∇` on the bundle
`Hom(TM, V)` of `V`-valued one-forms (`CovariantDerivative.hom`). The **covariant codifferential**
of a `V`-valued one-form `η : Π x, TangentSpace I x →L[ℝ] V x` is the negative metric trace of its
covariant derivative,

`∇* η = -tr_g (∇^{Hom} η) = -∑ᵢ (∇_{eᵢ} η)(eᵢ)`,

defined basis-independently by contracting `∇^{Hom} η` against
`InnerProductSpace.canonicalCovariantTensor`. Because `∇²σ = ∇^{Hom} (∇σ)` on smooth sections
(`CovariantDerivative.secondCovariantDerivative_eq_hom_apply`), composing `∇*` with `∇` recovers the
rough Laplacian `CovariantDerivative.roughLaplacian` on the nose:

`∇* (∇σ) = ∇*∇ σ`.

When `∇` is compatible with a fiber metric on `V` and `∇ᵀ` is the Levi-Civita connection,
`CovariantDerivative.RoughLaplacian.Energy` proves that `∇*` is the formal `L²` adjoint of `∇`
against the orientation-free Riemannian volume measure `TauCeti.riemannianVolume`.

This file also compares the intrinsic trace definitions of `∇*` and `∇*∇` with their two local
coordinate expressions on a chart domain `(chartAt H α).source` with chart frame `eᵢ`, dual frame
`eᵢ♯ = ∑ⱼ gⁱʲ eⱼ`, and Riemannian volume density `ρ = √det g`:

* **Inverse-Gram trace formula** (for any tangent connection `∇ᵀ`):
  `∇* η = -∑ᵢ ∑ⱼ gⁱʲ (∇_{eᵢ} η)(eⱼ)` and `∇*∇ σ = -∑ᵢ ∑ⱼ gⁱʲ ∇²σ(eᵢ, eⱼ)`.
* **Volume-density divergence formula** (when `∇ᵀ` is the Levi-Civita connection):
  `ρ (∇* η) = -∑ₖ ∇_{eₖ} (ρ η(eₖ♯))` and `ρ (∇*∇ σ) = -∑ₖ ∇_{eₖ} (ρ ∇_{eₖ♯} σ)`.

Finally, for smooth connections, `∇`, `∇*`, and `∇*∇` are bundled as real-linear maps on
`ContMDiffSection`, shown to preserve closed and compact supports, and placed in Grothendieck's
order filtration `TauCeti.differentialOperators` (`∇` and `∇*` of order at most `1`, `∇*∇ = ∇* ∘ ∇`
of order at most `2`).

## Main definitions

* `CovariantDerivative.codifferential`: the covariant codifferential `∇* η` at a point.
* `CovariantDerivative.smoothCovariantDerivative`,
  `CovariantDerivative.smoothCodifferential`, and
  `CovariantDerivative.smoothRoughLaplacian`: `∇`, `∇*`, and `∇*∇` as linear maps on smooth
  sections.

## Main results

* `CovariantDerivative.codifferential_eq_sum`: `∇* η = -∑ᵢ (∇_{eᵢ} η)(eᵢ)` in an orthonormal basis.
* `CovariantDerivative.codifferential_covariantDerivative` and
  `CovariantDerivative.smoothCodifferential_comp_smoothCovariantDerivative`: `∇* (∇σ) = ∇*∇ σ`.
* `CovariantDerivative.codifferential_smul`: `∇* (f • η) = f • ∇* η - η (grad f)`.
* `CovariantDerivative.codifferential_eq_sum_chartInvGramMatrix` and
  `CovariantDerivative.roughLaplacian_eq_sum_chartInvGramMatrix`: local `gⁱʲ` trace formulas.
* `CovariantDerivative.chartVolumeDensity_smul_codifferential` and
  `CovariantDerivative.chartVolumeDensity_smul_roughLaplacian`: local divergence-form coordinate
  expressions weighted by `ρ = √det g`.
* `CovariantDerivative.contMDiff_codifferential` and `CovariantDerivative.contMDiff_roughLaplacian`:
  smoothness of `∇* η` and `∇*∇ σ`.
* `CovariantDerivative.smoothCovariantDerivative_mem_differentialOperators_one`,
  `CovariantDerivative.smoothCodifferential_mem_differentialOperators_one`, and
  `CovariantDerivative.smoothRoughLaplacian_mem_differentialOperators_two`: placement in
  `TauCeti.differentialOperators`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (Proposition 2.5, formal adjoint of a connection and generalized Laplacians).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 2
  and 4.
-/

public section

open Bundle FiberBundle Riemannian.Tensor Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V)
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The **covariant codifferential** `∇* η = -tr_g (∇^{Hom} η)` of a `V`-valued one-form `η` at `x`:
the negative metric trace of its covariant derivative in `Hom(TM, V)` induced by `covT` and `cov`.
In any orthonormal basis `eᵢ` of `TangentSpace I x` it equals `-∑ᵢ (covT.hom cov η x (eᵢ)) eᵢ`
(`codifferential_eq_sum`). At a point where `η` is not differentiable it vanishes. -/
def codifferential (η : Π y : M, TangentSpace I y →L[ℝ] V y) (x : M) : V x :=
  -TensorProduct.lift (covT.hom cov η x).toLinearMap₁₂
    (InnerProductSpace.canonicalCovariantTensor (TangentSpace I x))

/-- The covariant codifferential in an orthonormal basis: `∇* η = -∑ᵢ (∇_{eᵢ} η)(eᵢ)`. -/
theorem codifferential_eq_sum (η : Π y : M, TangentSpace I y →L[ℝ] V y) (x : M) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.codifferential covT η x = -∑ i, covT.hom cov η x (b i) (b i) := by
  rw [codifferential, TensorProduct.lift_canonicalCovariantTensor_eq_sum _ b]
  rfl

/-- At a point where `η` is not differentiable, `cov.codifferential covT η x = 0`. -/
@[simp]
theorem codifferential_of_not_mdifferentiableAt {η : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (hη : ¬MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)) x) :
    cov.codifferential covT η x = 0 := by
  simp [codifferential_eq_sum cov covT _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    hom_eq_zero_of_not_mdifferentiableAt covT cov hη]

/-- The covariant codifferential of the zero one-form is zero. -/
@[simp]
theorem codifferential_zero (x : M) :
    cov.codifferential covT (0 : Π y : M, TangentSpace I y →L[ℝ] V y) x = 0 := by
  have h0 : covT.hom cov (0 : Π y : M, TangentSpace I y →L[ℝ] V y) x = 0 :=
    (covT.hom cov).isCovariantDerivativeOnUniv.zero
  simp [codifferential_eq_sum cov covT _ x (stdOrthonormalBasis ℝ (TangentSpace I x)), h0]

/-- The covariant codifferential is additive on one-forms differentiable at `x`. -/
theorem codifferential_add {η₁ η₂ : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (hη₁ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₁ y)) x)
    (hη₂ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₂ y)) x) :
    cov.codifferential covT (η₁ + η₂) x =
      cov.codifferential covT η₁ x + cov.codifferential covT η₂ x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  simp only [codifferential_eq_sum cov covT _ x b,
    (covT.hom cov).isCovariantDerivativeOnUniv.add hη₁ hη₂, add_apply, Finset.sum_add_distrib,
    neg_add_rev]
  abel

/-- The covariant codifferential commutes with multiplication by a constant scalar. -/
@[simp]
theorem codifferential_const_smul (c : ℝ) (η : Π y : M, TangentSpace I y →L[ℝ] V y) (x : M) :
    cov.codifferential covT (c • η) x = c • cov.codifferential covT η x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases hη : MDiffAt
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)) x
    · let b := stdOrthonormalBasis ℝ (TangentSpace I x)
      simp only [codifferential_eq_sum cov covT _ x b,
        (covT.hom cov).isCovariantDerivativeOnUniv.smul_const c hη, smul_apply,
        ← Finset.smul_sum, smul_neg]
    · have hcη : ¬MDiffAt (fun y ↦
          TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y ((c • η) y)) x :=
        fun h ↦ hη <| by
          simpa [smul_smul, inv_mul_cancel₀ hc] using
            (mdifferentiableAt_const (I := I) (c := c⁻¹)).smul_section h
      simp [codifferential_of_not_mdifferentiableAt cov covT hη,
        codifferential_of_not_mdifferentiableAt cov covT hcη]

/-- The covariant codifferential commutes with negation. -/
@[simp]
theorem codifferential_neg (η : Π y : M, TangentSpace I y →L[ℝ] V y) (x : M) :
    cov.codifferential covT (-η) x = -cov.codifferential covT η x := by
  rw [← neg_one_smul ℝ η, codifferential_const_smul, neg_one_smul]

/-- The covariant codifferential commutes with subtraction on one-forms differentiable at `x`. -/
theorem codifferential_sub {η₁ η₂ : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (hη₁ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₁ y)) x)
    (hη₂ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₂ y)) x) :
    cov.codifferential covT (η₁ - η₂) x =
      cov.codifferential covT η₁ x - cov.codifferential covT η₂ x := by
  rw [sub_eq_add_neg, codifferential_add cov covT hη₁ (mdifferentiableAt_neg_section hη₂),
    codifferential_neg, ← sub_eq_add_neg]

/-- **Locality of the covariant codifferential.** One-forms with the same germ at `x` have the same
codifferential at `x`. -/
theorem codifferential_congr_of_eventuallyEq {η₁ η₂ : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (h : ∀ᶠ y in 𝓝 x, η₁ y = η₂ y) :
    cov.codifferential covT η₁ x = cov.codifferential covT η₂ x := by
  have htot : (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y
      (η₁ y)) =ᶠ[𝓝 x]
      fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₂ y) :=
    h.mono fun y hy ↦ congrArg (TotalSpace.mk' (E →L[ℝ] F) y) hy
  by_cases hη₁ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₁ y)) x
  · have hη₂ := htot.mdifferentiableAt_iff.mp hη₁
    rw [codifferential, codifferential,
      (covT.hom cov).isCovariantDerivativeOnUniv.congr_of_eventuallyEq hη₁ hη₂ Filter.univ_mem h]
  · have hη₂ : ¬MDiffAt (fun y ↦
        TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₂ y)) x :=
      fun h₂ ↦ hη₁ (htot.mdifferentiableAt_iff.mpr h₂)
    simp [codifferential_of_not_mdifferentiableAt cov covT hη₁,
      codifferential_of_not_mdifferentiableAt cov covT hη₂]

/-- The covariant codifferential vanishes outside the closed support of `η`. -/
theorem codifferential_eq_zero_of_notMem_closure {η : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (hx : x ∉ closure {y | η y ≠ 0}) :
    cov.codifferential covT η x = 0 := by
  have hzero : ∀ᶠ y in 𝓝 x, η y = (0 : Π z : M, TangentSpace I z →L[ℝ] V z) y := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_closure hne)
  rw [codifferential_congr_of_eventuallyEq cov covT hzero, codifferential_zero]

/-- **Leibniz rule for the covariant codifferential.** For `f` and `η` differentiable at `x`,
`∇* (f • η) = f • ∇* η - η (grad f)`. -/
theorem codifferential_smul {f : M → ℝ} {η : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (hf : MDiffAt f x)
    (hη : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)) x) :
    cov.codifferential covT (f • η) x =
      f x • cov.codifferential covT η x - η x (TauCeti.Manifold.mgradient I f x) := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hleib (i) : covT.hom cov (f • η) x (b i) (b i) =
      f x • covT.hom cov η x (b i) (b i) + d% f x (b i) • η x (b i) := by
    rw [(covT.hom cov).isCovariantDerivativeOnUniv.leibniz hη hf]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have hgrad : ∑ i, d% f x (b i) • η x (b i) = η x (TauCeti.Manifold.mgradient I f x) := by
    conv_rhs => rw [← b.sum_repr' (TauCeti.Manifold.mgradient I f x)]
    simp only [map_sum, map_smul, TauCeti.Manifold.inner_mgradient_right]
  rw [codifferential_eq_sum cov covT _ x b, codifferential_eq_sum cov covT _ x b]
  simp only [hleib, Finset.sum_add_distrib, ← Finset.smul_sum, hgrad, smul_neg, neg_add_rev]
  abel

/-! ### Local chart-frame formulas -/

/-- **Local inverse-Gram formula for the covariant codifferential.** On the domain of the chart at
`α`, `∇* η = -∑ᵢ ∑ⱼ gⁱʲ (∇_{eᵢ} η)(eⱼ)` in the chart-local frame `eᵢ`. -/
theorem codifferential_eq_sum_chartInvGramMatrix (α : M) {x : M} (hx : x ∈ (chartAt H α).source)
    (η : Π y : M, TangentSpace I y →L[ℝ] V y) :
    cov.codifferential covT η x =
      -∑ i, ∑ j, chartInvGramMatrix (I := I) α x i j •
        covT.hom cov η x (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α j x) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  let b := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hx'
  have hb (i) : b i = chartLocalFrame (I := I) α i x :=
    (chartLocalFrame_apply_of_mem_chart_source (I := I) α hx i).symm
  have hgram : Matrix.gram ℝ b = chartGramMatrix (I := I) α x := by
    simpa using gram_basisAt_finBasis_reindex (I := I) (Equiv.refl _) α hx'
  rw [codifferential, TensorProduct.lift_canonicalCovariantTensor_eq_sum_inv_gram _ b, hgram,
    ← chartInvGramMatrix_def]
  simp only [hb, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- On the domain of the chart at `α`, `∇* η = -∑ᵢ (∇_{eᵢ} η)(eᵢ♯)` in terms of the chart-local
frame `eᵢ` and its metric dual frame `eᵢ♯ = chartDualFrame α i`. -/
theorem codifferential_eq_sum_chartDualFrame (α : M) {x : M} (hx : x ∈ (chartAt H α).source)
    (η : Π y : M, TangentSpace I y →L[ℝ] V y) :
    cov.codifferential covT η x =
      -∑ i, covT.hom cov η x (chartLocalFrame (I := I) α i x) (chartDualFrame (I := I) α i x) := by
  rw [codifferential_eq_sum_chartInvGramMatrix cov covT α hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [chartDualFrame_apply, map_sum, map_smul]

end General

section RoughLaplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **Factorization of the rough Laplacian.** On a smooth section `σ`, the covariant codifferential
of `∇σ` equals the rough Laplacian `∇*∇ σ` at every point: `∇* (∇σ) = ∇*∇ σ`. -/
theorem codifferential_covariantDerivative
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.codifferential covT (cov σ) x = cov.roughLaplacian covT σ x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [codifferential_eq_sum cov covT _ x b, roughLaplacian_eq_sum cov covT _ x b]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦
    (secondCovariantDerivative_eq_hom_apply cov covT hσ x _ _).symm

/-- The rough Laplacian vanishes outside the closed support of `σ`. -/
theorem roughLaplacian_eq_zero_of_notMem_closure
    {σ : Π y : M, V y} {x : M} (hx : x ∉ closure {y | σ y ≠ 0}) :
    cov.roughLaplacian covT σ x = 0 := by
  by_cases hσ : CMDiff ∞ (T% σ)
  · rw [← codifferential_covariantDerivative cov covT hσ]
    apply codifferential_eq_zero_of_notMem_closure cov covT
    have hsub : {y | cov σ y ≠ 0} ⊆ closure {z | σ z ≠ 0} := fun y hy ↦ by
      by_contra hy'
      have hzero : ∀ᶠ z in 𝓝 y, σ z = (0 : Π w : M, V w) z := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy'] with z hz
        by_contra hne
        exact hz (subset_closure hne)
      have h0diff : MDiffAt (T% (0 : Π z : M, V z)) y := by
        simpa only [zero_smul] using (hσ.mdifferentiableAt (by simp)).const_smul_section (0 : ℝ)
      exact hy <| (cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (hσ.mdifferentiableAt (by simp)) h0diff Filter.univ_mem hzero).trans
        cov.isCovariantDerivativeOnUniv.zero
    exact fun hx' ↦ hx (closure_minimal hsub isClosed_closure hx')
  · exact roughLaplacian_of_not_contMDiff cov covT hσ x

/-- **Local inverse-Gram formula for the rough Laplacian.** On the domain of the chart at `α`,
`∇*∇ σ = -∑ᵢ ∑ⱼ gⁱʲ ∇²σ(eᵢ, eⱼ)` in the chart-local frame `eᵢ`. -/
theorem roughLaplacian_eq_sum_chartInvGramMatrix
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) (σ : Π y : M, V y) :
    cov.roughLaplacian covT σ x =
      -∑ i, ∑ j, chartInvGramMatrix (I := I) α x i j •
        cov.secondCovariantDerivative covT σ x
          (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α j x) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  let b := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hx'
  have hb (i) : b i = chartLocalFrame (I := I) α i x :=
    (chartLocalFrame_apply_of_mem_chart_source (I := I) α hx i).symm
  have hgram : Matrix.gram ℝ b = chartGramMatrix (I := I) α x := by
    simpa using gram_basisAt_finBasis_reindex (I := I) (Equiv.refl _) α hx'
  rw [roughLaplacian_eq_sum cov covT σ x e,
    ← TensorProduct.lift_canonicalCovariantTensor_eq_sum _ e,
    TensorProduct.lift_canonicalCovariantTensor_eq_sum_inv_gram _ b, hgram,
    ← chartInvGramMatrix_def]
  simp only [hb]

/-- On the domain of the chart at `α`, `∇*∇ σ = -∑ᵢ ∇²σ(eᵢ, eᵢ♯)` in terms of `chartLocalFrame`
and `chartDualFrame`. -/
theorem roughLaplacian_eq_sum_chartDualFrame
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) (σ : Π y : M, V y) :
    cov.roughLaplacian covT σ x =
      -∑ i, cov.secondCovariantDerivative covT σ x
        (chartLocalFrame (I := I) α i x) (chartDualFrame (I := I) α i x) := by
  rw [roughLaplacian_eq_sum_chartInvGramMatrix cov covT α hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [chartDualFrame_apply, map_sum, map_smul]

end RoughLaplacian

/-! ### Bundled covariant derivative on smooth sections -/

section SmoothCovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

section Basic

variable (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative `∇` as a real-linear map from smooth sections of `V` to smooth
sections of `Hom(TM, V)`. -/
def smoothCovariantDerivative :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯ where
  toFun σ := ⟨cov σ, contMDiffOn_univ.mp
    (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using σ.contMDiff.contMDiffOn))⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦
    cov.isCovariantDerivativeOnUniv.add
      (σ.contMDiff.mdifferentiableAt (by simp)) (τ.contMDiff.mdifferentiableAt (by simp))
  map_smul' c σ := ContMDiffSection.ext fun x ↦
    cov.isCovariantDerivativeOnUniv.smul_const c
      (σ.contMDiff.mdifferentiableAt (by simp))

@[simp]
theorem smoothCovariantDerivative_apply (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.smoothCovariantDerivative σ x = cov σ x :=
  (rfl)

/-- Covariant differentiation does not enlarge the closed support of a smooth section. -/
theorem tsupport_smoothCovariantDerivative_subset (σ : Cₛ^∞⟮I; F, V⟯) :
    (cov.smoothCovariantDerivative σ).tsupport ⊆ σ.tsupport := by
  refine (ContMDiffSection.tsupport_subset_iff σ.isClosed_tsupport).2 fun x hx ↦ ?_
  have hzero : ∀ᶠ y in 𝓝 x, (σ : Π z, V z) y = (0 : Cₛ^∞⟮I; F, V⟯) y :=
    Filter.eventually_of_mem (σ.isClosed_tsupport.isOpen_compl.mem_nhds hx) fun y hy ↦ by
      simp [σ.eq_zero_of_notMem_tsupport hy]
  rw [smoothCovariantDerivative_apply,
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (σ.contMDiff.mdifferentiableAt (by simp))
      ((0 : Cₛ^∞⟮I; F, V⟯).contMDiff.mdifferentiableAt (by simp)) Filter.univ_mem hzero,
    ContMDiffSection.coe_zero, cov.isCovariantDerivativeOnUniv.zero]

/-- Covariant differentiation preserves compactly supported smooth sections. -/
theorem smoothCovariantDerivative_mem_compactlySupported {σ : Cₛ^∞⟮I; F, V⟯}
    (hσ : σ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    cov.smoothCovariantDerivative σ ∈
      ContMDiffSection.compactlySupported I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x) := by
  rw [ContMDiffSection.mem_compactlySupported] at hσ ⊢
  exact hσ.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
    (cov.tsupport_smoothCovariantDerivative_subset σ)

/-- The commutator `[∇, f] σ` acts on `v` by `df(v) • σ x`: the principal symbol of `∇`. -/
theorem smulCommutator_smoothCovariantDerivative_apply
    (f : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) (v : TangentSpace I x) :
    TauCeti.smulCommutator ℝ f cov.smoothCovariantDerivative σ x v = d% f x v • σ x := by
  have hcoe : (⇑(f • σ) : Π y, V y) = (f : M → ℝ) • (σ : Π y, V y) :=
    funext fun y ↦ ContMDiffSection.smul_apply f σ y
  simp only [TauCeti.smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply, ContMDiffSection.smul_apply, smul_apply,
    smoothCovariantDerivative_apply, hcoe,
    cov.covariantDerivative_smul_section_apply (f.contMDiff.mdifferentiableAt (by simp))
      (σ.contMDiff.mdifferentiableAt (by simp)), add_sub_cancel_left]

/-- A smooth covariant derivative has differential-operator order at most `1`. -/
theorem smoothCovariantDerivative_mem_differentialOperators_one :
    cov.smoothCovariantDerivative ∈
      TauCeti.differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯
        Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯ 1 := by
  refine TauCeti.mem_differentialOperators_succ_iff.2 fun f ↦
    TauCeti.mem_differentialOperators_zero_iff.2 fun g σ ↦ ContMDiffSection.ext fun x ↦ ?_
  ext v
  simp only [ContMDiffSection.smul_apply, smul_apply,
    smulCommutator_smoothCovariantDerivative_apply, smul_comm (d% f x v) (g x)]

end Basic

end SmoothCovariantDerivative

/-! ### Smoothness and local volume-density divergence formulas -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **Smoothness of the covariant codifferential.** For smooth connections `cov` and `covT` on a
smooth Riemannian manifold, `cov.codifferential covT` carries every smooth section of `Hom(TM, V)`
to a smooth section of `V`. -/
theorem contMDiff_codifferential [ContMDiffCovariantDerivative covT ∞]
    {η : Π x : M, TangentSpace I x →L[ℝ] V x}
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x))) :
    CMDiff ∞ (T% (cov.codifferential covT η)) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hhom := contMDiff_hom covT cov hη
  intro x
  let s := (chartAt H x).source
  have hframe (i) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) x i y)) s := by
    simpa only [s, TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartLocalFrame (I := I) (n := ∞) x i
  have hGinv (i j) : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ chartInvGramMatrix (I := I) x y i j) s := by
    simpa only [s, TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) x i j
  have hinner : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun y ↦ TotalSpace.mk' F y (∑ i, ∑ j, chartInvGramMatrix (I := I) x y i j •
        covT.hom cov η y (chartLocalFrame (I := I) x i y)
          (chartLocalFrame (I := I) x j y))) s :=
    ContMDiffOn.sum_section fun i _ ↦ ContMDiffOn.sum_section fun j _ ↦
      (hGinv i j).smul_section
        (((hhom.contMDiffOn (s := s)).clm_bundle_apply (hframe i)).clm_bundle_apply (hframe j))
  exact (((contMDiffOn_const (c := (-1 : ℝ))).smul_section hinner).congr fun y hy ↦
    congrArg (TotalSpace.mk' F y)
      ((codifferential_eq_sum_chartInvGramMatrix cov covT x hy η).trans
        (neg_one_smul ℝ _).symm)).contMDiffAt
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))

/-- **Smoothness of the rough Laplacian.** For smooth connections `cov` and `covT` on a smooth
Riemannian manifold, `cov.roughLaplacian covT` sends every smooth section of `V` to a smooth
section of `V`. -/
theorem contMDiff_roughLaplacian [ContMDiffCovariantDerivative covT ∞]
    {σ : Π x : M, V x} (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (cov.roughLaplacian covT σ)) := by
  have hcovσ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (cov σ x)) :=
    contMDiffOn_univ.mp
      (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using hσ.contMDiffOn))
  exact (cov.contMDiff_codifferential covT hcovσ).congr fun x ↦
    congrArg (TotalSpace.mk' F x) (codifferential_covariantDerivative cov covT hσ x).symm

omit [T2Space M] in
/-- Differentiating the locally constant Kronecker delta `⟪eₖ♯, eⱼ⟫ = δₖⱼ` expresses
`⟪∇^{LC}_{eₖ} eₖ♯, eⱼ⟫` as minus the `k`-th local-frame coefficient of `∇^{LC}_{eₖ} eⱼ`. -/
private theorem inner_leviCivitaConnection_chartDualFrame
    (α : M) {y : M} (hy : y ∈ (chartAt H α).source) (k j : Fin (Module.finrank ℝ E)) :
    ⟪leviCivitaConnection I M (chartDualFrame (I := I) α k) y (chartLocalFrame (I := I) α k y),
        chartLocalFrame (I := I) α j y⟫ =
      -(trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y
        (leviCivitaConnection I M (chartLocalFrame (I := I) α k) y
          (chartLocalFrame (I := I) α j y)) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  have hy_ext : y ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hLC := isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)
  have ht : (leviCivitaConnection I M).IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero _).2 hLC.torsion
  have hD : MDiffAt (T% (chartDualFrame (I := I) α k)) y :=
    (contMDiffAt_chartDualFrame (I := I) (n := ∞) α hy' k).mdifferentiableAt (by simp)
  have hF : MDiffAt (T% (chartLocalFrame (I := I) α j)) y :=
    ((contMDiffOn_chartLocalFrame (I := I) (n := ∞) α j).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hy')).mdifferentiableAt
      (by simp)
  have hcoeff (w : TangentSpace I y) :
      ⟪chartDualFrame (I := I) α k y, w⟫ =
        (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y w := by
    conv_lhs =>
      rw [(trivializationAt E (TangentSpace I) α).eq_sum_localFrameCoeff_smul
        (I := I) (b := Module.finBasis ℝ E) (s := fun _ ↦ w) hy']
    simp only [← chartLocalFrame_def, inner_sum, real_inner_smul_right, inner_chartDualFrame α hy,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hconst : (fun z ↦ ⟪chartDualFrame (I := I) α k z, chartLocalFrame (I := I) α j z⟫) =ᶠ[𝓝 y]
      fun _ ↦ if k = j then (1 : ℝ) else 0 := by
    filter_upwards [(chartAt H α).open_source.mem_nhds hy] with z hz
    exact inner_chartDualFrame α hz k j
  have h0 : mvfderiv I
      (fun z ↦ ⟪chartDualFrame (I := I) α k z, chartLocalFrame (I := I) α j z⟫) y
      (chartLocalFrame (I := I) α k y) = 0 := by
    rw [hconst.mvfderiv_eq, mvfderiv_const, zero_apply]
  have hm := hLC.isMetricCompatible.mvfderiv_inner_eq
    (fun _ ↦ chartLocalFrame (I := I) α k y) hD hF
  dsimp only at hm
  have hcomm : leviCivitaConnection I M (chartLocalFrame (I := I) α j) y
        (chartLocalFrame (I := I) α k y) =
      leviCivitaConnection I M (chartLocalFrame (I := I) α k) y
        (chartLocalFrame (I := I) α j y) := by
    simpa only [chartLocalFrame_def] using
      TauCeti.Manifold.covariantDerivative_localFrame_comm ht (Module.finBasis ℝ E) α hy_ext k j
  rw [h0, hcomm, hcoeff] at hm
  linarith

omit [T2Space M] in
/-- **Coordinate Piola identity for the Levi-Civita connection.** On a chart domain, the weighted
dual frame `ρ • eₖ♯` (with `ρ = chartVolumeDensity α`) satisfies `∑ₖ ∇^{LC}_{eₖ}(ρ • eₖ♯) = 0`.
This cancels the connection terms on `TM` when `∇*` and `∇*∇` are written in divergence form. -/
private theorem sum_leviCivitaConnection_chartVolumeDensity_smul_chartDualFrame
    (α : M) {y : M} (hy : y ∈ (chartAt H α).source) :
    ∑ k, leviCivitaConnection I M
      (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z • chartDualFrame (I := I) α k z) y
      (chartLocalFrame (I := I) α k y) = 0 := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  let b := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hy'
  have hb (j) : b j = chartLocalFrame (I := I) α j y :=
    (chartLocalFrame_apply_of_mem_chart_source (I := I) α hy j).symm
  have hLC := isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)
  have hρ : MDiffAt (TauCeti.chartVolumeDensity (I := I) α) y :=
    ((TauCeti.contMDiffOn_chartVolumeDensity (I := I) (n := ∞) α).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hy')).mdifferentiableAt
      (by simp)
  have hD (k) : MDiffAt (T% (chartDualFrame (I := I) α k)) y :=
    (contMDiffAt_chartDualFrame (I := I) (n := ∞) α hy' k).mdifferentiableAt (by simp)
  refine InnerProductSpace.ext_inner_right_basis b fun j ↦ ?_
  rw [inner_zero_left, hb, sum_inner]
  have hsmul (k) : (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z •
      chartDualFrame (I := I) α k z) =
      TauCeti.chartVolumeDensity (I := I) α • chartDualFrame (I := I) α k := rfl
  have hsum : ∑ k,
      ⟪leviCivitaConnection I M
          (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z • chartDualFrame (I := I) α k z) y
          (chartLocalFrame (I := I) α k y), chartLocalFrame (I := I) α j y⟫ =
      -TauCeti.chartVolumeDensity (I := I) α y *
          ∑ k, (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y
            (leviCivitaConnection I M (chartLocalFrame (I := I) α k) y
              (chartLocalFrame (I := I) α j y)) +
        mvfderiv I (TauCeti.chartVolumeDensity (I := I) α) y (chartLocalFrame (I := I) α j y) := by
    simp only [hsmul, covariantDerivative_smul_section_apply (leviCivitaConnection I M) hρ (hD _),
      inner_add_left, real_inner_smul_left, inner_leviCivitaConnection_chartDualFrame α hy,
      inner_chartDualFrame α hy, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_neg, Finset.sum_neg_distrib,
      ← Finset.mul_sum, neg_mul]
  rw [hsum, TauCeti.mvfderiv_chartVolumeDensity hLC.isMetricCompatible α hy']
  ring

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative cov ∞] in
/-- **Local volume-density divergence formula for the covariant codifferential.** On the domain of
the chart at `α`, with `ρ = chartVolumeDensity α`, chart frame `eₖ = chartLocalFrame α k`, and dual
frame `eₖ♯ = chartDualFrame α k`,
`ρ (∇* η) = -∑ₖ ∇_{eₖ} (ρ • η(eₖ♯))` for the Levi-Civita connection on `TM`. -/
theorem chartVolumeDensity_smul_codifferential (α : M) {y : M} (hy : y ∈ (chartAt H α).source)
    {η : Π x : M, TangentSpace I x →L[ℝ] V x}
    (hη : MDiffAt
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun w ↦ TangentSpace I w →L[ℝ] V w) z (η z)) y) :
    TauCeti.chartVolumeDensity (I := I) α y •
        cov.codifferential (leviCivitaConnection I M) η y =
      -∑ k, cov (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z •
          η z (chartDualFrame (I := I) α k z)) y (chartLocalFrame (I := I) α k y) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  have hρ : MDiffAt (TauCeti.chartVolumeDensity (I := I) α) y :=
    ((TauCeti.contMDiffOn_chartVolumeDensity (I := I) (n := ∞) α).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hy')).mdifferentiableAt
      (by simp)
  have hρD (k) : MDiffAt (T% (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z •
      chartDualFrame (I := I) α k z)) y :=
    hρ.smul_section ((contMDiffAt_chartDualFrame (I := I) (n := ∞) α hy' k).mdifferentiableAt
      (by simp))
  have hterm (k) :
      TauCeti.chartVolumeDensity (I := I) α y •
          (leviCivitaConnection I M).hom cov η y
            (chartLocalFrame (I := I) α k y) (chartDualFrame (I := I) α k y) =
        cov (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z •
            η z (chartDualFrame (I := I) α k z)) y (chartLocalFrame (I := I) α k y) -
          η y (leviCivitaConnection I M
            (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z • chartDualFrame (I := I) α k z) y
            (chartLocalFrame (I := I) α k y)) := by
    have hh := hom_apply (leviCivitaConnection I M) cov hη (hρD k)
      (chartLocalFrame (I := I) α k y)
    simpa only [map_smul] using hh
  rw [codifferential_eq_sum_chartDualFrame cov (leviCivitaConnection I M) α hy, smul_neg,
    Finset.smul_sum]
  simp only [hterm, Finset.sum_sub_distrib, ← map_sum,
    sum_leviCivitaConnection_chartVolumeDensity_smul_chartDualFrame (I := I) α hy, map_zero,
    sub_zero]

omit [ContMDiffVectorBundle ∞ F V I] in
/-- **Local volume-density divergence formula for the rough Laplacian.** On the domain of the chart
at `α`, with `ρ = chartVolumeDensity α`, chart frame `eₖ = chartLocalFrame α k`, and dual frame
`eₖ♯ = chartDualFrame α k`,
`ρ (∇*∇ σ) = -∑ₖ ∇_{eₖ} (ρ • ∇_{eₖ♯} σ)` for every smooth section `σ`. -/
theorem chartVolumeDensity_smul_roughLaplacian (α : M) {y : M} (hy : y ∈ (chartAt H α).source)
    {σ : Π x : M, V x} (hσ : CMDiff ∞ (T% σ)) :
    TauCeti.chartVolumeDensity (I := I) α y •
        cov.roughLaplacian (leviCivitaConnection I M) σ y =
      -∑ k, cov (fun z ↦ TauCeti.chartVolumeDensity (I := I) α z •
          cov σ z (chartDualFrame (I := I) α k z)) y (chartLocalFrame (I := I) α k y) := by
  have hcovσ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun w ↦ TangentSpace I w →L[ℝ] V w) z (cov σ z)) :=
    contMDiffOn_univ.mp
      (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using hσ.contMDiffOn))
  rw [← codifferential_covariantDerivative cov (leviCivitaConnection I M) hσ,
    chartVolumeDensity_smul_codifferential cov α hy (hcovσ.mdifferentiable (by simp) y)]

/-! ### Bundled codifferential and rough Laplacian on smooth sections -/

section Bundled

variable [ContMDiffCovariantDerivative covT ∞]

/-- The covariant codifferential `∇*` as a real-linear map from smooth sections of `Hom(TM, V)` to
smooth sections of `V`. -/
def smoothCodifferential :
    Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ where
  toFun η := ⟨cov.codifferential covT η, cov.contMDiff_codifferential covT η.contMDiff⟩
  map_add' η₁ η₂ := ContMDiffSection.ext fun x ↦
    codifferential_add cov covT
      (η₁.contMDiff.mdifferentiableAt (by simp)) (η₂.contMDiff.mdifferentiableAt (by simp))
  map_smul' c η := ContMDiffSection.ext fun x ↦ codifferential_const_smul cov covT c η x

@[simp]
theorem smoothCodifferential_apply
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯) (x : M) :
    cov.smoothCodifferential covT η x = cov.codifferential covT η x :=
  (rfl)

/-- The rough Laplacian `∇*∇` as a real-linear endomorphism of the smooth sections of `V`. -/
def smoothRoughLaplacian : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ where
  toFun σ := ⟨cov.roughLaplacian covT σ, cov.contMDiff_roughLaplacian covT σ.contMDiff⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦
    roughLaplacian_add cov covT σ.contMDiff τ.contMDiff x
  map_smul' c _ := ContMDiffSection.ext fun x ↦ roughLaplacian_const_smul cov covT c x

@[simp]
theorem smoothRoughLaplacian_apply (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.smoothRoughLaplacian covT σ x = cov.roughLaplacian covT σ x :=
  (rfl)

/-- **Operator factorization `∇* ∘ ∇ = ∇*∇`** on smooth sections. -/
@[simp]
theorem smoothCodifferential_comp_smoothCovariantDerivative :
    (cov.smoothCodifferential covT).comp cov.smoothCovariantDerivative =
      cov.smoothRoughLaplacian covT :=
  LinearMap.ext fun σ ↦ ContMDiffSection.ext fun x ↦
    codifferential_covariantDerivative cov covT σ.contMDiff x

/-- The covariant codifferential does not enlarge the closed support of a smooth one-form. -/
theorem tsupport_smoothCodifferential_subset
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯) :
    (cov.smoothCodifferential covT η).tsupport ⊆ η.tsupport := by
  refine (ContMDiffSection.tsupport_subset_iff η.isClosed_tsupport).2 fun x hx ↦ ?_
  have hzero : ∀ᶠ y in 𝓝 x, η y = (0 : Π z : M, TangentSpace I z →L[ℝ] V z) y :=
    Filter.eventually_of_mem (η.isClosed_tsupport.isOpen_compl.mem_nhds hx) fun y hy ↦
      η.eq_zero_of_notMem_tsupport hy
  rw [smoothCodifferential_apply, codifferential_congr_of_eventuallyEq cov covT hzero,
    codifferential_zero]

/-- The rough Laplacian does not enlarge the closed support of a smooth section. -/
theorem tsupport_smoothRoughLaplacian_subset (σ : Cₛ^∞⟮I; F, V⟯) :
    (cov.smoothRoughLaplacian covT σ).tsupport ⊆ σ.tsupport := by
  rw [← smoothCodifferential_comp_smoothCovariantDerivative, LinearMap.comp_apply]
  exact (cov.tsupport_smoothCodifferential_subset covT _).trans
    (cov.tsupport_smoothCovariantDerivative_subset σ)

/-- The covariant codifferential preserves compactly supported smooth one-forms. -/
theorem smoothCodifferential_mem_compactlySupported
    {η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯}
    (hη : η ∈
      ContMDiffSection.compactlySupported I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x)) :
    cov.smoothCodifferential covT η ∈ ContMDiffSection.compactlySupported I F ∞ V := by
  rw [ContMDiffSection.mem_compactlySupported] at hη ⊢
  exact hη.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
    (cov.tsupport_smoothCodifferential_subset covT η)

/-- The rough Laplacian preserves compactly supported smooth sections. -/
theorem smoothRoughLaplacian_mem_compactlySupported {σ : Cₛ^∞⟮I; F, V⟯}
    (hσ : σ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    cov.smoothRoughLaplacian covT σ ∈ ContMDiffSection.compactlySupported I F ∞ V := by
  rw [ContMDiffSection.mem_compactlySupported] at hσ ⊢
  exact hσ.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
    (cov.tsupport_smoothRoughLaplacian_subset covT σ)

/-- The commutator `[∇*, f] η` is `-η(grad f)`: the principal symbol `-ι_{ξ♯}` of `∇*`. -/
theorem smulCommutator_smoothCodifferential_apply
    (f : C^∞⟮I, M; ℝ⟯)
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯) (x : M) :
    TauCeti.smulCommutator ℝ f (cov.smoothCodifferential covT) η x =
      -η x (TauCeti.Manifold.mgradient I f x) := by
  have hcoe : (⇑(f • η) : Π y, TangentSpace I y →L[ℝ] V y) =
      (f : M → ℝ) • (η : Π y, TangentSpace I y →L[ℝ] V y) :=
    funext fun y ↦ ContMDiffSection.smul_apply f η y
  simp only [TauCeti.smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, smoothCodifferential_apply, hcoe,
    codifferential_smul cov covT (f.contMDiff.mdifferentiableAt (by simp))
      (η.contMDiff.mdifferentiableAt (by simp)), sub_sub_cancel_left]

/-- The covariant codifferential has differential-operator order at most `1`. -/
theorem smoothCodifferential_mem_differentialOperators_one :
    cov.smoothCodifferential covT ∈
      TauCeti.differentialOperators ℝ C^∞⟮I, M; ℝ⟯
        Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  refine TauCeti.mem_differentialOperators_succ_iff.2 fun f ↦
    TauCeti.mem_differentialOperators_zero_iff.2 fun g η ↦ ContMDiffSection.ext fun x ↦ ?_
  simp only [ContMDiffSection.smul_apply, smulCommutator_smoothCodifferential_apply,
    smul_apply, smul_neg]

/-- The rough Laplacian `∇*∇ = ∇* ∘ ∇` has differential-operator order at most `2` on smooth
sections, as the composition of the first-order operators `∇*` and `∇`. -/
theorem smoothRoughLaplacian_mem_differentialOperators_two :
    cov.smoothRoughLaplacian covT ∈
      TauCeti.differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2 := by
  rw [← smoothCodifferential_comp_smoothCovariantDerivative]
  exact TauCeti.comp_mem_differentialOperators
    (cov.smoothCodifferential_mem_differentialOperators_one covT)
    cov.smoothCovariantDerivative_mem_differentialOperators_one

/-- The double commutator `[[∇*∇, f], g] σ` on bundled smooth sections is
`-(2 * ⟪grad f, grad g⟫) • σ`, recording the scalar metric principal symbol of `∇*∇` via
`∇*∇ = ∇* ∘ ∇` and the principal symbols of `∇*` and `∇`. -/
theorem smulCommutator_smulCommutator_smoothRoughLaplacian_apply
    (f g : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    TauCeti.smulCommutator ℝ g
        (TauCeti.smulCommutator ℝ f (cov.smoothRoughLaplacian covT)) σ x =
      -(2 * ⟪TauCeti.Manifold.mgradient I f x, TauCeti.Manifold.mgradient I g x⟫) • σ x := by
  have hQ0 := TauCeti.smulCommutator_eq_zero_of_mem_differentialOperators_zero
    (TauCeti.smulCommutator_mem_differentialOperators
      cov.smoothCovariantDerivative_mem_differentialOperators_one f) g
  have hP0 := TauCeti.smulCommutator_eq_zero_of_mem_differentialOperators_zero
    (TauCeti.smulCommutator_mem_differentialOperators
      (cov.smoothCodifferential_mem_differentialOperators_one covT) f) g
  rw [← smoothCodifferential_comp_smoothCovariantDerivative, TauCeti.smulCommutator_comp,
    map_add, TauCeti.smulCommutator_comp, TauCeti.smulCommutator_comp, hQ0, hP0]
  simp only [LinearMap.comp_zero, LinearMap.zero_comp, zero_add, add_zero, LinearMap.add_apply,
    LinearMap.comp_apply, ContMDiffSection.coe_add, Pi.add_apply,
    smulCommutator_smoothCodifferential_apply, smulCommutator_smoothCovariantDerivative_apply,
    ← TauCeti.Manifold.inner_mgradient_right,
    real_inner_comm (TauCeti.Manifold.mgradient I g x)]
  module

end Bundled

end Smooth

end CovariantDerivative

end
