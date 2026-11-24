/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.HilbertSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Analysis.InnerProductSpace.CanonicalTensor
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The formal adjoint of a connection and local coordinate formulas

Let `∇` be a connection on a vector bundle `V` over a Riemannian manifold `M`, and `∇ᵀ` a
connection on the tangent bundle. The connection is an operator `∇ : Γ(V) → Γ(T*M ⊗ V)` from
sections of `V` to `V`-valued one-forms, here sections `α` of the bundle `Hom(TM, V)`. Its
**formal adjoint** (or covariant codifferential) is the negative metric trace of the covariant
derivative of a one-form,

`∇*α = -tr_g ∇α = -∑ᵢ (∇_{eᵢ} α)(eᵢ)`,

for any orthonormal basis `eᵢ` of the tangent space, where `∇α` is the covariant derivative of
`α` for the connection induced by `∇ᵀ` and `∇` on `Hom(TM, V)` (`CovariantDerivative.hom`).

This file proves that `∇*` is the formal adjoint of `∇`, establishes local inverse-Gram and
volume-density divergence formulas for `∇*` and `∇*∇`, and shows that the rough Laplacian factors
through `∇*`:

* the rough Laplacian is the composite `∇*∇ σ = ∇*(∇σ)`, since the covariant derivative of the
  one-form `∇σ` is the second covariant derivative `∇²σ`;
* in a chart frame `eᵢ` with dual frame `eᵢ♯` and volume density `ρ = √det g`,
  `∇*α = -∑ᵢ ∑ⱼ gⁱʲ (∇_{eᵢ} α)(eⱼ)` and, for the Levi-Civita connection on `TM`,
  `ρ (∇*α) = -∑ₖ ∇_{eₖ} (ρ • α(eₖ♯))` and `ρ (∇*∇ σ) = -∑ₖ ∇_{eₖ} (ρ • ∇_{eₖ♯} σ)` via the
  coordinate Piola identity;
* on any `C²` Riemannian manifold, the vector field `X` metric-dual to `w ↦ ⟪τ, α(w)⟫` satisfies
  the pointwise divergence identity `div X = ⟪α, ∇τ⟫ - ⟪∇*α, τ⟫`
  (`CovariantDerivative.IsMetricCompatible.divergence_rieszDual_innerSL_comp`);
* for a metric connection `∇` and the Levi-Civita connection `∇ᵀ` on a manifold without boundary,
  **integration by parts** holds for the Riemannian volume `dV`:

  `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`

  for a smooth one-form `α` and a smooth section `τ`, one of which has compact support. Here
  `⟪α, ∇τ⟫ = ∑ᵢ ⟪α(eᵢ), ∇_{eᵢ} τ⟫` is the pointwise inner product of `V`-valued one-forms, the
  Hilbert–Schmidt inner product `ContinuousLinearMap.hilbertSchmidtInner`.

For `α = ∇σ` the integration by parts is the energy identity `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`
of the rough Laplacian, in `RoughLaplacian/Energy.lean`.

## Main definitions and results

* `CovariantDerivative.formalAdjoint`: the formal adjoint `∇*α` of a `V`-valued one-form at a
  point.
* `CovariantDerivative.formalAdjoint_eq_sum`: its value in an orthonormal basis.
* `CovariantDerivative.formalAdjoint_congr_of_eventuallyEq`,
  `CovariantDerivative.formalAdjoint_eq_zero_of_notMem_closure` and
  `CovariantDerivative.roughLaplacian_eq_zero_of_notMem_closure`: germ locality and support bounds.
* `CovariantDerivative.formalAdjoint_smul`: the Leibniz rule `∇*(f α) = f ∇*α - α(grad f)`.
* `CovariantDerivative.formalAdjoint_eq_neg_sum_chartInvGramMatrix`,
  `CovariantDerivative.formalAdjoint_eq_neg_sum_chartDualFrame`, and
  `CovariantDerivative.roughLaplacian_eq_neg_sum_chartInvGramMatrix`: local `gⁱʲ` and dual-frame
  trace formulas.
* `CovariantDerivative.chartVolumeDensity_smul_formalAdjoint` and
  `CovariantDerivative.chartVolumeDensity_smul_roughLaplacian`: local divergence-form expressions
  weighted by `ρ = √det g`.
* `CovariantDerivative.roughLaplacian_eq_formalAdjoint`: `∇*∇ σ = ∇*(∇σ)` for a smooth section.
* `CovariantDerivative.IsMetricCompatible.divergence_rieszDual_innerSL_comp` and
  `CovariantDerivative.IsMetricCompatible.divergence_rieszDual_innerSL_comp_cov`: pointwise
  divergence identities on `C²` and smooth Riemannian manifolds.
* `CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint`,
  `CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint_of_isCompact_left`, and
  `CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint_of_or`:
  **integration by parts**, `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`, when `τ` or `α` has compact support.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (Propositions 2.4–2.5, formal adjoint of a connection and generalized Laplacians).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §8 (the connection Laplacian `∇*∇` as the composite of `∇` and its adjoint).
* P. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, §2 (the rough
  Laplacian and operators of Laplace type).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence theorem) and Chapter 4 (covariant derivatives of tensor fields).
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open TauCeti (riemannianVolume)
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

section Definition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V)
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {α : Π x : M, TangentSpace I x →L[ℝ] V x}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **formal adjoint** `∇*α = -tr_g ∇α` of the connection `∇`, applied to a `V`-valued
one-form `α` at `x`: the negative metric trace of the covariant derivative of `α` for the
connection induced by `∇ᵀ` and `∇` on `Hom(TM, V)`. In an orthonormal basis it is
`-∑ᵢ (∇_{eᵢ} α)(eᵢ)` (`formalAdjoint_eq_sum`). For a metric connection and the Levi-Civita
connection it is the formal adjoint of `∇` for the Riemannian volume
(`IsMetricCompatible.integral_inner_formalAdjoint`), and `∇*(∇σ)` is the rough Laplacian
(`roughLaplacian_eq_formalAdjoint`). It is zero at points where `α` is not differentiable. -/
def formalAdjoint (α : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) : V x :=
  -TensorProduct.lift.equiv (.id ℝ) (TangentSpace I x) (TangentSpace I x) (V x)
    (ContinuousLinearMap.toLinearMap₁₂ (covT.hom cov α x))
    (InnerProductSpace.canonicalCovariantTensor (TangentSpace I x))

/-- The formal adjoint of a connection in an orthonormal basis: `∇*α = -∑ᵢ (∇_{eᵢ} α)(eᵢ)`. -/
theorem formalAdjoint_eq_sum (α : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.formalAdjoint covT α x = -∑ i, covT.hom cov α x (b i) (b i) := by
  rw [formalAdjoint, InnerProductSpace.canonicalCovariantTensor_eq_sum _ b, map_sum]
  simp only [TensorProduct.lift.equiv_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- The formal adjoint vanishes at a point where the one-form is not differentiable. -/
@[simp]
theorem formalAdjoint_eq_zero_of_not_mdifferentiableAt {x : M}
    (hα : ¬MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x) :
    cov.formalAdjoint covT α x = 0 := by
  simp [formalAdjoint, hom_eq_zero_of_not_mdifferentiableAt covT cov hα]

/-- The formal adjoint of the zero one-form is zero. -/
@[simp]
theorem formalAdjoint_zero (x : M) :
    cov.formalAdjoint covT (0 : Π x : M, TangentSpace I x →L[ℝ] V x) x = 0 := by
  rw [formalAdjoint_eq_sum cov covT _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    (covT.hom cov).isCovariantDerivativeOnUniv.zero]
  simp

/-- The formal adjoint is additive on one-forms differentiable at the point. -/
theorem formalAdjoint_add {β : Π x : M, TangentSpace I x →L[ℝ] V x} {x : M}
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x)
    (hβ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (β y)) x) :
    cov.formalAdjoint covT (α + β) x = cov.formalAdjoint covT α x + cov.formalAdjoint covT β x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  simp only [formalAdjoint_eq_sum cov covT _ x b,
    (covT.hom cov).isCovariantDerivativeOnUniv.add hα hβ, add_apply,
    Finset.sum_add_distrib, neg_add]

/-- The formal adjoint commutes with multiplication of the one-form by a constant. -/
@[simp]
theorem formalAdjoint_const_smul (c : ℝ) (x : M) :
    cov.formalAdjoint covT (c • α) x = c • cov.formalAdjoint covT α x := by
  by_cases hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x
  · set b := stdOrthonormalBasis ℝ (TangentSpace I x)
    simp only [formalAdjoint_eq_sum cov covT _ x b,
      (covT.hom cov).isCovariantDerivativeOnUniv.smul_const c hα, smul_apply,
      ← Finset.smul_sum, smul_neg]
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have hcα : ¬MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
          (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y ((c • α) y)) x := fun h ↦ hα (by
        simpa [smul_smul, inv_mul_cancel₀ hc] using
          (mdifferentiableAt_const (c := c⁻¹)).smul_section h)
      simp [formalAdjoint_eq_zero_of_not_mdifferentiableAt cov covT hα,
        formalAdjoint_eq_zero_of_not_mdifferentiableAt cov covT hcα]

/-- The formal adjoint commutes with negation of the one-form. -/
@[simp]
theorem formalAdjoint_neg (x : M) :
    cov.formalAdjoint covT (-α) x = -cov.formalAdjoint covT α x := by
  rw [← neg_one_smul ℝ α, formalAdjoint_const_smul, neg_one_smul]

/-- The formal adjoint commutes with differences of one-forms differentiable at the point. -/
theorem formalAdjoint_sub {β : Π x : M, TangentSpace I x →L[ℝ] V x} {x : M}
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x)
    (hβ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (β y)) x) :
    cov.formalAdjoint covT (α - β) x = cov.formalAdjoint covT α x - cov.formalAdjoint covT β x := by
  have hβ' : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y ((-β) y)) x := by
    simpa using (mdifferentiableAt_const (c := (-1 : ℝ))).smul_section hβ
  rw [sub_eq_add_neg, formalAdjoint_add cov covT hα hβ', formalAdjoint_neg, sub_eq_add_neg]

/-- **Locality of the formal adjoint.** One-forms with the same germ at `x` have the same formal
adjoint at `x`. -/
theorem formalAdjoint_congr_of_eventuallyEq {β : Π y : M, TangentSpace I y →L[ℝ] V y} {x : M}
    (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    cov.formalAdjoint covT α x = cov.formalAdjoint covT β x := by
  have htot : (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y
      (α y)) =ᶠ[𝓝 x]
      fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (β y) :=
    h.mono fun y hy ↦ congrArg (TotalSpace.mk' (E →L[ℝ] F) y) hy
  by_cases hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x
  · have hβ := htot.mdifferentiableAt_iff.mp hα
    rw [formalAdjoint, formalAdjoint,
      (covT.hom cov).isCovariantDerivativeOnUniv.congr_of_eventuallyEq hα hβ Filter.univ_mem h]
  · have hβ : ¬MDiffAt (fun y ↦
        TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (β y)) x :=
      fun h₂ ↦ hα (htot.mdifferentiableAt_iff.mpr h₂)
    simp [formalAdjoint_eq_zero_of_not_mdifferentiableAt cov covT hα,
      formalAdjoint_eq_zero_of_not_mdifferentiableAt cov covT hβ]

/-- The formal adjoint vanishes outside the closed support of `α`. -/
theorem formalAdjoint_eq_zero_of_notMem_closure {x : M} (hx : x ∉ closure {y | α y ≠ 0}) :
    cov.formalAdjoint covT α x = 0 := by
  simp [formalAdjoint_eq_sum cov covT _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    (covT.hom cov).apply_eq_zero_of_notMem_closure hx]

/-- **Leibniz rule for the formal adjoint.** For a function `f` and a one-form `α` differentiable
at `x`, `∇*(f α) = f ∇*α - α(grad f)`. -/
theorem formalAdjoint_smul {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x) :
    cov.formalAdjoint covT (f • α) x =
      f x • cov.formalAdjoint covT α x - α x (TauCeti.Manifold.mgradient I f x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- `∑ᵢ df(eᵢ) α(eᵢ) = α(grad f)`, since `grad f = ∑ᵢ df(eᵢ) eᵢ`.
  have hgrad : ∑ i, d% f x (b i) • α x (b i) = α x (TauCeti.Manifold.mgradient I f x) := by
    conv_rhs => rw [← b.sum_repr' (TauCeti.Manifold.mgradient I f x)]
    simp only [map_sum, map_smul, TauCeti.Manifold.inner_mgradient_right]
  simp only [formalAdjoint_eq_sum cov covT _ x b,
    (covT.hom cov).isCovariantDerivativeOnUniv.leibniz hα hf, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, Finset.sum_add_distrib,
    ← Finset.smul_sum, hgrad]
  module

/-! ### Local chart-frame formulas -/

/-- **Local inverse-Gram formula for the formal adjoint.** On the domain of the chart at `α₀`,
`∇*α = -∑ᵢ ∑ⱼ gⁱʲ (∇_{eᵢ} α)(eⱼ)` in the chart-local frame `eᵢ`. -/
theorem formalAdjoint_eq_neg_sum_chartInvGramMatrix (α₀ : M) {x : M}
    (hx : x ∈ (chartAt H α₀).source) (α : Π y : M, TangentSpace I y →L[ℝ] V y) :
    cov.formalAdjoint covT α x =
      -∑ i, ∑ j, chartInvGramMatrix (I := I) α₀ x i j •
        covT.hom cov α x (chartLocalFrame (I := I) α₀ i x) (chartLocalFrame (I := I) α₀ j x) := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [formalAdjoint_eq_sum cov covT α x e]
  simp only [← ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply (covT.hom cov α x),
    ← TensorProduct.lift_canonicalCovariantTensor_eq_sum _ e,
    lift_canonicalCovariantTensor_eq_sum_chartInvGramMatrix α₀ hx]

/-- On the domain of the chart at `α₀`, `∇*α = -∑ᵢ (∇_{eᵢ} α)(eᵢ♯)` in terms of the chart-local
frame `eᵢ` and its metric dual frame `eᵢ♯ = chartDualFrame α₀ i`. -/
theorem formalAdjoint_eq_neg_sum_chartDualFrame (α₀ : M) {x : M}
    (hx : x ∈ (chartAt H α₀).source) (α : Π y : M, TangentSpace I y →L[ℝ] V y) :
    cov.formalAdjoint covT α x =
      -∑ i, covT.hom cov α x
        (chartLocalFrame (I := I) α₀ i x) (chartDualFrame (I := I) α₀ i x) := by
  rw [formalAdjoint_eq_neg_sum_chartInvGramMatrix cov covT α₀ hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [chartDualFrame_apply, map_sum, map_smul]

/-- **Local volume-density divergence formula for the formal adjoint.** On the domain of the chart
at `α₀`, with `ρ = chartVolumeDensity α₀`, chart frame `eₖ = chartLocalFrame α₀ k`, and dual frame
`eₖ♯ = chartDualFrame α₀ k`, `ρ (∇*α) = -∑ₖ ∇_{eₖ} (ρ • α(eₖ♯))` for the Levi-Civita connection
on `TM`. -/
theorem chartVolumeDensity_smul_formalAdjoint
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (α₀ : M) {y : M} (hy : y ∈ (chartAt H α₀).source)
    (hα : MDiffAt
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun w ↦ TangentSpace I w →L[ℝ] V w) z (α z)) y) :
    TauCeti.chartVolumeDensity (I := I) α₀ y •
        cov.formalAdjoint (leviCivitaConnection I M) α y =
      -∑ k, cov (fun z ↦ TauCeti.chartVolumeDensity (I := I) α₀ z •
          α z (chartDualFrame (I := I) α₀ k z)) y (chartLocalFrame (I := I) α₀ k y) := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  have hρ : MDiffAt (TauCeti.chartVolumeDensity (I := I) α₀) y :=
    (TauCeti.contMDiffAt_chartVolumeDensity (I := I) (n := 1) α₀ hy).mdifferentiableAt one_ne_zero
  have hρD (k) : MDiffAt (T% (fun z ↦ TauCeti.chartVolumeDensity (I := I) α₀ z •
      chartDualFrame (I := I) α₀ k z)) y :=
    hρ.smul_section ((contMDiffAt_chartDualFrame (I := I) (n := 1) α₀ hy' k).mdifferentiableAt
      one_ne_zero)
  have hterm (k) :
      TauCeti.chartVolumeDensity (I := I) α₀ y •
          (leviCivitaConnection I M).hom cov α y
            (chartLocalFrame (I := I) α₀ k y) (chartDualFrame (I := I) α₀ k y) =
        cov (fun z ↦ TauCeti.chartVolumeDensity (I := I) α₀ z •
            α z (chartDualFrame (I := I) α₀ k z)) y (chartLocalFrame (I := I) α₀ k y) -
          α y (leviCivitaConnection I M
            (fun z ↦ TauCeti.chartVolumeDensity (I := I) α₀ z • chartDualFrame (I := I) α₀ k z) y
            (chartLocalFrame (I := I) α₀ k y)) := by
    simpa only [map_smul] using
      hom_apply (leviCivitaConnection I M) cov hα (hρD k) (chartLocalFrame (I := I) α₀ k y)
  rw [formalAdjoint_eq_neg_sum_chartDualFrame cov (leviCivitaConnection I M) α₀ hy, smul_neg,
    Finset.smul_sum]
  simp only [hterm, Finset.sum_sub_distrib, ← map_sum,
    TauCeti.sum_leviCivitaConnection_chartVolumeDensity_smul_chartDualFrame (I := I) α₀ hy,
    map_zero, sub_zero]

end Definition

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
  {σ : Π x : M, V x}

/-- **The rough Laplacian is the composite of the connection and its formal adjoint**:
`∇*∇ σ = ∇*(∇σ)` for a smooth section `σ`. -/
theorem roughLaplacian_eq_formalAdjoint (hσ : CMDiff ∞ (T% σ)) :
    cov.roughLaplacian covT σ = cov.formalAdjoint covT (cov σ) := by
  funext x
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  simp only [roughLaplacian_eq_sum cov covT σ x b, formalAdjoint_eq_sum cov covT _ x b,
    secondCovariantDerivative_eq_hom_apply cov covT hσ]

/-- The rough Laplacian vanishes outside the closed support of `σ`. -/
theorem roughLaplacian_eq_zero_of_notMem_closure {x : M} (hx : x ∉ closure {y | σ y ≠ 0}) :
    cov.roughLaplacian covT σ x = 0 := by
  by_cases hσ : CMDiff ∞ (T% σ)
  · rw [congrFun (roughLaplacian_eq_formalAdjoint cov covT hσ) x]
    have hsub : {z | cov σ z ≠ 0} ⊆ closure {z | σ z ≠ 0} := fun y hy ↦
      by_contra fun hy' ↦ hy (cov.apply_eq_zero_of_notMem_closure hy')
    exact formalAdjoint_eq_zero_of_notMem_closure cov covT
      fun hx' ↦ hx (closure_minimal hsub isClosed_closure hx')
  · exact roughLaplacian_of_not_contMDiff cov covT hσ x

/-- **Local inverse-Gram formula for the rough Laplacian.** On the domain of the chart at `α₀`,
`∇*∇ σ = -∑ᵢ ∑ⱼ gⁱʲ ∇²σ(eᵢ, eⱼ)` in the chart-local frame `eᵢ`. -/
theorem roughLaplacian_eq_neg_sum_chartInvGramMatrix
    (α₀ : M) {x : M} (hx : x ∈ (chartAt H α₀).source) (σ : Π y : M, V y) :
    cov.roughLaplacian covT σ x =
      -∑ i, ∑ j, chartInvGramMatrix (I := I) α₀ x i j •
        cov.secondCovariantDerivative covT σ x
          (chartLocalFrame (I := I) α₀ i x) (chartLocalFrame (I := I) α₀ j x) := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [roughLaplacian_eq_sum cov covT σ x e,
    ← TensorProduct.lift_canonicalCovariantTensor_eq_sum _ e,
    lift_canonicalCovariantTensor_eq_sum_chartInvGramMatrix α₀ hx]

/-- **Local volume-density divergence formula for the rough Laplacian.** On the domain of the chart
at `α₀`, with `ρ = chartVolumeDensity α₀`, chart frame `eₖ = chartLocalFrame α₀ k`, and dual frame
`eₖ♯ = chartDualFrame α₀ k`, `ρ (∇*∇ σ) = -∑ₖ ∇_{eₖ} (ρ • ∇_{eₖ♯} σ)` for every smooth section
`σ`. -/
theorem chartVolumeDensity_smul_roughLaplacian
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (α₀ : M) {y : M} (hy : y ∈ (chartAt H α₀).source) (hσ : CMDiff ∞ (T% σ)) :
    TauCeti.chartVolumeDensity (I := I) α₀ y •
        cov.roughLaplacian (leviCivitaConnection I M) σ y =
      -∑ k, cov (fun z ↦ TauCeti.chartVolumeDensity (I := I) α₀ z •
          cov σ z (chartDualFrame (I := I) α₀ k z)) y (chartLocalFrame (I := I) α₀ k y) := by
  have hcovσ := cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)
  rw [congrFun (roughLaplacian_eq_formalAdjoint cov (leviCivitaConnection I M) hσ) y,
    chartVolumeDensity_smul_formalAdjoint cov α₀ hy (hcovσ.mdifferentiableAt (by simp))]

end RoughLaplacian

/-! ### Pointwise divergence identity -/

section PointwiseDivergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov : _root_.CovariantDerivative I F V}

/-- **Pointwise divergence identity for the formal adjoint of a connection.** For a
metric-compatible connection `∇` on `V`, a section `α` of `Hom(TM, V)` and a section `τ` of `V`
differentiable at `x`, the divergence of the vector field dual to `v ↦ ⟪τ, α v⟫` equals
`⟪α, ∇τ⟫ - ⟪∇*α, τ⟫`. No orientation, boundarylessness, Hausdorffness, or compactness is needed. -/
theorem IsMetricCompatible.divergence_rieszDual_innerSL_comp (hcov : cov.IsMetricCompatible)
    {α : Π y : M, TangentSpace I y →L[ℝ] V y} {τ : Π y : M, V y} {x : M}
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x)
    (hτ : MDiffAt (T% τ) x) :
    TauCeti.Manifold.divergence I
        (fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (α y))) x =
      (α x).hilbertSchmidtInner (cov τ x) -
        ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let X : Π y : M, TangentSpace I y :=
    fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (α y))
  have hX : MDiffAt (T% X) x := hα.rieszDual_innerSL_comp hτ
  have hLC := (isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)).isMetricCompatible
  -- Each diagonal term of the divergence is `⟪α(eᵢ), ∇_{eᵢ} τ⟫ + ⟪(∇_{eᵢ} α)(eᵢ), τ⟫`.
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      ⟪leviCivitaConnection I M X x (b i), b i⟫ =
        ⟪α x (b i), cov τ x (b i)⟫ +
          ⟪(leviCivitaConnection I M).hom cov α x (b i) (b i), τ x⟫ := by
    let Y : Π y : M, TangentSpace I y := extend E (b i)
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend I E (b i)
    have hLCi := hLC.mvfderiv_inner_eq Y hX hY
    have hVi := hcov.mvfderiv_inner_eq Y hτ (hα.clm_bundle_apply hY)
    have hfun : (fun y ↦ ⟪X y, Y y⟫) = fun y ↦ ⟪τ y, α y (Y y)⟫ :=
      funext fun y ↦ inner_rieszDual ((innerSL ℝ (τ y)).comp (α y)) (Y y)
    have hYX : ⟪X x, leviCivitaConnection I M Y x (b i)⟫ =
        ⟪τ x, α x (leviCivitaConnection I M Y x (b i))⟫ :=
      inner_rieszDual ((innerSL ℝ (τ x)).comp (α x)) _
    have hhom := hom_apply (leviCivitaConnection I M) cov hα hY (b i)
    dsimp only at hLCi hVi
    simp only [Y, extend_apply_self] at hLCi hVi hhom
    rw [hfun] at hLCi
    rw [hVi, hYX] at hLCi
    simp only [Y] at hLCi
    rw [real_inner_comm _ (α x (b i)), real_inner_comm (τ x), hhom, inner_sub_right]
    linarith
  rw [TauCeti.Manifold.divergence_eq_sum_inner I X x b]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← ContinuousLinearMap.hilbertSchmidtInner_eq_sum (α x) (cov τ x) b,
    formalAdjoint_eq_sum cov (leviCivitaConnection I M) α x b, inner_neg_left, sum_inner,
    sub_neg_eq_add]

end PointwiseDivergence

/-- **Pointwise divergence identity for the rough Laplacian.** Applying
`IsMetricCompatible.divergence_rieszDual_innerSL_comp` to `α = ∇σ` expresses `div X` as
`⟪∇σ, ∇τ⟫ - ⟪∇*∇ σ, τ⟫`. -/
theorem IsMetricCompatible.divergence_rieszDual_innerSL_comp_cov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V]
    {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y} {x : M}
    (hσ : CMDiff ∞ (T% σ)) (hτ : MDiffAt (T% τ) x) :
    TauCeti.Manifold.divergence I
        (fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (cov σ y))) x =
      (cov σ x).hilbertSchmidtInner (cov τ x) -
        ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ := by
  have hcovσ := cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)
  rw [hcov.divergence_rieszDual_innerSL_comp (hcovσ.mdifferentiableAt (by simp)) hτ,
    congrFun (roughLaplacian_eq_formalAdjoint cov (leviCivitaConnection I M) hσ) x]

/-! ### Integration by parts -/

section Pairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {α : Π x : M, TangentSpace I x →L[ℝ] V x} {τ : Π x : M, V x}

/-- The vector field metric-dual to the one-form `w ↦ ⟪α(w), τ⟫`. -/
private def pairingField (α : Π x : M, TangentSpace I x →L[ℝ] V x) (τ : Π x : M, V x) (y : M) :
    TangentSpace I y :=
  rieszDual y ((innerSL ℝ (τ y)).comp (α y))

namespace IsMetricCompatible

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- Integration by parts for the formal adjoint, when the vector field dual to `⟪α, τ⟫` and the
function `⟪α, ∇τ⟫` both vanish off a compact set. -/
private theorem integral_inner_formalAdjoint_of_subset (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) {K : Set M} (hK : IsCompact K) (hKc : IsClosed K)
    (hX : ∀ y ∉ K, pairingField α τ y = 0)
    (hB : ∀ y ∉ K, (α y).hilbertSchmidtInner (cov τ y) = 0) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hXc : HasCompactSupport (β := E) (pairingField α τ) := .intro' hK hKc hX
  have hBc : HasCompactSupport fun x ↦ (α x).hilbertSchmidtInner (cov τ x) := .intro' hK hKc hB
  have hX1 : ContMDiff I I.tangent 1 (T% (pairingField α τ)) :=
    (hα.rieszDual_innerSL_comp hτ).of_le (by simp)
  have hBi : Integrable (fun x ↦ (α x).hilbertSchmidtInner (cov τ x)) (riemannianVolume I M) :=
    (hα.hilbertSchmidtInner_bundle
      (cov.contMDiff_covariantDerivative (by simpa using hτ))).continuous
      |>.integrable_of_hasCompactSupport hBc
  have hdiv := TauCeti.Manifold.integral_divergence_eq_zero hX1 hXc
  have hpt : ∀ x, TauCeti.Manifold.divergence I (pairingField α τ) x =
      (α x).hilbertSchmidtInner (cov τ x) -
        ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ := fun x ↦
    hcov.divergence_rieszDual_innerSL_comp (hα.mdifferentiableAt (by simp))
      (hτ.mdifferentiableAt (by simp))
  simp_rw [hpt] at hdiv
  rw [integral_sub hBi] at hdiv
  · linarith
  · refine (hBi.sub (TauCeti.Manifold.integrable_divergence hX1 hXc)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, hpt]
    ring

/-- **Integration by parts for the formal adjoint of a connection.** For a metric connection `∇`
on a Riemannian vector bundle over a manifold without boundary, a smooth `V`-valued one-form `α`
and a smooth section `τ` with compact support, `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`, where
`⟪α, ∇τ⟫ = ∑ᵢ ⟪α(eᵢ), ∇_{eᵢ} τ⟫`: `∇*` is the formal adjoint of `∇` for the Riemannian
volume. -/
theorem integral_inner_formalAdjoint (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) (hτc : IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M := by
  refine integral_inner_formalAdjoint_of_subset hcov hα hτ hτc isClosed_closure
    (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · have hτy : τ y = 0 := by
      by_contra h
      exact hy (subset_closure h)
    simp [pairingField, hτy, LinearIsometryEquiv.map_zero]
  · simp [cov.apply_eq_zero_of_notMem_closure hy]

/-- **Integration by parts for the formal adjoint of a connection**, when the one-form has
compact support: `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`. -/
theorem integral_inner_formalAdjoint_of_isCompact_left (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) (hαc : IsCompact (closure {x | α x ≠ 0})) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M := by
  have hαy {y : M} (hy : y ∉ closure {x | α x ≠ 0}) : α y = 0 := by
    by_contra h
    exact hy (subset_closure h)
  refine integral_inner_formalAdjoint_of_subset hcov hα hτ hαc isClosed_closure
    (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · simp [pairingField, hαy hy, LinearIsometryEquiv.map_zero]
  · simp [hαy hy]

/-- **Integration by parts for the formal adjoint of a connection**, when either the one-form `α`
or the section `τ` has compact support. -/
theorem integral_inner_formalAdjoint_of_or (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ))
    (hsupp : IsCompact (closure {x | α x ≠ 0}) ∨ IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M :=
  hsupp.elim (hcov.integral_inner_formalAdjoint_of_isCompact_left hα hτ)
    (hcov.integral_inner_formalAdjoint hα hτ)

end IsMetricCompatible

end Pairing

end CovariantDerivative

end
