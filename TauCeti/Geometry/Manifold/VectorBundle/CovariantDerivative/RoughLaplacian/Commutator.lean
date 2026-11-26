/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ThirdCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace

/-!
# The commutator of the rough Laplacian with the covariant derivative

Let `∇` be a smooth connection on a vector bundle `V` over a Riemannian manifold `M`, and `∇ᵀ` a
smooth torsion-free metric connection on the tangent bundle, such as the Levi-Civita connection.
The covariant derivative `∇σ` of a smooth section `σ` of `V` is a section of `Hom(TM, V)`, which
carries the connection induced by `∇ᵀ` and `∇`, and so has its own rough Laplacian `∇*∇(∇σ)`. This
file computes its difference with the covariant derivative of the rough Laplacian of `σ`: for every
orthonormal basis `eᵢ` of the tangent space at `x` and every tangent vector `v`,

`∇*∇(∇σ)(v) - ∇_v(∇*∇σ) = ∑ᵢ (2 R(v, eᵢ) ∇_{eᵢ}σ + (∇_{eᵢ}R)(v, eᵢ) σ - ∇_{Rᵀ(v, eᵢ) eᵢ} σ)`

(`roughLaplacian_covariantDerivative_apply_sub_covariantDerivative_roughLaplacian`), where `R` is
the curvature of `∇`, `∇R` its covariant derivative (`CovariantDerivative.derivCurvatureTensor`),
and `Rᵀ` the curvature of `∇ᵀ`. For the Levi-Civita connection, `∑ᵢ Rᵀ(v, eᵢ) eᵢ` is the vector
metric-dual to the Ricci curvature `Ric(v, ·)`. On the trivial line bundle, where
`R = 0`, this is the identity `∇*∇ df = d(∇*∇ f) - Ric(df)` behind the Bochner formula for
functions (`TauCeti.Manifold.laplaceBeltrami_norm_sq_mgradient`).

This is the rule for differentiating an equation of Laplace type once. If `σ` solves
`∇*∇σ = Φ(σ)`, then `∇σ` solves `∇*∇(∇σ) = ∇Φ(σ) + (curvature terms)`, whose curvature terms are of
order zero in `∇σ` and `σ`. Pairing with `∇σ` gives differential inequalities for `|∇σ|²`, the
input of maximum-principle bounds on the gradient such as Taubes's gradient bound for
large-parameter Seiberg–Witten solutions (`TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le`).

Both sides are computed through the third covariant derivative
`∇³σ(u, w, z) = (∇_u ∇²σ)(w, z)`, the covariant derivative of the section `∇²σ` of
`Hom(TM, Hom(TM, V))`:

* `∇*∇(∇σ)(v) = -∑ᵢ ∇³σ(eᵢ, eᵢ, v)`, since the second covariant derivative of `∇σ` is `∇³σ`
  (`CovariantDerivative.secondCovariantDerivative_covariantDerivative`,
  `CovariantDerivative.roughLaplacian_covariantDerivative_apply_eq_sum`);
* `∇_v(∇*∇σ) = -∑ᵢ ∇³σ(v, eᵢ, eᵢ)`, since a metric connection commutes with the metric trace
  (`CovariantDerivative.covariantDerivative_roughLaplacian_eq_sum`, an instance of
  `CovariantDerivative.IsMetricCompatible.covariantDerivative_metricTrace`);
* the Ricci identities for `∇³σ` swap its first two and its last two slots
  (`Curvature/ThirdCovariantDerivative.lean`).

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 9 (the Bochner
  technique and the commutation of covariant derivatives).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the Ricci identities).
-/

public section

open Bundle FiberBundle Filter Riemannian.Tensor
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative covT ∞]
  {σ : Π y : M, V y}

/-! ### The two traces -/

section Trace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **The rough Laplacian of `∇σ`.** For every orthonormal basis `eᵢ` of the tangent space at `x`,
the rough Laplacian of the section `∇σ` of `Hom(TM, V)` is `∇*∇(∇σ)(v) = -∑ᵢ ∇³σ(eᵢ, eᵢ, v)`. -/
theorem roughLaplacian_covariantDerivative_apply_eq_sum (hσ : CMDiff ∞ (T% σ)) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (v : TangentSpace I x) :
    (covT.hom cov).roughLaplacian covT (cov σ) x v =
      -∑ i, covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x (b i) (b i) v := by
  rw [roughLaplacian_eq_sum _ covT _ x b]
  simp only [secondCovariantDerivative_covariantDerivative cov hσ,
    neg_apply, sum_apply]

omit [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative covT ∞] in
/-- **The rough Laplacian in a chart frame.** On the chart domain at `α`, the rough Laplacian is
`∇*∇σ = -∑ᵢ ∇²σ(Fᵢ, Dᵢ)`, where `Fᵢ` is the chart-local frame and `Dᵢ` its metric-dual frame.
Unlike a pointwise choice of orthonormal basis, these frames depend smoothly on the point. -/
theorem roughLaplacian_eq_neg_sum_chartDualFrame (α : M) {y : M}
    (hy : y ∈ (chartAt H α).source) :
    cov.roughLaplacian covT σ y = -∑ i, cov.secondCovariantDerivative covT σ y
      (chartLocalFrame (I := I) α i y) (chartDualFrame (I := I) α i y) := by
  rw [roughLaplacian_def, metricTrace_eq_sum_chartDualFrame α hy]

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The covariant derivative of the rough Laplacian.** For a metric connection `∇ᵀ` and every
orthonormal basis `eᵢ` of the tangent space at `x`, `∇_v(∇*∇σ) = -∑ᵢ ∇³σ(v, eᵢ, eᵢ)`: covariant
differentiation commutes with the metric trace that defines `∇*∇`. -/
theorem covariantDerivative_roughLaplacian_eq_sum
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) covT)
    (hσ : CMDiff ∞ (T% σ)) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (v : TangentSpace I x) :
    cov (cov.roughLaplacian covT σ) x v =
      -∑ i, covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x v (b i) (b i) := by
  have hD2x :=
    (contMDiff_hom_covariantDerivative cov (covT := covT) hσ).mdifferentiableAt (x := x) (by simp)
  -- The rough Laplacian is minus the metric trace of the section `∇²σ` of `Hom(TM, Hom(TM, V))`.
  have hlap : cov.roughLaplacian covT σ = -fun y ↦ LinearMap.BilinMap.metricTrace
      (ContinuousLinearMap.toLinearMap₁₂ (covT.hom cov (cov σ) y)) := by
    funext y
    rw [roughLaplacian_def, Pi.neg_apply,
      secondCovariantDerivative_eq_toLinearMap₁₂_hom cov covT hσ y]
  rw [hlap, cov.isCovariantDerivativeOnUniv.neg hD2x.metricTrace, neg_apply,
    hcov.covariantDerivative_metricTrace cov hD2x v, LinearMap.BilinMap.metricTrace_eq_sum _ b]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-! ### The commutation formula -/

variable [FiniteDimensional ℝ F]

/-- **The commutator of the rough Laplacian with the covariant derivative.** Let `∇ᵀ` be a
torsion-free metric connection on the tangent bundle, such as the Levi-Civita connection, and let
`σ` be a smooth section of `V`. For every orthonormal basis `eᵢ` of the tangent space at `x` and
every tangent vector `v`,

`∇*∇(∇σ)(v) - ∇_v(∇*∇σ) = ∑ᵢ (2 R(v, eᵢ) ∇_{eᵢ}σ + (∇_{eᵢ}R)(v, eᵢ) σ - ∇_{Rᵀ(v, eᵢ) eᵢ} σ)`,

where `∇*∇(∇σ)` is the rough Laplacian of the section `∇σ` of `Hom(TM, V)`, `R` is the curvature
of `∇`, `∇R` its covariant derivative and `Rᵀ` the curvature of `∇ᵀ`. -/
theorem roughLaplacian_covariantDerivative_apply_sub_covariantDerivative_roughLaplacian
    (ht : covT.IsTorsionFree)
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) covT)
    (hσ : CMDiff ∞ (T% σ)) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (v : TangentSpace I x) :
    (covT.hom cov).roughLaplacian covT (cov σ) x v - cov (cov.roughLaplacian covT σ) x v =
      ∑ i, ((2 : ℝ) • cov.curvatureTensor x v (b i) (cov σ x (b i)) +
        cov.derivCurvatureTensor covT x (b i) v (b i) (σ x) -
        cov σ x (covT.curvatureTensor x v (b i) (b i))) := by
  rw [roughLaplacian_covariantDerivative_apply_eq_sum cov covT hσ x b,
    covariantDerivative_roughLaplacian_eq_sum cov covT hcov hσ x b, neg_sub_neg,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Move `v` from the first slot to the last one, one transposition at a time.
  have h₁ := covariantDerivative_secondCovariantDerivative_sub_swap_left_of_isTorsionFree cov ht
    hσ x v (b i) (b i)
  have h₂ := covariantDerivative_secondCovariantDerivative_sub_swap_right_of_isTorsionFree cov ht
    hσ x (b i) v (b i)
  rw [two_smul]
  calc _ = (covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x v (b i) (b i) -
          covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x (b i) v (b i)) +
        (covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x (b i) v (b i) -
          covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x (b i) (b i) v) := by abel
    _ = _ := by rw [h₁, h₂]; abel

end Trace

end CovariantDerivative
