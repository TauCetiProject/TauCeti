/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The energy identity for the rough Laplacian

Let `∇` be a metric connection on a Riemannian vector bundle `V` over a Riemannian manifold `M`
without boundary, and let `∇*∇ σ = -tr_g ∇²σ` be its rough Laplacian
(`CovariantDerivative.roughLaplacian`), built with the Levi-Civita connection on the tangent
bundle. This file proves the **energy identity**

`∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`

for smooth sections `σ`, `τ` one of which has compact support, where
`⟪∇σ, ∇τ⟫ = ∑ᵢ ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫` for any orthonormal basis `eᵢ` of the tangent space
(`CovariantDerivative.innerCovariantDerivative`) is the pointwise inner product of the covariant
derivatives, and `dV` is the Riemannian volume. Its consequences are that `∇*∇` is **formally
self-adjoint** and **nonnegative**:

`∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪σ, ∇*∇ τ⟫ dV`,   `∫ ⟪∇*∇ σ, σ⟫ dV = ∫ |∇σ|² dV ≥ 0`,

and that on a closed manifold the smooth sections with `∇*∇ σ = 0` are exactly the parallel ones.
Together with the principal symbol `σ_F(∇*∇) = |ξ|²_g Id`
(`CovariantDerivative.roughLaplacian_smul_smul_sub`), these are the properties of the rough
Laplacian that make it the model Laplace-type operator on a bundle.

## The argument

Let `X` be the vector field metric-dual to the one-form `w ↦ ⟪∇_w σ, τ⟫`. At a point `x`, with a
smooth vector field `W` and `u = W x`, metric compatibility of the Levi-Civita connection and of
`∇` gives

`⟪∇_u X, W x⟫ = u ⟪∇_W σ, τ⟫ - ⟪X, ∇_u W⟫ = ⟪∇²σ(u, u), τ⟫ + ⟪∇_u σ, ∇_u τ⟫`,

since `∇²σ(u, W x) = ∇_u (∇_W σ) - ∇_{∇_u W} σ`. Tracing over an orthonormal basis,

`div X = ⟪∇σ, ∇τ⟫ - ⟪∇*∇ σ, τ⟫`,

and the divergence theorem `∫ div X dV = 0` (`TauCeti.Manifold.integral_divergence_eq_zero`)
gives the energy identity. The vector field `X` is smooth because its evaluations on a chart frame
are smooth (`Riemannian.Tensor.contMDiffAt_rieszDual`), and it has compact support as soon as `σ`
or `τ` has.

## Main results

* `CovariantDerivative.innerCovariantDerivative`: the pointwise inner product `⟪∇σ, ∇τ⟫`; it is
  smooth (`CovariantDerivative.contMDiff_innerCovariantDerivative`), and `⟪∇σ, ∇σ⟫ = 0` exactly
  where `∇σ = 0` (`CovariantDerivative.innerCovariantDerivative_self_eq_zero_iff`).
* `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian`,
  `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian_of_isCompact_left`:
  **the energy identity**, when `τ`, respectively `σ`, has compact support.
* `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian_comm`: the rough
  Laplacian is formally self-adjoint.
* `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian_self_nonneg`: it is
  nonnegative.
* `CovariantDerivative.IsMetricCompatible.roughLaplacian_eq_zero_iff`: on a compact manifold a
  smooth section satisfies `∇*∇ σ = 0` if and only if it is parallel.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §8 (the connection Laplacian is formally self-adjoint and nonnegative).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence theorem) and Chapter 4 (the second covariant derivative).
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open TauCeti (riemannianVolume)
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

/-! ### The pointwise inner product of covariant derivatives -/

/-- The pointwise inner product `⟪∇σ, ∇τ⟫ = ∑ᵢ ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫` of the covariant
derivatives of two sections at `x`, for any orthonormal basis `eᵢ` of the tangent space
(`CovariantDerivative.innerCovariantDerivative_eq_sum`): the metric trace of the bilinear form
`(u, v) ↦ ⟪∇_u σ, ∇_v τ⟫`. It is the inner product of `∇σ` and `∇τ` as sections of `T*M ⊗ V`,
and `⟪∇σ, ∇σ⟫ = |∇σ|²` is the squared Hilbert–Schmidt norm of `∇σ` at `x`. -/
def innerCovariantDerivative (σ τ : Π x : M, V x) (x : M) : ℝ :=
  TauCeti.bilinFormTrace ((innerₗ (V x)).compl₁₂ (cov σ x : TangentSpace I x →ₗ[ℝ] V x)
    (cov τ x : TangentSpace I x →ₗ[ℝ] V x))

/-- The inner product of covariant derivatives in an orthonormal basis:
`⟪∇σ, ∇τ⟫ = ∑ᵢ ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫`. -/
theorem innerCovariantDerivative_eq_sum (σ τ : Π x : M, V x) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.innerCovariantDerivative σ τ x = ∑ i, ⟪cov σ x (b i), cov τ x (b i)⟫ := by
  simp only [innerCovariantDerivative, TauCeti.bilinFormTrace_eq_sum _ b,
    LinearMap.compl₁₂_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe]

/-- The inner product of covariant derivatives is symmetric: `⟪∇σ, ∇τ⟫ = ⟪∇τ, ∇σ⟫`. -/
theorem innerCovariantDerivative_comm (σ τ : Π x : M, V x) (x : M) :
    cov.innerCovariantDerivative σ τ x = cov.innerCovariantDerivative τ σ x := by
  simp only [cov.innerCovariantDerivative_eq_sum _ _ x (stdOrthonormalBasis ℝ _),
    real_inner_comm (cov σ x _)]

/-- `⟪∇σ, ∇σ⟫ = ∑ᵢ |∇_{eᵢ} σ|²` in an orthonormal basis. -/
theorem innerCovariantDerivative_self_eq_sum (σ : Π x : M, V x) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.innerCovariantDerivative σ σ x = ∑ i, ‖cov σ x (b i)‖ ^ 2 := by
  simp only [cov.innerCovariantDerivative_eq_sum _ _ x b, real_inner_self_eq_norm_sq]

/-- `⟪∇σ, ∇σ⟫ = |∇σ|²` is nonnegative. -/
theorem innerCovariantDerivative_self_nonneg (σ : Π x : M, V x) (x : M) :
    0 ≤ cov.innerCovariantDerivative σ σ x := by
  rw [cov.innerCovariantDerivative_self_eq_sum σ x (stdOrthonormalBasis ℝ _)]
  positivity

/-- `⟪∇σ, ∇σ⟫` vanishes at `x` exactly when the covariant derivative of `σ` vanishes at `x`. -/
theorem innerCovariantDerivative_self_eq_zero_iff (σ : Π x : M, V x) (x : M) :
    cov.innerCovariantDerivative σ σ x = 0 ↔ cov σ x = 0 := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [cov.innerCovariantDerivative_self_eq_sum σ x b,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by positivity]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, norm_eq_zero]
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h i ↦ by simp [h]⟩
  rw [← b.sum_repr' v]
  simp [h]

section Smooth

variable [VectorBundle ℝ F V] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [ContMDiffCovariantDerivative cov ∞]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] in
/-- The covariant derivative of a smooth section along a member of a chart frame is smooth at
every point of the chart source. -/
private theorem contMDiffAt_apply_chartLocalFrame (hσ : CMDiff ∞ (T% σ)) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (j : Fin (Module.finrank ℝ E)) :
    CMDiffAt ∞ (T% (fun y ↦ cov σ y (chartLocalFrame (I := I) α j y))) x := by
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have hframe : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) α j y)) x := by
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    exact (contMDiffOn_chartLocalFrame (I := I) (n := ∞) α j).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds (by simpa using hx))
  exact ((contMDiffOn_univ.mp
    (ContMDiffCovariantDerivative.contMDiff.contMDiff hσ'.contMDiffOn)) x).clm_bundle_apply hframe

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
/-- The inner product `⟪∇σ, ∇τ⟫` of the covariant derivatives of two smooth sections is a smooth
function. -/
theorem contMDiff_innerCovariantDerivative (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) :
    ContMDiff I 𝓘(ℝ) ∞ (cov.innerCovariantDerivative σ τ) := by
  intro x
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  -- On the chart source, the metric trace is read off with the inverse Gram matrix.
  have heq : (fun y ↦ ∑ i, ∑ j, chartInvGramMatrix (I := I) x y i j *
      ⟪cov σ y (chartLocalFrame (I := I) x i y), cov τ y (chartLocalFrame (I := I) x j y)⟫)
      =ᶠ[𝓝 x] cov.innerCovariantDerivative σ τ := by
    filter_upwards [hopen.mem_nhds (mem_chart_source H x)] with y hy
    simp only [innerCovariantDerivative, bilinFormTrace_eq_sum_chartInvGramMatrix x hy,
      LinearMap.compl₁₂_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq.symm
  refine contMDiffAt_finsetSum fun i _ ↦ contMDiffAt_finsetSum fun j _ ↦ ?_
  have hG : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ chartInvGramMatrix (I := I) x y i j) x := by
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    exact (contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) x i j).contMDiffAt
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds (by simp))
  exact hG.mul ((cov.contMDiffAt_apply_chartLocalFrame hσ x (mem_chart_source H x) i).inner_bundle
    (cov.contMDiffAt_apply_chartLocalFrame hτ x (mem_chart_source H x) j))

/-! ### The vector field dual to `⟪∇σ, τ⟫` -/

/-- The vector field metric-dual to the one-form `w ↦ ⟪∇_w σ, τ⟫`. -/
private def pairingField (σ τ : Π x : M, V x) (y : M) : TangentSpace I y :=
  rieszDual y ((innerSL ℝ (τ y)).comp (cov σ y))

omit [VectorBundle ℝ F V] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [ContMDiffCovariantDerivative cov ∞] in
private theorem inner_pairingField (y : M) (w : TangentSpace I y) :
    ⟪cov.pairingField σ τ y, w⟫ = ⟪cov σ y w, τ y⟫ := by
  rw [pairingField, inner_rieszDual]
  simp [real_inner_comm]

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiff_pairingField (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) :
    ContMDiff I I.tangent ∞ (T% (cov.pairingField σ τ)) := by
  intro x
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  refine contMDiffAt_rieszDual (n := ∞) x (mem_chart_source H x) fun j ↦ ?_
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using
    (cov.contMDiffAt_apply_chartLocalFrame hσ x (mem_chart_source H x) j).inner_bundle (hτ x)

/-- The divergence of the vector field dual to `⟪∇σ, τ⟫` is `⟪∇σ, ∇τ⟫ - ⟪∇*∇ σ, τ⟫`. -/
private theorem divergence_pairingField [FiniteDimensional ℝ F] (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) (x : M) :
    TauCeti.Manifold.divergence I (cov.pairingField σ τ) x =
      cov.innerCovariantDerivative σ τ x -
        ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ := by
  set covT := leviCivitaConnection I M
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hXd : MDiffAt (T% (cov.pairingField σ τ)) x :=
    (cov.contMDiff_pairingField hσ hτ).mdifferentiableAt (by simp)
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have hτd : MDiffAt (T% τ) x := hτ.mdifferentiable (by simp) x
  -- Each diagonal term of the divergence is `⟪∇²σ(eᵢ, eᵢ), τ⟫ + ⟪∇_{eᵢ} σ, ∇_{eᵢ} τ⟫`.
  have hterm (i) : ⟪leviCivitaConnection I M (cov.pairingField σ τ) x (b i), b i⟫ =
      ⟪cov.secondCovariantDerivative covT σ x (b i) (b i), τ x⟫ +
        ⟪cov σ x (b i), cov τ x (b i)⟫ := by
    obtain ⟨W, hW, hWx⟩ := exists_contMDiff_section_eq I E ∞ (b i)
    have hWd : MDiffAt (T% W) x := hW.mdifferentiable (by simp) x
    have hσWd : MDiffAt (T% (fun y ↦ cov σ y (W y))) x :=
      (cov.contMDiff_apply hW hσ').mdifferentiable (by simp) x
    have hLC := (isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      (FiberBundle.extend E (b i)) hXd hWd
    have hV := hcov.mvfderiv_inner_eq (FiberBundle.extend E (b i)) hσWd hτd
    have hfun : (fun y ↦ ⟪cov.pairingField σ τ y, W y⟫) = fun y ↦ ⟪cov σ y (W y), τ y⟫ :=
      funext fun y ↦ cov.inner_pairingField y (W y)
    have hS := cov.secondCovariantDerivative_apply covT hσ x hW (b i)
    simp only [FiberBundle.extend_apply_self] at hLC hV
    rw [hfun, hV, cov.inner_pairingField] at hLC
    rw [hWx] at hLC hS
    rw [hS, inner_sub_left]
    linarith
  rw [TauCeti.Manifold.divergence_eq_sum_inner I _ x b, cov.innerCovariantDerivative_eq_sum σ τ x b,
    cov.roughLaplacian_eq_sum covT σ x b]
  simp only [hterm, Finset.sum_add_distrib, inner_neg_left, sum_inner]
  ring

end Smooth

/-! ### The energy identity -/

namespace IsMetricCompatible

variable [VectorBundle ℝ F V] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [T2Space M]
  [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [ContMDiffCovariantDerivative cov ∞] [I.Boundaryless] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The covariant derivative of a smooth section vanishes off the closure of its nonzero locus. -/
private theorem apply_eq_zero_of_notMem_closure (hσ : CMDiff ∞ (T% σ)) {y : M}
    (hy : y ∉ closure {x | σ x ≠ 0}) : cov σ y = 0 := by
  have hev : ∀ᶠ z in 𝓝 y, σ z = (0 : Π x : M, V x) z := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
    by_contra h
    exact hz (subset_closure h)
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (hσ.mdifferentiable (by simp) y)
    (mdifferentiableAt_zeroSection ..) Filter.univ_mem hev]
  exact congrFun cov.zero y

/-- The energy identity, when the vector field dual to `⟪∇σ, τ⟫` and the function `⟪∇σ, ∇τ⟫`
both vanish off a compact set. -/
private theorem integral_inner_roughLaplacian_of_subset (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) {K : Set M} (hK : IsCompact K)
    (hKc : IsClosed K) (hX : ∀ y ∉ K, cov.pairingField σ τ y = 0)
    (hB : ∀ y ∉ K, cov.innerCovariantDerivative σ τ y = 0) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M := by
  have hXc : HasCompactSupport (β := E) (cov.pairingField σ τ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun y hy ↦ by
      by_contra h
      exact hy (hX y h)) hKc)
  have hBc : HasCompactSupport (cov.innerCovariantDerivative σ τ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun y hy ↦ by
      by_contra h
      exact hy (hB y h)) hKc)
  have hX1 : ContMDiff I I.tangent 1 (T% (cov.pairingField σ τ)) :=
    (cov.contMDiff_pairingField hσ hτ).of_le (by simp)
  have hBi : Integrable (cov.innerCovariantDerivative σ τ) (riemannianVolume I M) :=
    (cov.contMDiff_innerCovariantDerivative hσ hτ).continuous.integrable_of_hasCompactSupport hBc
  have hdiv := TauCeti.Manifold.integral_divergence_eq_zero hX1 hXc
  simp_rw [cov.divergence_pairingField hcov hσ hτ] at hdiv
  rw [integral_sub hBi] at hdiv
  · linarith
  · refine (hBi.sub (TauCeti.Manifold.integrable_divergence hX1 hXc)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, cov.divergence_pairingField hcov hσ hτ]
    ring

/-- **The energy identity for the rough Laplacian.** For a metric connection `∇` on a Riemannian
vector bundle over a manifold without boundary, and smooth sections `σ` and `τ` where `τ` has
compact support, `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`. -/
theorem integral_inner_roughLaplacian (hcov : cov.IsMetricCompatible) (hσ : CMDiff ∞ (T% σ))
    (hτ : CMDiff ∞ (T% τ)) (hτc : IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M := by
  refine integral_inner_roughLaplacian_of_subset hcov hσ hτ hτc isClosed_closure
    (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · have hτy : τ y = 0 := by
      by_contra h
      exact hy (subset_closure h)
    simp [pairingField, hτy, LinearIsometryEquiv.map_zero]
  · simp [cov.innerCovariantDerivative_eq_sum σ τ y (stdOrthonormalBasis ℝ _),
      apply_eq_zero_of_notMem_closure hτ hy]

/-- **The energy identity for the rough Laplacian**, when the first section has compact
support: `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`. -/
theorem integral_inner_roughLaplacian_of_isCompact_left (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M :=
  integral_inner_roughLaplacian_of_subset hcov hσ hτ hσc isClosed_closure
    (fun y hy ↦ by
      simp [pairingField, apply_eq_zero_of_notMem_closure hσ hy, LinearIsometryEquiv.map_zero])
    (fun y hy ↦ by
      simp [cov.innerCovariantDerivative_eq_sum σ τ y (stdOrthonormalBasis ℝ _),
        apply_eq_zero_of_notMem_closure hσ hy])

/-- **The rough Laplacian is formally self-adjoint.** For a metric connection and smooth sections
`σ` and `τ` where `τ` has compact support, `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪σ, ∇*∇ τ⟫ dV`. -/
theorem integral_inner_roughLaplacian_comm (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) (hτc : IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, ⟪σ x, cov.roughLaplacian (leviCivitaConnection I M) τ x⟫ ∂riemannianVolume I M := by
  calc _ = ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M :=
        hcov.integral_inner_roughLaplacian hσ hτ hτc
    _ = ∫ x, cov.innerCovariantDerivative τ σ x ∂riemannianVolume I M :=
        integral_congr_ae (.of_forall fun x ↦ cov.innerCovariantDerivative_comm σ τ x)
    _ = ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) τ x, σ x⟫ ∂riemannianVolume I M :=
        (hcov.integral_inner_roughLaplacian_of_isCompact_left hτ hσ hτc).symm
    _ = _ := integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _)

/-- **The rough Laplacian is nonnegative.** For a metric connection and a compactly supported
smooth section `σ`, `∫ ⟪∇*∇ σ, σ⟫ dV = ∫ |∇σ|² dV ≥ 0`. -/
theorem integral_inner_roughLaplacian_self_nonneg (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    0 ≤ ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫ ∂riemannianVolume I M := by
  rw [hcov.integral_inner_roughLaplacian hσ hσ hσc]
  exact integral_nonneg fun x ↦ cov.innerCovariantDerivative_self_nonneg σ x

omit [SigmaCompactSpace M] in
/-- **The kernel of the rough Laplacian on a closed manifold.** For a metric connection on a
Riemannian vector bundle over a compact manifold without boundary, a smooth section satisfies
`∇*∇ σ = 0` if and only if it is parallel, `∇σ = 0`. -/
theorem roughLaplacian_eq_zero_iff [CompactSpace M] (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) :
    cov.roughLaplacian (leviCivitaConnection I M) σ = 0 ↔ cov σ = 0 := by
  constructor
  · intro h
    have hσc : IsCompact (closure {x | σ x ≠ 0}) := isClosed_closure.isCompact
    have hint := hcov.integral_inner_roughLaplacian hσ hσ hσc
    simp only [h, Pi.zero_apply, inner_zero_left, integral_zero] at hint
    have hcont := (cov.contMDiff_innerCovariantDerivative hσ hσ).continuous
    -- `⟪∇σ, ∇σ⟫` is continuous and nonnegative with integral zero, so it vanishes everywhere.
    have hzero : cov.innerCovariantDerivative σ σ = 0 :=
      (hcont.ae_eq_iff_eq _ continuous_zero).1 ((integral_eq_zero_iff_of_nonneg
        (cov.innerCovariantDerivative_self_nonneg σ)
        (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1
        hint.symm)
    exact funext fun x ↦ (cov.innerCovariantDerivative_self_eq_zero_iff σ x).1 (congrFun hzero x)
  · intro hcov0
    funext x
    rw [cov.roughLaplacian_eq_sum (leviCivitaConnection I M) σ x (stdOrthonormalBasis ℝ _)]
    refine neg_eq_zero.2 (Finset.sum_eq_zero fun i _ ↦ ?_)
    obtain ⟨W, hW, hWx⟩ := exists_contMDiff_section_eq I E ∞ (stdOrthonormalBasis ℝ _ i)
    have hW0 : (fun y ↦ cov σ y (W y)) = 0 := funext fun y ↦ by simp [hcov0]
    rw [← hWx, cov.secondCovariantDerivative_apply _ hσ x hW, hW0]
    simp [hcov0]

end IsMetricCompatible

end CovariantDerivative
