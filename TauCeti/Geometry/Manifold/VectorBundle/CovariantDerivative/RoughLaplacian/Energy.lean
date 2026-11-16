/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Pairing
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

* `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian`,
  `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian_of_isCompact_left`:
  **the energy identity**, when `τ`, respectively `σ`, has compact support.
* `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian_left_eq_right`: the rough
  Laplacian is formally self-adjoint.
* `CovariantDerivative.IsMetricCompatible.integral_inner_roughLaplacian_self_nonneg`: it is
  nonnegative.
* `CovariantDerivative.IsMetricCompatible.apply_eq_zero_of_roughLaplacian_eq_zero`: a
  compactly supported smooth section with `∇*∇ σ = 0` is parallel.
* `CovariantDerivative.IsMetricCompatible.roughLaplacian_eq_zero_iff_apply_eq_zero`: on a compact
  manifold a smooth section satisfies `∇*∇ σ = 0` if and only if it is parallel.

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

section Smooth

variable [VectorBundle ℝ F V] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [ContMDiffCovariantDerivative cov ∞]

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
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  refine contMDiffAt_rieszDual (n := ∞) x (mem_chart_source H x) fun j ↦ ?_
  have hframe : CMDiffAt ∞ (T% (chartLocalFrame (I := I) x j)) x :=
    contMDiffAt_chartLocalFrame (I := I) (n := ∞) x j
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using
    (cov.contMDiffAt_apply hframe hσ').inner_bundle (hτ x)

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

/-- The energy identity, when the vector field dual to `⟪∇σ, τ⟫` and the function `⟪∇σ, ∇τ⟫`
both vanish off a compact set. -/
private theorem integral_inner_roughLaplacian_of_subset (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) {K : Set M} (hK : IsCompact K)
    (hKc : IsClosed K) (hX : ∀ y ∉ K, cov.pairingField σ τ y = 0)
    (hB : ∀ y ∉ K, cov.innerCovariantDerivative σ τ y = 0) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M := by
  have hXc : HasCompactSupport (β := E) (cov.pairingField σ τ) := .intro' hK hKc hX
  have hBc : HasCompactSupport (cov.innerCovariantDerivative σ τ) := .intro' hK hKc hB
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
  · exact cov.innerCovariantDerivative_eq_zero_of_notMem_closure_right hy

/-- **The energy identity for the rough Laplacian**, when the first section has compact
support: `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`. -/
theorem integral_inner_roughLaplacian_of_isCompact_left (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M :=
  integral_inner_roughLaplacian_of_subset hcov hσ hτ hσc isClosed_closure
    (fun y hy ↦ by
      simp [pairingField, cov.apply_eq_zero_of_notMem_closure hy, LinearIsometryEquiv.map_zero])
    (fun _ ↦ cov.innerCovariantDerivative_eq_zero_of_notMem_closure_left)

/-- **The rough Laplacian is formally self-adjoint.** For a metric connection and smooth sections
`σ` and `τ` where `τ` has compact support, `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪σ, ∇*∇ τ⟫ dV`. -/
theorem integral_inner_roughLaplacian_left_eq_right (hcov : cov.IsMetricCompatible)
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

/-- **A compactly supported smooth section in the kernel of the rough Laplacian is parallel.**
For a metric connection on a Riemannian vector bundle over a manifold without boundary, a smooth
section `σ` with compact support and `∇*∇ σ = 0` satisfies `∇σ = 0`. -/
theorem apply_eq_zero_of_roughLaplacian_eq_zero (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0}))
    (h : cov.roughLaplacian (leviCivitaConnection I M) σ = 0) : cov σ = 0 := by
  have hint := hcov.integral_inner_roughLaplacian hσ hσ hσc
  simp only [h, Pi.zero_apply, inner_zero_left, integral_zero] at hint
  have hcont := (cov.contMDiff_innerCovariantDerivative hσ hσ).continuous
  have hBc : HasCompactSupport (cov.innerCovariantDerivative σ σ) :=
    .intro' hσc isClosed_closure fun _ ↦ cov.innerCovariantDerivative_eq_zero_of_notMem_closure_left
  -- `⟪∇σ, ∇σ⟫` is continuous and nonnegative with integral zero, so it vanishes everywhere.
  have hzero : cov.innerCovariantDerivative σ σ = 0 :=
    (hcont.ae_eq_iff_eq _ continuous_zero).1 ((integral_eq_zero_iff_of_nonneg
      (cov.innerCovariantDerivative_self_nonneg σ) (hcont.integrable_of_hasCompactSupport hBc)).1
      hint.symm)
  exact funext fun x ↦ (cov.innerCovariantDerivative_self_eq_zero_iff σ x).1 (congrFun hzero x)

omit [SigmaCompactSpace M] in
/-- **The kernel of the rough Laplacian on a closed manifold.** For a metric connection on a
Riemannian vector bundle over a compact manifold without boundary, a smooth section satisfies
`∇*∇ σ = 0` if and only if it is parallel, `∇σ = 0`. -/
theorem roughLaplacian_eq_zero_iff_apply_eq_zero [CompactSpace M]
    (hcov : cov.IsMetricCompatible) (hσ : CMDiff ∞ (T% σ)) :
    cov.roughLaplacian (leviCivitaConnection I M) σ = 0 ↔ cov σ = 0 :=
  ⟨hcov.apply_eq_zero_of_roughLaplacian_eq_zero hσ isClosed_closure.isCompact,
    cov.roughLaplacian_eq_zero_of_apply_eq_zero _ hσ⟩

end IsMetricCompatible

end CovariantDerivative
