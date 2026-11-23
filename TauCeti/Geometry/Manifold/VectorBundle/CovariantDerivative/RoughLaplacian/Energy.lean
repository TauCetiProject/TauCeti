/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.FormalAdjoint
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Pairing
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

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

The rough Laplacian is the composite `∇*∇ σ = ∇*(∇σ)` of the connection and its formal adjoint
(`CovariantDerivative.roughLaplacian_eq_formalAdjoint`), so the energy identity is the case
`ω = ∇σ` of the integration by parts `∫ ⟪∇*ω, τ⟫ dV = ∫ ⟪ω, ∇τ⟫ dV` for `V`-valued one-forms
(`CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint`), which comes from the
divergence theorem. The one-form `∇σ` has compact support as soon as `σ` has.

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
  [FiberBundle F V] {σ τ : Π x : M, V x}

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

/-- **The energy identity for the rough Laplacian.** For a metric connection `∇` on a Riemannian
vector bundle over a manifold without boundary, and smooth sections `σ` and `τ` where `τ` has
compact support, `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`. -/
theorem integral_inner_roughLaplacian (hcov : cov.IsMetricCompatible) (hσ : CMDiff ∞ (T% σ))
    (hτ : CMDiff ∞ (T% τ)) (hτc : IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M := by
  simp only [roughLaplacian_eq_formalAdjoint cov _ hσ, innerCovariantDerivative_def]
  exact hcov.integral_inner_formalAdjoint
    (cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)) hτ hτc

/-- **The energy identity for the rough Laplacian**, when the first section has compact
support: `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`. -/
theorem integral_inner_roughLaplacian_of_isCompact_left (hcov : cov.IsMetricCompatible)
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, cov.innerCovariantDerivative σ τ x ∂riemannianVolume I M := by
  -- `∇σ` vanishes off the closure of the nonzero locus of `σ`, so it has compact support.
  have hc : closure {x | cov σ x ≠ 0} ⊆ closure {x | σ x ≠ 0} :=
    closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (cov.apply_eq_zero_of_notMem_closure h))
      isClosed_closure
  simp only [roughLaplacian_eq_formalAdjoint cov _ hσ, innerCovariantDerivative_def]
  exact hcov.integral_inner_formalAdjoint_of_isCompact_left
    (cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)) hτ
    (hσc.of_isClosed_subset isClosed_closure hc)

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
