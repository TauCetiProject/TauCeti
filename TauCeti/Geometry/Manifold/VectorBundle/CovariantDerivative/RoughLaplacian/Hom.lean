/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Extension
import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.MaximumPrinciple
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Topology.VectorBundle.DiscSphere

/-!
# The rough Laplacian of a bundle map and Hamilton's maximum principle

Let `∇` be connections on vector bundles `V` and `W` over a manifold `M`, with the induced
connection on the bundle `Hom(V, W)` (`CovariantDerivative.hom`), and let `∇ᵀ` be a connection on
the tangent bundle. For a smooth bundle map `A` and a smooth section `s` of `V`, the second
covariant derivative of `A s` obeys the Leibniz rule

`∇²(A s)(u, w) = (∇²A)(u, w) s + (∇_u A)(∇_w s) + (∇_w A)(∇_u s) + A ∇²s(u, w)`

(`CovariantDerivative.secondCovariantDerivative_clm_apply`, in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom`).
Taking the metric trace gives the rough Laplacian `∇*∇ = -tr ∇²` of `A s`:

`∇*∇(A s) = (∇*∇A) s - 2 ∑ᵢ (∇_{eᵢ} A)(∇_{eᵢ} s) + A ∇*∇s`

(`CovariantDerivative.roughLaplacian_clm_apply`).

For an endomorphism field `A` of a Riemannian bundle `V` with a metric connection, and a section
`s` with `∇s (x) = 0`, the Laplace–Beltrami operator `Δ = div ∘ grad` of `⟪A s, s⟫` at `x` is

`Δ ⟪A s, s⟫ = -⟪(∇*∇A) s, s⟫ - ⟪A ∇*∇s, s⟫ - ⟪A s, ∇*∇s⟫`

(`CovariantDerivative.IsMetricCompatible.laplaceBeltrami_inner_clm_apply_of_cov_eq_zero`). If
moreover `A x` is symmetric with eigenvector `s x` of eigenvalue `c`, and `⟪A s, s⟫ ≥ c |s|²`
near `x` with equality at `x`, then `Δ (c |s|²) ≤ Δ ⟪A s, s⟫` at `x`, and the two terms in
`∇*∇s` cancel against `c Δ |s|²`. What remains is the sign `⟪(∇*∇A) s, s⟫ ≤ 0` at `x`
(`CovariantDerivative.IsMetricCompatible.inner_roughLaplacian_hom_apply_nonpos`).

This is the key step of **Hamilton's maximum principle for symmetric tensors**. On a compact
boundaryless Riemannian manifold, let `A` be a smooth field of symmetric endomorphisms of the
tangent bundle. The quadratic form `⟪A v, v⟫` attains its minimum `m` on the compact unit tangent
bundle at some unit vector `v ∈ T_x M`, which is then an eigenvector of `A x` for its least
eigenvalue `m`; by `TauCeti.Manifold.exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero`
it extends to a smooth vector field parallel at `x`. Hence, if `⟪(∇*∇A) v, v⟫ > 0` at every such
minimizing unit vector whose value is below `-C`, then `A ≥ -C`, that is
`-C |u|² ≤ ⟪A u, u⟫` for every tangent vector `u`
(`TauCeti.Manifold.forall_le_inner_apply_self_of_inner_roughLaplacian_pos`). The least eigenvalue
of `A` is never differentiated, so crossings of eigenvalues cause no difficulty.

`TauCeti.Manifold.forall_le_apply_self_of_laplaceBeltrami_neg` is the version for a family of
bilinear forms on one fixed vector space, where `Δ` acts on the coefficients. The version here
is intrinsic: the hypothesis is stated with the rough Laplacian of `A` for the connection induced
by the Levi-Civita connection, as it is computed from Weitzenböck formulas. In Taubes's analysis
of the large-parameter Seiberg–Witten equations on a symplectic four-manifold, `A` is the
Hermitian part of the curvature of the connection on the twisting line, viewed as an endomorphism
through the metric, and the lower bound `A ≥ -C` gives the refined bound on the anti-self-dual
curvature (`TauCeti.SeibergWitten.norm_smul_sub_hodgeStar_le`).

## Main results

* `CovariantDerivative.roughLaplacian_clm_apply`: the Leibniz rule for `∇*∇(A s)`.
* `CovariantDerivative.IsMetricCompatible.laplaceBeltrami_inner_clm_apply_of_cov_eq_zero`:
  `Δ ⟪A s, s⟫` at a point where `s` is parallel.
* `CovariantDerivative.IsMetricCompatible.inner_roughLaplacian_hom_apply_nonpos`:
  `⟪(∇*∇A) s, s⟫ ≤ 0` where `s` is parallel and minimizes the quadratic form of `A`.
* `CovariantDerivative.IsMetricCompatible.forall_le_inner_apply_self_of_inner_roughLaplacian_pos`:
  Hamilton's maximum principle `A ≥ -C` for a bundle whose vectors extend to sections parallel
  at their base point.
* `TauCeti.Manifold.forall_le_inner_apply_self_of_inner_roughLaplacian_pos`: Hamilton's maximum
  principle `A ≥ -C` for a field of symmetric endomorphisms of the tangent bundle.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4 (the maximum principle for symmetric tensors).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 4
  (induced connections and second covariant derivatives).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W I]
  (covV : _root_.CovariantDerivative I F V) (covW : _root_.CovariantDerivative I G W)
  [ContMDiffCovariantDerivative covV ∞] [ContMDiffCovariantDerivative covW ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {A : Π x : M, V x →L[ℝ] W x} {s : Π x : M, V x}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **The Leibniz rule for the rough Laplacian of a bundle map applied to a section.** For a
smooth section `A` of `Hom(V, W)`, a smooth section `s` of `V` and an orthonormal basis `eᵢ` of
the tangent space at `x`, `∇*∇(A s) = (∇*∇A) s - 2 ∑ᵢ (∇_{eᵢ} A)(∇_{eᵢ} s) + A ∇*∇s` at `x`. -/
theorem roughLaplacian_clm_apply
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x (A x)))
    (hs : CMDiff ∞ (T% s)) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    covW.roughLaplacian covT (fun y ↦ A y (s y)) x =
      (covV.hom covW).roughLaplacian covT A x (s x) -
        2 • ∑ i, covV.hom covW A x (b i) (covV s x (b i)) +
        A x (covV.roughLaplacian covT s x) := by
  rw [roughLaplacian_eq_sum covW covT _ x b, roughLaplacian_eq_sum (covV.hom covW) covT _ x b,
    roughLaplacian_eq_sum covV covT _ x b]
  simp only [secondCovariantDerivative_clm_apply covV covW covT hA hs, Finset.sum_add_distrib,
    neg_apply, sum_apply, map_neg, map_sum, two_smul]
  abel

end CovariantDerivative

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
  {A : Π x : M, V x →L[ℝ] V x} {s : Π x : M, V x}

/-- **The Laplacian of the quadratic form of an endomorphism field at a parallel point.** For a
metric connection on a Riemannian bundle `V`, a smooth endomorphism field `A` and a smooth section
`s` with `∇s (x) = 0`, the Laplace–Beltrami operator of `⟪A s, s⟫` at `x` is
`-⟪(∇*∇A) s, s⟫ - ⟪A ∇*∇s, s⟫ - ⟪A s, ∇*∇s⟫`, where `∇*∇` is the rough Laplacian built with the
Levi-Civita connection and `A` is differentiated with the induced connection on `Hom(V, V)`. -/
theorem laplaceBeltrami_inner_clm_apply_of_cov_eq_zero (hcov : cov.IsMetricCompatible)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (A x)))
    (hs : CMDiff ∞ (T% s)) {x : M} (hs₀ : cov s x = 0) :
    TauCeti.Manifold.laplaceBeltrami I (fun y ↦ ⟪A y (s y), s y⟫) x =
      -⟪(cov.hom cov).roughLaplacian (leviCivitaConnection I M) A x (s x), s x⟫ -
        ⟪A x (cov.roughLaplacian (leviCivitaConnection I M) s x), s x⟫ -
        ⟪A x (s x), cov.roughLaplacian (leviCivitaConnection I M) s x⟫ := by
  set LC := leviCivitaConnection I M
  set t : Π y : M, V y := fun y ↦ A y (s y) with ht_def
  have ht : CMDiff ∞ (T% t) := hA.clm_bundle_apply hs
  have hp : CMDiff ∞ (T% (t + s)) := ht.add_section hs
  have hm : CMDiff ∞ (T% (t - s)) := ht.sub_section hs
  -- Polarization: `⟪A s, s⟫ = (‖A s + s‖² - ‖A s - s‖²) / 4`.
  have hpol : (fun y ↦ ⟪A y (s y), s y⟫) =
      (1 / 4 : ℝ) • ((fun y ↦ ‖(t + s) y‖ ^ 2) - fun y ↦ ‖(t - s) y‖ ^ 2) := by
    funext y
    simp only [ht_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_comm (s y) (A y (s y))]
    ring
  have hsq : ∀ {σ : Π y : M, V y}, CMDiff ∞ (T% σ) →
      ContMDiff I 𝓘(ℝ) 2 (fun y ↦ ‖σ y‖ ^ 2) := fun hσ ↦
    ((TauCeti.contMDiff_norm_sq_bundle I ∞ F V).comp hσ).of_le (by simp)
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hcovt : ∀ i, cov (t + s) x (b i) = cov (t - s) x (b i) := fun i ↦ by
    rw [cov.isCovariantDerivativeOnUniv.add ((ht x).mdifferentiableAt (by simp))
      ((hs x).mdifferentiableAt (by simp)),
      cov.isCovariantDerivativeOnUniv.sub ((ht x).mdifferentiableAt (by simp))
      ((hs x).mdifferentiableAt (by simp)), hs₀]
    simp
  have hRt : cov.roughLaplacian LC t x =
      (cov.hom cov).roughLaplacian LC A x (s x) + A x (cov.roughLaplacian LC s x) := by
    rw [ht_def, roughLaplacian_clm_apply cov cov LC hA hs x b, hs₀]
    simp
  have hd : ContMDiff I 𝓘(ℝ) 2 ((fun y ↦ ‖(t + s) y‖ ^ 2) - fun y ↦ ‖(t - s) y‖ ^ 2) :=
    (hsq hp).sub (hsq hm)
  rw [hpol, TauCeti.Manifold.laplaceBeltrami_smul I _ hd,
    TauCeti.Manifold.laplaceBeltrami_sub I (hsq hp) (hsq hm),
    hcov.laplaceBeltrami_norm_sq hp x b, hcov.laplaceBeltrami_norm_sq hm x b,
    roughLaplacian_add cov LC ht hs, roughLaplacian_sub cov LC ht hs, hRt]
  simp only [hcovt, Pi.add_apply, Pi.sub_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  rw [real_inner_comm (cov.roughLaplacian LC s x) (t x)]
  ring

variable [I.Boundaryless]

/-- **The rough Laplacian of an endomorphism field at a minimizing parallel vector.** On a
boundaryless manifold, let `A` be a smooth endomorphism field of a Riemannian bundle with a metric
connection, and `s` a smooth section with `∇s (x) = 0`. If `A x` is symmetric with eigenvector
`s x` of eigenvalue `c`, and `c ‖s y‖² ≤ ⟪A y (s y), s y⟫` for `y` near `x`, then
`⟪(∇*∇A) (s x), s x⟫ ≤ 0`. This is the pointwise step of Hamilton's maximum principle: the
function `⟪A s, s⟫ - c ‖s‖²` has a local minimum `0` at `x`, and its Laplacian there is
`-⟪(∇*∇A) s, s⟫`. -/
theorem inner_roughLaplacian_hom_apply_nonpos (hcov : cov.IsMetricCompatible)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (A x)))
    (hs : CMDiff ∞ (T% s)) {x : M} (hs₀ : cov s x = 0)
    (hsym : (A x : V x →ₗ[ℝ] V x).IsSymmetric) {c : ℝ} (heig : A x (s x) = c • s x)
    (hle : ∀ᶠ y in 𝓝 x, c * ‖s y‖ ^ 2 ≤ ⟪A y (s y), s y⟫) :
    ⟪(cov.hom cov).roughLaplacian (leviCivitaConnection I M) A x (s x), s x⟫ ≤ 0 := by
  have hf : ContMDiff I 𝓘(ℝ) 2 (fun y ↦ ⟪A y (s y), s y⟫) :=
    ((hA.clm_bundle_apply hs).inner_bundle hs).of_le (by simp)
  have hn : ContMDiff I 𝓘(ℝ) 2 (fun y ↦ ‖s y‖ ^ 2) :=
    ((TauCeti.contMDiff_norm_sq_bundle I ∞ F V).comp hs).of_le (by simp)
  have hcn : ContMDiff I 𝓘(ℝ) 2 (c • fun y ↦ ‖s y‖ ^ 2) :=
    ((contMDiff_const (c := c)).mul hn : ContMDiff I 𝓘(ℝ) 2 fun y ↦ c * ‖s y‖ ^ 2)
  -- `c ‖s‖²` touches `⟪A s, s⟫` from below at `x`.
  have hlap := TauCeti.Manifold.laplaceBeltrami_le_of_eventuallyLE_of_eq hcn.contMDiffAt
    hf.contMDiffAt hle (by simp [heig, real_inner_smul_left])
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have h0 : ∑ i, ‖(0 : TangentSpace I x →L[ℝ] V x) (b i)‖ ^ 2 = 0 := by simp
  rw [TauCeti.Manifold.laplaceBeltrami_smul I c hn, hcov.laplaceBeltrami_norm_sq hs x b, hs₀, h0,
    hcov.laplaceBeltrami_inner_clm_apply_of_cov_eq_zero hA hs hs₀] at hlap
  set R := cov.roughLaplacian (leviCivitaConnection I M) s x
  -- Since `A x` is symmetric with eigenvector `s x`, both terms in `∇*∇s` are `c ⟪∇*∇s, s⟫`.
  have h1 : ⟪A x R, s x⟫ = c * ⟪R, s x⟫ := by
    have h := hsym R (s x)
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [h, heig, real_inner_smul_right]
  rw [h1, heig, real_inner_smul_left, real_inner_comm R (s x)] at hlap
  linarith

/-- **Hamilton's maximum principle for a field of symmetric endomorphisms of a bundle.** On a
compact boundaryless Riemannian manifold, let `V` be a Riemannian bundle with a metric connection
in which every vector `v ∈ V x` is the value at `x` of a smooth section parallel at `x`, and let
`A` be a smooth field of symmetric endomorphisms of `V`. Suppose that at every point `x` and every
unit vector `v ∈ V x` minimizing `⟪A y w, w⟫` over all unit vectors `w ∈ V y` of the bundle, with
`⟪A x v, v⟫ < -C`, the rough Laplacian satisfies `⟪(∇*∇A) v, v⟫ > 0`. Then `A ≥ -C`:
`-C ‖u‖² ≤ ⟪A x u, u⟫` for every `u ∈ V x`.

The tangent bundle with its Levi-Civita connection has the required parallel extensions
(`TauCeti.Manifold.exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero`), which gives
`TauCeti.Manifold.forall_le_inner_apply_self_of_inner_roughLaplacian_pos`. -/
theorem forall_le_inner_apply_self_of_inner_roughLaplacian_pos [CompactSpace M]
    (hcov : cov.IsMetricCompatible)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (A x)))
    (hsym : ∀ x, (A x : V x →ₗ[ℝ] V x).IsSymmetric)
    (hpar : ∀ x (v : V x), ∃ s : Π y : M, V y, CMDiff ∞ (T% s) ∧ s x = v ∧ cov s x = 0)
    {C : ℝ} (h : ∀ x (v : V x), ‖v‖ = 1 →
      (∀ y (w : V y), ‖w‖ = 1 → ⟪A x v, v⟫ ≤ ⟪A y w, w⟫) → ⟪A x v, v⟫ < -C →
      0 < ⟪(cov.hom cov).roughLaplacian (leviCivitaConnection I M) A x v, v⟫)
    (x : M) : ∀ u : V x, -C * ‖u‖ ^ 2 ≤ ⟪A x u, u⟫ := by
  intro u
  have : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
      (V := V)
  by_contra! hlt
  have hu : u ≠ 0 := by rintro rfl; simp at hlt
  -- The quadratic form attains its minimum `m` on the compact unit sphere bundle.
  set S := {q : TotalSpace F V | ‖q.snd‖ = 1}
  have hS : IsCompact S := TauCeti.isCompact_setOf_norm_eq_bundle continuous_const
  have hf : Continuous fun q : TotalSpace F V ↦ ⟪A q.proj q.snd, q.snd⟫ := by
    have hid : Continuous fun q : TotalSpace F V ↦ TotalSpace.mk' F q.proj q.snd :=
      continuous_id.congr fun q ↦ (TotalSpace.eta q).symm
    have hAc : Continuous fun q : TotalSpace F V ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) q.proj (A q.proj) :=
      hA.continuous.comp (FiberBundle.continuous_proj F V)
    exact (hAc.clm_bundle_apply hid).inner_bundle hid
  have hune : (TotalSpace.mk' F x (‖u‖⁻¹ • u)) ∈ S := by
    simp [S, norm_smul, norm_ne_zero_iff.mpr hu]
  obtain ⟨q₀, hq₀S, hq₀⟩ := hS.exists_isMinOn ⟨_, hune⟩ hf.continuousOn
  set x₀ := q₀.proj
  set v₀ : V x₀ := q₀.snd
  set m := ⟪A x₀ v₀, v₀⟫
  have hv₀ : ‖v₀‖ = 1 := hq₀S
  have hmin : ∀ y (w : V y), m * ‖w‖ ^ 2 ≤ ⟪A y w, w⟫ := fun y w ↦ by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    -- Rescale `w` to the unit vector `‖w‖⁻¹ • w`.
    have h1 : m ≤ ⟪A y (‖w‖⁻¹ • w), ‖w‖⁻¹ • w⟫ :=
      hq₀ (by simp [S, norm_smul, norm_ne_zero_iff.mpr hw] : TotalSpace.mk' F y (‖w‖⁻¹ • w) ∈ S)
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
    calc m * ‖w‖ ^ 2 ≤ ‖w‖⁻¹ * (‖w‖⁻¹ * ⟪A y w, w⟫) * ‖w‖ ^ 2 := by gcongr
      _ = ⟪A y w, w⟫ := by field_simp
  have hmC : m < -C := by nlinarith [hmin x u, (by positivity : 0 < ‖u‖ ^ 2)]
  -- The minimizing unit vector is an eigenvector, and extends to a section parallel at `x₀`.
  have heig : A x₀ v₀ = m • v₀ := by
    have : FiniteDimensional ℝ (V x₀) := VectorBundle.finiteDimensional ℝ F V x₀
    have : CompleteSpace (V x₀) := FiniteDimensional.completeSpace ℝ (V x₀)
    have hext : IsMinOn (A x₀).reApplyInnerSelf (Metric.sphere 0 ‖v₀‖) v₀ := fun w hw ↦ by
      have hw1 : ‖w‖ = 1 := by simpa [hv₀] using hw
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply, hw1, m] using hmin x₀ w
    -- A minimum of the Rayleigh quotient on a sphere is an eigenvector.
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply, hv₀, m] using
      (hsym x₀).isSelfAdjoint.eq_smul_self_of_isLocalExtrOn (Or.inl hext.isLocalMinOn)
  obtain ⟨s, hs, hsx, hs₀⟩ := hpar x₀ v₀
  have hle := hcov.inner_roughLaplacian_hom_apply_nonpos hA hs hs₀ (hsym x₀)
    (c := m) (by rw [hsx]; exact heig) (Filter.Eventually.of_forall fun y ↦ hmin y (s y))
  rw [hsx] at hle
  have hpos := h x₀ v₀ hv₀ (fun y w hw ↦ by simpa [hw] using hmin y w) hmC
  linarith

end CovariantDerivative.IsMetricCompatible

namespace TauCeti.Manifold

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Hamilton's maximum principle for a field of symmetric endomorphisms.** On a compact
boundaryless Riemannian manifold `M`, let `A` be a smooth field of symmetric endomorphisms of the
tangent bundle, and let `∇*∇A` be its rough Laplacian for the connection induced by the
Levi-Civita connection. Suppose that at every point `y` and every unit vector `v ∈ T_y M` which
minimizes `⟪A z w, w⟫` over all unit tangent vectors `w ∈ T_z M` of `M`, with
`⟪A y v, v⟫ < -C`, the rough Laplacian satisfies `⟪(∇*∇A) v, v⟫ > 0`. Then `A ≥ -C`:
`-C ‖v‖² ≤ ⟪A y v, v⟫` for every tangent vector `v`. This is the general bundle version
`CovariantDerivative.IsMetricCompatible.forall_le_inner_apply_self_of_inner_roughLaplacian_pos`
for the tangent bundle.

The minimizing unit vectors are the unit eigenvectors of the least eigenvalue of `A` at the points
where that eigenvalue is smallest, so the hypothesis is only needed there. -/
theorem forall_le_inner_apply_self_of_inner_roughLaplacian_pos
    {A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (hsym : ∀ x, (A x : TangentSpace I x →ₗ[ℝ] TangentSpace I x).IsSymmetric) {C : ℝ}
    (hΔ : ∀ y (v : TangentSpace I y), ‖v‖ = 1 →
      (∀ z (w : TangentSpace I z), ‖w‖ = 1 → ⟪A y v, v⟫ ≤ ⟪A z w, w⟫) → ⟪A y v, v⟫ < -C →
      0 < ⟪((leviCivitaConnection I M).hom (leviCivitaConnection I M)).roughLaplacian
        (leviCivitaConnection I M) A y v, v⟫)
    (y : M) : ∀ v : TangentSpace I y, -C * ‖v‖ ^ 2 ≤ ⟪A y v, v⟫ :=
  (isMetricCompatible_leviCivitaConnection I).forall_le_inner_apply_self_of_inner_roughLaplacian_pos
    hA hsym exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero hΔ y

end TauCeti.Manifold
