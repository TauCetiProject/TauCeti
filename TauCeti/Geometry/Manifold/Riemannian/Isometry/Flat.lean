/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Flat
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Geometry.Manifold.DifferentialForm.CovariantDerivative
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Flat Riemannian metrics and local Euclidean isometries

A smooth Riemannian manifold `(M, g)` is locally isometric to Euclidean space around a point `x₀`
when `x₀` admits an open neighbourhood carrying a local Riemannian isometry (or a smooth Riemannian
isometry onto an open ball centred at the origin) to `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`.

This file proves the fundamental characterization of flat Riemannian metrics: at every interior
point `x₀`, the curvature tensor of the Levi-Civita connection vanishes on a neighbourhood of `x₀`
if and only if `x₀` admits an open neighbourhood isometric to an open ball in Euclidean space (or
carrying a local Riemannian isometry to Euclidean space). Consequently, on an open set `U` of
interior points (and on any open set when `M` is boundaryless), the curvature tensor vanishes at
every point of `U` if and only if every point of `U` admits a local Euclidean isometry.

The flat-implies-isometric direction chains four ingredients:

1. Because `leviCivitaConnection I M` is metric-compatible and has vanishing curvature near `x₀`,
   `IsMetricCompatible.exists_orthonormal_isLocalFrameOn_parallel_of_isInteriorPoint` produces a
   smooth local orthonormal parallel frame `(s i)` on an open neighbourhood `W₁` of `x₀` extending
   an orthonormal basis `b₀` of `TangentSpace I x₀`.
2. Because `leviCivitaConnection I M` is torsion-free, parallel vector fields commute
   (`CovariantDerivative.IsTorsionFree.mlieBracket_eq_zero_of_cov_eq_zero`), and any differentiable
   one-form whose pairings with a local parallel frame have vanishing differentials at a point is
   closed there (`CovariantDerivative.IsTorsionFree.mextDeriv_eq_zero_of_isLocalFrameOn`).
   Applied to the dual coframe one-forms `α i (y) = ⟪s i y, ·⟫`, whose pairings `α i (s j) = δ_{ij}`
   are constant on `W₁`, each `α i` is closed on `W₁`.
3. By the manifold Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`), near `x₀` each `α i` is the
   exterior derivative of a smooth function `f i : M → ℝ`, so `mvfderiv I (f i) y = ⟪s i y, ·⟫`.
4. Given any linear isometric equivalence `L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F`, the smooth map
   `Φ y = ∑ i, (f i y - f i x₀) • L (b₀ i)` sends `x₀` to `0`, has differential `L` at `x₀`, and
   preserves inner products on every tangent space near `x₀`. The manifold inverse function theorem
   (`TauCeti.exists_riemannianIsometry_ball_of_inner_mfderiv_eq`) restricts `Φ` to a smooth
   `RiemannianIsometry` from an open neighbourhood of `x₀` onto an open ball around `0 : F`.

The converse (`TauCeti.curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry`)
needs no interior-point hypothesis: a local Riemannian isometry from an open submanifold `W` into a
real inner-product space `F` pulls back the vanishing Euclidean curvature tensor to `W`, and the
inclusion `W → M` (`TauCeti.IsLocalRiemannianIsometry.subtype_val`) pushes that vanishing to `M`.

## Main results

* `TauCeti.exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint`:
  from vanishing curvature near an interior point `x₀` and `L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F`,
  constructs a `RiemannianIsometry` from an open neighbourhood of `x₀` onto `Metric.ball (0 : F) r`
  sending `x₀` to `0`.
* `TauCeti.curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry`: any local
  Riemannian isometry from an open neighbourhood into `F` forces the curvature tensor to vanish.
* `TauCeti.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff` (and its
  `of_isInteriorPoint` and `ball` forms): germ equivalence at a point.
* `TauCeti.forall_curvatureTensor_leviCivitaConnection_eq_zero_iff` (and its `of_isInteriorPoint`
  and `Bundle.ContMDiffRiemannianMetric` forms): flat curvature on an open set is equivalent to a
  local Euclidean isometry around every point of that set.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 7.10 and Proposition 7.11.
* M. Spivak, *A Comprehensive Introduction to Differential Geometry*, Vol. II, 3rd ed.,
  Publish or Perish (1999), Chapter 6, Theorem 13.
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology TauCeti

namespace TauCeti

/-! ### Converse: local Euclidean isometries force vanishing curvature -/

section Converse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A local Riemannian isometry from an open submanifold to a real inner-product space forces the
curvature tensor to vanish.** No interior-point or boundaryless assumption is needed. -/
theorem curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry
    {W : Opens M} {f : W → F} (hf : IsLocalRiemannianIsometry I 𝓘(ℝ, F) f) {x : M} (hx : x ∈ W) :
    (leviCivitaConnection I M).curvatureTensor x = 0 := by
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
    ⟨(riemannianMetricVectorSpace F).inner, (riemannianMetricVectorSpace F).contMDiff.of_le le_top,
      fun _ _ _ ↦ rfl⟩
  let xW : W := ⟨x, hx⟩
  -- First, `f : W → F` pulls back the vanishing curvature of `F` to `W`.
  have hW0 (u v w : TangentSpace I xW) :
      (leviCivitaConnection I W).curvatureTensor xW u v w = 0 := by
    apply hf.mfderiv_injective xW
    rw [hf.mfderiv_curvatureTensor, Manifold.curvatureTensor_leviCivitaConnection_model_space]
    simp
  -- Second, the open-submanifold inclusion `(Subtype.val : W → M)` pushes that vanishing to `M`.
  have hι := IsLocalRiemannianIsometry.subtype_val (I := I) W
  have hM0 : (leviCivitaConnection I M).curvatureTensor (Subtype.val xW) = 0 := by
    ext u v w
    simp only [LinearMap.zero_apply]
    obtain ⟨u', rfl⟩ := hι.mfderiv_surjective xW u
    obtain ⟨v', rfl⟩ := hι.mfderiv_surjective xW v
    obtain ⟨w', rfl⟩ := hι.mfderiv_surjective xW w
    rw [← hι.mfderiv_curvatureTensor, hW0, map_zero]
  exact hM0

/-- If an open submanifold `W` is Riemannian-isometric to an open subset `B` of a real
inner-product space `F`, then the curvature tensor of `M` vanishes at every point of `W`. -/
theorem curvatureTensor_leviCivitaConnection_eq_zero_of_riemannianIsometry_opens
    {W : Opens M} {B : Opens F} (Ψ : RiemannianIsometry I 𝓘(ℝ, F) W B) {x : M} (hx : x ∈ W) :
    (leviCivitaConnection I M).curvatureTensor x = 0 :=
  curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry
    ((IsLocalRiemannianIsometry.subtype_val B).comp Ψ.isLocalRiemannianIsometry) hx

end Converse

/-! ### Forward direction: flat metrics admit local Euclidean isometries -/

section FlatImpliesIsometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Flat curvature near an interior point produces a local Riemannian isometry onto an open ball
of any isometric model space `F`.** Given `L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F`, there exist an open
neighbourhood `W ⊆ U` of `x₀`, a radius `r > 0`, and a smooth `RiemannianIsometry`
`Ψ : RiemannianIsometry I 𝓘(ℝ, F) W (⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩ : Opens F)`
sending `x₀` to `0` whose differential at `x₀` realizes `L`. -/
theorem exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hflat : ∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0)
    {U : Set M} (hU : U ∈ 𝓝 x₀) (L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F) :
    ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
      (Ψ : RiemannianIsometry I 𝓘(ℝ, F) W (⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩ : Opens F)),
      (W : Set M) ⊆ U ∧ (Ψ ⟨x₀, hx₀W⟩ : F) = 0 ∧
      ∀ v : TangentSpace I (⟨x₀, hx₀W⟩ : W),
        mvfderiv I ((Subtype.val : (⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩ : Opens F) → F) ∘ Ψ)
            ⟨x₀, hx₀W⟩ v =
          L (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x₀, hx₀W⟩ v) := by
  -- Step 1: Build a smooth local orthonormal parallel frame `(s i)` on `W₁ ⊆ U` extending `b₀`.
  let b₀ := stdOrthonormalBasis ℝ (TangentSpace I x₀)
  have hLC := isLeviCivitaConnection_leviCivitaConnection I (M := M)
  have htors : (leviCivitaConnection I M).IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero (leviCivitaConnection I M)).2 hLC.2
  obtain ⟨s, W₁, hs_smooth, hW₁open, hx₀W₁, hW₁U, hframe₁, hs_x₀, hpar₁, horth₁⟩ :=
    hLC.1.exists_orthonormal_isLocalFrameOn_parallel_of_isInteriorPoint hx₀ hflat hU b₀
  -- Step 2: Form the dual coframe 1-forms `α i (y) = ⟪s i y, ·⟫` and prove they are closed on `W₁`.
  let g := Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun y : M ↦ TangentSpace I y)
  have hg_inner (y : M) (u v : TangentSpace I y) : g.inner y u v = inner ℝ u v := by
    simp only [g, Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
    -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
    rfl
  let α : Fin (Module.finrank ℝ (TangentSpace I x₀)) → RoughForm I M ℝ 1 := fun i y ↦
    ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) ℝ (0 : Fin 1) (g.inner y (s i y))
  have hα_smooth (i) : IsSmoothForm I (⊤ : ℕ∞) (α i) :=
    isSmoothForm_ofSubsingleton_iff.2 (g.contMDiff.clm_bundle_apply (hs_smooth i))
  have hα_pair (i j) {y : M} (hy : y ∈ W₁) :
      α i y ![s j y] = if i = j then (1 : ℝ) else 0 := by
    simp only [α, ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero,
      hg_inner]
    exact orthonormal_iff_ite.1 (horth₁ y hy) i j
  have hα_const (i j) {y : M} (hy : y ∈ W₁) :
      mvfderiv I (fun z ↦ α i z ![s j z]) y = 0 := by
    have heq : (fun z ↦ α i z ![s j z]) =ᶠ[𝓝 y] fun _ ↦ if i = j then (1 : ℝ) else 0 :=
      eventually_of_mem (hW₁open.mem_nhds hy) fun z hz ↦ hα_pair i j hz
    exact heq.mvfderiv_eq.trans (mvfderiv_const _)
  have hα_closed (i) : ∀ᶠ y in 𝓝 x₀, mextDeriv (α i) y = 0 :=
    eventually_of_mem (hW₁open.mem_nhds hx₀W₁) fun y hy ↦
      htors.mextDeriv_eq_zero_of_isLocalFrameOn (by simp) (hW₁open.mem_nhds hy) hframe₁
        (fun j ↦ hpar₁ j y hy) (((hα_smooth i).contMDiff.mdifferentiable (by simp)) y)
        (fun j ↦ hα_const i j hy)
  -- Step 3: Integrate each closed 1-form `α i` near `x₀` via the Poincaré lemma.
  have hprim (i) : ∃ V ∈ 𝓝 x₀, ∃ f : M → ℝ, CMDiff ∞ f ∧
      ∀ y ∈ V, ∀ v : TangentSpace I y, mvfderiv I f y v = inner ℝ (s i y) v := by
    obtain ⟨V, hV, ψ, hψ, hdψ⟩ :=
      exists_mextDeriv_eq_nhds (le_top : (1 : ℕ∞) ≤ ⊤) (hα_smooth i) (hα_closed i)
    let f : M → ℝ := fun y ↦ ψ y 0
    have hψeq : ψ = RoughForm.ofFunction I f := RoughForm.eq_ofFunction ψ
    refine ⟨V, hV, f, isSmoothForm_ofFunction_iff.1 (hψeq ▸ hψ), fun y hy v ↦ ?_⟩
    have hd := congrArg (fun η : TangentSpace I y [⋀^Fin 1]→L[ℝ] ℝ ↦ η ![v]) (hdψ y hy)
    rw [hψeq, mextDeriv_ofFunction] at hd
    simpa [α, hg_inner] using hd
  choose V hVnhds f hf_smooth hf_deriv using hprim
  -- Step 4: Assemble `Φ : M → F` on `W₂ ⊆ W₁ ⊆ U` and apply the inverse-function helper.
  let W₂ : Set M := W₁ ∩ ⋂ i, interior (V i)
  have hW₂open : IsOpen W₂ := hW₁open.inter (isOpen_iInter_of_finite fun _ ↦ isOpen_interior)
  have hx₀W₂ : x₀ ∈ W₂ := ⟨hx₀W₁, mem_iInter.2 fun i ↦ mem_interior_iff_mem_nhds.2 (hVnhds i)⟩
  let Φ : M → F := fun y ↦ ∑ i, (f i y - f i x₀) • L (b₀ i)
  have hΦ_smooth : CMDiff ∞ Φ :=
    ContMDiff.sum fun i _ ↦ ((hf_smooth i).sub contMDiff_const).smul contMDiff_const
  have hΦ_mv {y : M} (hy : y ∈ W₂) (v : TangentSpace I y) :
      mvfderiv I Φ y v = ∑ i, inner ℝ (s i y) v • L (b₀ i) := by
    have hfi (i) : MDiffAt (f i) y := (hf_smooth i).mdifferentiable (by simp) y
    have hsub (i) : MDiffAt (fun z ↦ f i z - f i x₀) y := (hfi i).sub mdifferentiableAt_const
    have h := DFunLike.congr_fun
      (mvfderiv_fun_sum (I := I) (u := Finset.univ)
        (f := fun i z ↦ (f i z - f i x₀) • L (b₀ i))
        (fun i _ ↦ (hsub i).smul mdifferentiableAt_const)) v
    rw [sum_apply] at h
    refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    have hmv_sub : mvfderiv I (fun z ↦ f i z - f i x₀) y v = mvfderiv I (f i) y v := by
      simp [-mvfderiv_apply_eq_mfderiv_apply, mvfderiv_fun_sub (hfi i) mdifferentiableAt_const,
        mvfderiv_const]
    simp [-mvfderiv_apply_eq_mfderiv_apply, mvfderiv_fun_smul (hsub i) mdifferentiableAt_const,
      mvfderiv_const, hmv_sub, hf_deriv i y (interior_subset (mem_iInter.1 hy.2 i)) v]
  have hΦ_mv_x₀ (v : TangentSpace I x₀) : mvfderiv I Φ x₀ v = L v := by
    rw [hΦ_mv hx₀W₂ v]
    simp_rw [hs_x₀, ← L.map_smul, ← map_sum, ← b₀.repr_apply_apply]
    rw [b₀.sum_repr]
  have hLb_orth : Orthonormal ℝ (fun i ↦ L (b₀ i)) :=
    orthonormal_iff_ite.2 fun i j ↦
      (L.inner_map_map _ _).trans (orthonormal_iff_ite.1 b₀.orthonormal i j)
  refine exists_riemannianIsometry_ball_of_inner_mfderiv_eq hx₀ hW₂open hx₀W₂
    (inter_subset_left.trans hW₁U) L hΦ_smooth (by simp [Φ]) hΦ_mv_x₀ fun {y} hy v w ↦ ?_
  rw [Manifold.inner_tangentSpace_vectorSpace, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, hΦ_mv hy v, hΦ_mv hy w]
  simpa only [OrthonormalBasis.coe_mk] using
    (OrthonormalBasis.mk (horth₁ y hy.1) (hframe₁.generating hy.1)).inner_sum_inner_smul
      hLb_orth v w

/-- **Existence of an injective local Riemannian isometry into any isometric model space `F` from
vanishing curvature near an interior point.** -/
theorem exists_isLocalRiemannianIsometry_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hflat : ∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0)
    {U : Set M} (hU : U ∈ 𝓝 x₀) (L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F) :
    ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (f : W → F),
      (W : Set M) ⊆ U ∧ Injective f ∧ f ⟨x₀, hx₀W⟩ = 0 ∧
      IsLocalRiemannianIsometry I 𝓘(ℝ, F) f := by
  obtain ⟨W, hx₀W, r, _, Ψ, hWU, hΨ0, _⟩ :=
    exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
      hx₀ hflat hU L
  let B : Opens F := ⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩
  exact ⟨W, hx₀W, (Subtype.val : B → F) ∘ Ψ, hWU, Subtype.val_injective.comp Ψ.injective, hΨ0,
    (IsLocalRiemannianIsometry.subtype_val B).comp Ψ.isLocalRiemannianIsometry⟩

end FlatImpliesIsometric

/-! ### Equivalence characterizations of flat Riemannian metrics -/

section Characterizations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Local Euclidean-isometry characterization of flat curvature at an interior point (open-ball
isometry form).** Near an interior point `x₀`, the curvature tensor vanishes if and only if `x₀`
admits an open neighbourhood Riemannian-isometric to an open ball around `0` in
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`. -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_ball_of_isInteriorPoint
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    (∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))),
        (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  refine ⟨fun hflat ↦ ?_, ?_⟩
  · obtain ⟨W, hx₀W, r, hr, Ψ, -, hΨ0, -⟩ :=
      exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
        hx₀ hflat univ_mem
        ((stdOrthonormalBasis ℝ (TangentSpace I x₀)).reindex
          (finCongr (finrank_tangentSpace x₀))).repr
    exact ⟨W, hx₀W, r, hr, Ψ, hΨ0⟩
  · rintro ⟨W, hx₀W, r, -, Ψ, -⟩
    exact eventually_of_mem (W.isOpen.mem_nhds hx₀W) fun y hy ↦
      curvatureTensor_leviCivitaConnection_eq_zero_of_riemannianIsometry_opens Ψ hy

/-- **Local Euclidean-isometry characterization of flat curvature at an interior point.** Near an
interior point `x₀`, the curvature tensor vanishes if and only if `x₀` admits an open neighbourhood
carrying a local Riemannian isometry into `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`. -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    (∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) ↔
      ∃ (W : Opens M) (_ : x₀ ∈ W) (f : W → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
        IsLocalRiemannianIsometry I
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) f := by
  refine ⟨fun hflat ↦ ?_, ?_⟩
  · obtain ⟨W, hx₀W, r, _, Ψ, -⟩ :=
      (eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_ball_of_isInteriorPoint hx₀).1
        hflat
    exact ⟨W, hx₀W, Subtype.val ∘ Ψ,
      (IsLocalRiemannianIsometry.subtype_val _).comp Ψ.isLocalRiemannianIsometry⟩
  · rintro ⟨W, hx₀W, f, hf⟩
    exact eventually_of_mem (W.isOpen.mem_nhds hx₀W) fun y hy ↦
      curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry hf hy

/-- **Flat curvature on an open set of interior points is equivalent to a local Euclidean isometry
around every point of that set.** -/
theorem forall_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
    {U : Set M} (hU : IsOpen U) (hUint : ∀ x ∈ U, I.IsInteriorPoint x) :
    (∀ x ∈ U, (leviCivitaConnection I M).curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))),
        (W : Set M) ⊆ U ∧
          (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  refine ⟨fun hflat x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨W, hxW, r, hr, Ψ, hWU, hΨ0, -⟩ :=
      exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
        (hUint x hx) (eventually_of_mem (hU.mem_nhds hx) hflat) (hU.mem_nhds hx)
        ((stdOrthonormalBasis ℝ (TangentSpace I x)).reindex
          (finCongr (finrank_tangentSpace x))).repr
    exact ⟨W, hxW, r, hr, Ψ, hWU, hΨ0⟩
  · obtain ⟨W, hxW, _, -, Ψ, -, -⟩ := h x hx
    exact curvatureTensor_leviCivitaConnection_eq_zero_of_riemannianIsometry_opens Ψ hxW

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Local Euclidean-isometry characterization of flat curvature at a point of a boundaryless
manifold (open-ball isometry form).** -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_ball {x₀ : M} :
    (∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))),
        (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 :=
  eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_ball_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

/-- **Local Euclidean-isometry characterization of flat curvature at a point of a boundaryless
manifold.** -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff {x₀ : M} :
    (∀ᶠ y in 𝓝 x₀, (leviCivitaConnection I M).curvatureTensor y = 0) ↔
      ∃ (W : Opens M) (_ : x₀ ∈ W) (f : W → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
        IsLocalRiemannianIsometry I
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) f :=
  eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

/-- **Flat curvature on an open set is equivalent to a local Euclidean isometry around every point
of that set.** -/
theorem forall_curvatureTensor_leviCivitaConnection_eq_zero_iff {U : Set M} (hU : IsOpen U) :
    (∀ x ∈ U, (leviCivitaConnection I M).curvatureTensor x = 0) ↔
      ∀ x ∈ U, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))),
        (W : Set M) ⊆ U ∧
          (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 :=
  forall_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hU
    fun _ _ ↦ BoundarylessManifold.isInteriorPoint

/-- **Global characterization of flat Riemannian manifolds.** A boundaryless Riemannian manifold has
vanishing curvature tensor everywhere if and only if every point admits an open neighbourhood
isometric to an open Euclidean ball. -/
theorem curvatureTensor_leviCivitaConnection_eq_zero_iff :
    (∀ x : M, (leviCivitaConnection I M).curvatureTensor x = 0) ↔
      ∀ x : M, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))),
        (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  simpa using forall_curvatureTensor_leviCivitaConnection_eq_zero_iff (I := I) (M := M) isOpen_univ

end Boundaryless

end Characterizations

end TauCeti

/-! ### Interface for bundled smooth Riemannian metrics -/

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- For a bundled smooth Riemannian metric `g`, vanishing of the curvature tensor near an interior
point `x₀` is equivalent to the existence of a smooth Riemannian isometry from `(W, g|_W)` onto an
open Euclidean ball sending `x₀` to `0`. -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    (∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r),
        letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
          ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  exact
    (TauCeti.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_ball_of_isInteriorPoint
      hx₀).trans
      (exists_congr fun W ↦ exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun _ ↦ by
        rw [g.riemannianBundle_restrictOpenTangentSpace_eq W])

/-- For a bundled smooth Riemannian metric `g`, vanishing of the curvature tensor on an open set
`U` of interior points is equivalent to a local Euclidean isometry around every point of `U`. -/
theorem forall_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {U : Set M}
    (hU : IsOpen U) (hUint : ∀ x ∈ U, I.IsInteriorPoint x) :
    (∀ x ∈ U, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) = 0) ↔
      ∀ x ∈ U, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r),
        letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
          ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (W : Set M) ⊆ U ∧
            (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  exact (TauCeti.forall_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hU
    hUint).trans
    (forall₂_congr fun _ _ ↦ exists_congr fun W ↦ exists_congr fun _ ↦
      exists_congr fun _ ↦ exists_congr fun _ ↦ by
        rw [g.riemannianBundle_restrictOpenTangentSpace_eq W])

section Boundaryless

variable [BoundarylessManifold I M]

/-- For a bundled smooth Riemannian metric `g` on a boundaryless manifold, vanishing of the
curvature tensor near `x₀` is equivalent to the existence of a smooth Riemannian isometry from
`(W, g|_W)` onto an open Euclidean ball sending `x₀` to `0`. -/
theorem eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M} :
    (∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r),
        letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
          ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 :=
  g.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

/-- For a bundled smooth Riemannian metric `g` on a boundaryless manifold, vanishing of the
curvature tensor on an open set `U` is equivalent to a local Euclidean isometry around every point
of `U`. -/
theorem forall_curvatureTensor_leviCivitaConnection_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {U : Set M}
    (hU : IsOpen U) :
    (∀ x ∈ U, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) = 0) ↔
      ∀ x ∈ U, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r),
        letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
          ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (W : Set M) ⊆ U ∧
            (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 :=
  g.forall_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hU
    fun _ _ ↦ BoundarylessManifold.isInteriorPoint

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
