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
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.CovariantDerivative
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
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
   (`TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq`) restricts `Φ` to a smooth `RiemannianIsometry`
   from an open neighbourhood of `x₀` onto an open ball around `0 : F`.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
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
  have : FiniteDimensional ℝ (TangentSpace I x₀) :=
    ((trivializationAt E (TangentSpace I) x₀).linearEquivAt ℝ x₀
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)).symm.finiteDimensional
  have : FiniteDimensional ℝ F := L.toLinearEquiv.finiteDimensional
  have : IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
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
    have hf_smooth : CMDiff ∞ f := isSmoothForm_ofFunction_iff.1 (hψeq ▸ hψ)
    refine ⟨V, hV, f, hf_smooth, fun y hy v ↦ ?_⟩
    have hd := congrArg (fun η : TangentSpace I y [⋀^Fin 1]→L[ℝ] ℝ ↦ η ![v]) (hdψ y hy)
    rw [hψeq, mextDeriv_ofFunction] at hd
    simpa [α, hg_inner] using hd
  choose V hVnhds f hf_smooth hf_deriv using hprim
  -- Step 4: Assemble `Φ : M → F` on an open neighbourhood `W₂ ⊆ W₁ ⊆ U` of `x₀`.
  let W₂ : Set M := W₁ ∩ ⋂ i, interior (V i)
  have hW₂open : IsOpen W₂ :=
    hW₁open.inter (isOpen_iInter_of_finite fun _ ↦ isOpen_interior)
  have hx₀W₂ : x₀ ∈ W₂ :=
    ⟨hx₀W₁, mem_iInter.2 fun i ↦ mem_interior_iff_mem_nhds.2 (hVnhds i)⟩
  have hW₂U : W₂ ⊆ U := inter_subset_left.trans hW₁U
  let Φ : M → F := fun y ↦ ∑ i, (f i y - f i x₀) • L (b₀ i)
  have hΦ_smooth : CMDiff ∞ Φ := by
    refine ContMDiff.sum fun i _ ↦ ?_
    exact ((hf_smooth i).sub contMDiff_const).smul contMDiff_const
  have hΦ_x₀ : Φ x₀ = 0 := by simp [Φ]
  have hΦ_mv {y : M} (hy : y ∈ W₂) (v : TangentSpace I y) :
      mvfderiv I Φ y v = ∑ i, inner ℝ (s i y) v • L (b₀ i) := by
    have hterm_diff (i) : MDiffAt (fun z ↦ (f i z - f i x₀) • L (b₀ i)) y :=
      ((((hf_smooth i).mdifferentiable (by simp) y).sub mdifferentiableAt_const).smul
        mdifferentiableAt_const)
    have h := DFunLike.congr_fun
      (mvfderiv_fun_sum (I := I) (t := Finset.univ)
        (g := fun i z ↦ (f i z - f i x₀) • L (b₀ i)) (fun i _ ↦ hterm_diff i)) v
    rw [sum_apply] at h
    refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    have hfi : MDiffAt (f i) y := (hf_smooth i).mdifferentiable (by simp) y
    have hsub : MDiffAt (fun z ↦ f i z - f i x₀) y := hfi.sub mdifferentiableAt_const
    rw [mvfderiv_fun_smul hsub mdifferentiableAt_const, mvfderiv_const, smul_zero, zero_add,
      ContinuousLinearMap.smulRight_apply, mvfderiv_fun_sub hfi mdifferentiableAt_const,
      mvfderiv_const, sub_apply, zero_apply, sub_zero,
      hf_deriv i y (interior_subset (mem_iInter.1 hy.2 i)) v]
  -- Differential at `x₀` equals `L` (up to `fromTangentSpace 0`).
  have hΦ_mv_x₀ (v : TangentSpace I x₀) : mvfderiv I Φ x₀ v = L v := by
    rw [hΦ_mv hx₀W₂ v]
    simp_rw [hs_x₀, ← L.map_smul, ← map_sum]
    congr 1
    simp_rw [← b₀.repr_apply_apply]
    exact b₀.sum_repr v
  -- Differential on `W₂` preserves inner products everywhere.
  have hLb_orth : Orthonormal ℝ (fun i ↦ L (b₀ i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [L.inner_map_map]
    exact orthonormal_iff_ite.1 b₀.orthonormal i j
  have hΦ_inner {y : M} (hy : y ∈ W₂) (v w : TangentSpace I y) :
      inner ℝ (mfderiv I 𝓘(ℝ, F) Φ y v) (mfderiv I 𝓘(ℝ, F) Φ y w) = inner ℝ v w := by
    have : FiniteDimensional ℝ (TangentSpace I y) :=
      ((trivializationAt E (TangentSpace I) y).linearEquivAt ℝ y
        (mem_baseSet_trivializationAt E (TangentSpace I) y)).symm.finiteDimensional
    let b_y : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x₀))) ℝ (TangentSpace I y) :=
      (hframe₁.toBasisAt hy.1).toOrthonormalBasis
        (by
          have hcoe : ⇑(hframe₁.toBasisAt hy.1) = fun i ↦ s i y :=
            funext (hframe₁.toBasisAt_coe hy.1)
          rw [hcoe]
          exact horth₁ y hy.1)
    have hb_y (i) : b_y i = s i y := by
      rw [b_y.coe_toBasis.symm, Module.Basis.toBasis_toOrthonormalBasis,
        hframe₁.toBasisAt_coe hy.1]
    rw [Manifold.inner_tangentSpace_vectorSpace, NormedSpace.fromTangentSpace_apply,
      NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
      ← mvfderiv_apply_eq_mfderiv_apply, hΦ_mv hy v, hΦ_mv hy w,
      hLb_orth.inner_sum _ _ Finset.univ]
    simp only [RCLike.conj_to_real]
    calc ∑ i, inner ℝ (s i y) v * inner ℝ (s i y) w
      _ = ∑ i, inner ℝ v (b_y i) * inner ℝ (b_y i) w := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hb_y i, real_inner_comm (s i y) v]
      _ = inner ℝ v w := b_y.sum_inner_mul_inner v w
  -- Step 5: Apply the manifold inverse function theorem at `x₀` and shrink to an open ball in `F`.
  let e₀ : TangentSpace I x₀ ≃L[ℝ] TangentSpace 𝓘(ℝ, F) (Φ x₀) :=
    L.toLinearEquiv.toContinuousLinearEquiv.trans (NormedSpace.fromTangentSpace (Φ x₀)).symm
  have he₀ : (e₀ : TangentSpace I x₀ →L[ℝ] TangentSpace 𝓘(ℝ, F) (Φ x₀)) =
      mfderiv I 𝓘(ℝ, F) Φ x₀ := by
    ext v
    apply (NormedSpace.fromTangentSpace (Φ x₀)).injective
    simpa [e₀, mvfderiv] using (hΦ_mv_x₀ v).symm
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ Φ x₀ :=
    isLocalDiffeomorphAt_of_mfderiv_eq hΦ_smooth.contMDiffOn isOpen_univ (mem_univ x₀) hx₀
      (by simp) he₀
  let ψ := hloc.localInverse
  let S : Set F := ψ.source ∩ ψ ⁻¹' W₂
  have hS_open : IsOpen S :=
    hloc.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage ψ.open_source hW₂open
  have h0S : (0 : F) ∈ S := by
    refine ⟨hΦ_x₀ ▸ hloc.localInverse_mem_source, ?_⟩
    simpa only [mem_preimage, ψ, ← hΦ_x₀,
      hloc.localInverse_left_inv hloc.localInverse_mem_target] using hx₀W₂
  obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.1 hS_open 0 h0S
  let W_set : Set M := (ψ.target ∩ W₂) ∩ Φ ⁻¹' Metric.ball (0 : F) r
  have hW_open : IsOpen W_set :=
    (ψ.open_target.inter hW₂open).inter (Metric.isOpen_ball.preimage hΦ_smooth.continuous)
  have hx₀W : x₀ ∈ W_set :=
    ⟨⟨hloc.localInverse_mem_target, hx₀W₂⟩, by simp [hΦ_x₀, hr]⟩
  let W : Opens M := ⟨W_set, hW_open⟩
  let B : Opens F := ⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩
  have hψ_maps {z : F} (hz : z ∈ Metric.ball (0 : F) r) : ψ z ∈ W_set := by
    obtain ⟨hz_src, hψW₂⟩ := hr_sub hz
    refine ⟨⟨ψ.map_source hz_src, hψW₂⟩, ?_⟩
    simpa only [mem_preimage, ψ, hloc.localInverse_right_inv hz_src] using hz
  let d : Diffeomorph I 𝓘(ℝ, F) W B ∞ :=
    { toFun := fun y ↦ ⟨Φ y.1, y.2.2⟩
      invFun := fun z ↦ ⟨ψ z.1, hψ_maps z.2⟩
      left_inv := fun y ↦ Subtype.ext (hloc.localInverse_left_inv y.2.1.1)
      right_inv := fun z ↦ Subtype.ext (hloc.localInverse_right_inv (hr_sub z.2).1)
      contMDiff_toFun :=
        (ContMDiff.subtypeVal_comp_iff B _).mp (hΦ_smooth.comp contMDiff_subtype_val)
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff W _).mp <|
        contMDiffOn_univ.1 <|
          hloc.contMDiffOn_localInverse.comp contMDiff_subtype_val.contMDiffOn
            fun z _ ↦ (hr_sub z.2).1 }
  have hcomp_coe : ((Subtype.val : B → F) ∘ d) = (Φ ∘ (Subtype.val : W → M)) := rfl
  let Ψ : RiemannianIsometry I 𝓘(ℝ, F) W B :=
    { toDiffeomorph := d
      inner_mfderiv' := fun y v w ↦ by
        have hιB := IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) B
        have hιW := IsLocalRiemannianIsometry.subtype_val (I := I) W
        have hd_diff : MDiffAt d y := d.contMDiff.mdifferentiableAt (by simp)
        have hB_diff : MDiffAt (Subtype.val : B → F) (d y) := hιB.mdifferentiableAt (d y)
        have hW_diff : MDiffAt (Subtype.val : W → M) y := hιW.mdifferentiableAt y
        have hΦ_diff : MDiffAt Φ y.1 := hΦ_smooth.mdifferentiableAt (by simp)
        rw [← hιB.inner_mfderiv (d y), ← mfderiv_comp_apply y hB_diff hd_diff,
          ← mfderiv_comp_apply y hB_diff hd_diff, hcomp_coe,
          mfderiv_comp_apply y hΦ_diff hW_diff, mfderiv_comp_apply y hΦ_diff hW_diff,
          hΦ_inner y.2.1.2, hιW.inner_mfderiv y] }
  refine ⟨W, hx₀W, r, hr, Ψ, fun y hy ↦ hW₂U hy.1.2, hΦ_x₀, fun v ↦ ?_⟩
  have hW_diff : MDiffAt (Subtype.val : W → M) ⟨x₀, hx₀W⟩ :=
    (IsLocalRiemannianIsometry.subtype_val (I := I) W).mdifferentiableAt ⟨x₀, hx₀W⟩
  have hΦ_diff : MDiffAt Φ x₀ := hΦ_smooth.mdifferentiableAt (by simp)
  have hmv := mvfderiv_comp_apply (⟨x₀, hx₀W⟩ : W) hΦ_diff hW_diff v
  rw [Manifold.mfderiv_subtype_val, hΦ_mv_x₀] at hmv
  exact hmv

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

private def tangentSpaceEuclideanEquiv (x₀ : M) :
    TangentSpace I x₀ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  let eT := (trivializationAt E (TangentSpace I) x₀).linearEquivAt ℝ x₀
    (mem_baseSet_trivializationAt E (TangentSpace I) x₀)
  have : FiniteDimensional ℝ (TangentSpace I x₀) := eT.symm.finiteDimensional
  ((stdOrthonormalBasis ℝ (TangentSpace I x₀)).reindex (finCongr eT.finrank_eq)).repr

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
        hx₀ hflat univ_mem (tangentSpaceEuclideanEquiv x₀)
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
  · obtain ⟨W, hx₀W, f, -, -, -, hf⟩ :=
      exists_isLocalRiemannianIsometry_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
        hx₀ hflat univ_mem (tangentSpaceEuclideanEquiv x₀)
    exact ⟨W, hx₀W, f, hf⟩
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
        (tangentSpaceEuclideanEquiv x)
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
  refine
    (TauCeti.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_ball_of_isInteriorPoint
      hx₀).trans ?_
  refine exists_congr fun W ↦ exists_congr fun hx₀W ↦ exists_congr fun r ↦ exists_congr fun _ ↦ ?_
  exact iff_of_eq (congrArg
    (fun b : RiemannianBundle (fun x : W ↦ TangentSpace I x) ↦
      letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) := b
      ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
        (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0)
    (g.riemannianBundle_restrictOpenTangentSpace_eq W))

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
  refine (TauCeti.forall_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hU
    hUint).trans ?_
  refine forall₂_congr fun x _ ↦ exists_congr fun W ↦ exists_congr fun hxW ↦
    exists_congr fun r ↦ exists_congr fun _ ↦ ?_
  exact iff_of_eq (congrArg
    (fun b : RiemannianBundle (fun x : W ↦ TangentSpace I x) ↦
      letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) := b
      ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
        (W : Set M) ⊆ U ∧ (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0)
    (g.riemannianBundle_restrictOpenTangentSpace_eq W))

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
