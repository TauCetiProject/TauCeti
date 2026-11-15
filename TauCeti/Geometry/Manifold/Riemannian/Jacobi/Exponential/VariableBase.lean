/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Propagator
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InitialData
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ConstantGeodesic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Jacobi fields and the variable-basepoint differential of the exponential map

In `TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic`, differentiating the fixed-base
exponential map `exp_p` along radial rays produces the Jacobi fields vanishing at `t = 0`:
`d(exp_p)_{t v} (t w)` has initial data `(0, w)`. To obtain a Jacobi field with arbitrary initial
data `(u, w)` — including `u ≠ 0` and constant geodesics `v = 0` — one differentiates the bundle
exponential map `(x, v) ↦ exp_x v` on `TM` along a path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩` whose base
point and initial velocity both vary.

Because `exp_x (t • v) = maximalGeodesic x v t` holds globally on `TM × ℝ` (on and off the maximal
geodesic interval), the geodesic Jacobi propagator at time `t` factors on the natural geodesic
interval as fibrewise scalar multiplication `(x, v) ↦ (x, t • v)` followed by the differential of
`(x, v) ↦ exp_x v`. Consequently:

* For any curve `σ : ℝ → TM` differentiable at `0`, differentiating `(x, v) ↦ exp_x v` along the
  ray-rescaled path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩` produces a Jacobi field along
  `t ↦ exp_{(σ 0).proj} (t • (σ 0).2)` on its entire maximal geodesic interval, with initial value
  `∂_q (σ q).proj (0)` and initial covariant derivative `D_q (σ q).2 (0)` (at `t = 0`, the initial
  value identity holds unconditionally without assuming `σ` differentiable).
* Conversely, every Jacobi field `X` along `t ↦ exp_p (t • v)` on a preconnected parameter set
  containing `0` arises this way from a smooth curve `σ` through `(p, v)`, with no completeness,
  nonzero-velocity, or vanishing-initial-value assumption.
* Along a constant geodesic (`v = 0`), for any curve `σ` differentiable at `0` through `0_p`, the
  resulting Jacobi field reduces to the affine formula `J(t) = J(0) + t • D_t J(0)` for all
  `t : ℝ` (see `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_zeroSection_apply` in
  `TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase` for the pointwise
  differential on `T_{0_p}(TM)`).

## Main results

* `TangentBundle.geodesicJacobiPropagator_eq_mfderiv_riemannianExp_tangentBundle`: factorization of
  `geodesicJacobiPropagator` through fibre rescaling and `mfderiv` of `(x, v) ↦ exp_x v`.
* `TauCeti.Manifold.variationField_riemannianExp_smul`: the variation field of
  `(q, t) ↦ exp_{(σ q).proj} (t • (σ q).2)` equals `mfderiv` of `(x, v) ↦ exp_x v` along the
  ray-rescaled path in `TM`.
* `TauCeti.Manifold.isJacobiFieldOn_mfderiv_riemannianExp_tangentBundle`,
  `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_curveVelocity_zero`, and
  `TauCeti.Manifold.alongCurveWithin_mfderiv_riemannianExp_tangentBundle_zero`: the variable-base
  differential of `exp` along a ray-rescaled curve in `TM` is a Jacobi field with initial data
  `(∂_q (σ q).proj (0), D_q (σ q).2 (0))`.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_mfderiv_riemannianExp_tangentBundle` and
  `TauCeti.Manifold.IsJacobiFieldOn.exists_contMDiffAt_eq_mfderiv_riemannianExp_tangentBundle`:
  every Jacobi field along `t ↦ exp_p (t • v)` on a preconnected parameter set containing `0` is
  given by differentiating `(x, v) ↦ exp_x v` along a smooth curve in `TM`.
* `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_zeroSection_curveVelocity`: the constant
  geodesic (`v = 0`) specialization, yielding the affine field `J(0) + t • D_t J(0)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10,
  Theorem 10.4 and Proposition 10.10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 3, §3 and Chapter 5, §2.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The bundle exponential map `(x, v) ↦ exp_x v` is differentiable at `(x, t • v)` whenever `t`
lies in the maximal geodesic interval of `(x, v)`. -/
private theorem mdifferentiableAt_riemannianExp_tangentBundle_smul
    {z : TangentBundle I M} {t : ℝ} (ht : t ∈ geodesicInterval I M z.proj z.2) :
    MDifferentiableAt I.tangent I
      (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
      (TotalSpace.mk' E z.proj (t • z.2)) := by
  have hz : TotalSpace.mk' E z.proj (t • z.2) ∈
      {w : TangentBundle I M | w.2 ∈ expDomain I M w.proj} :=
    mem_geodesicInterval_iff_smul_mem_expDomain.mp ht
  exact ((contMDiffOn_riemannianExp_tangentBundle _ hz).contMDiffAt
    (isOpen_setOfPred_mem_expDomain.mem_nhds hz)).mdifferentiableAt (by simp)

/-- **Factorization of the Jacobi propagator through the bundle exponential map.** On the natural
geodesic interval, `TangentBundle.geodesicJacobiPropagator` factors as the differential of fibrewise
rescaling `(x, v) ↦ (x, t • v)` followed by the differential of `(x, v) ↦ exp_x v`. -/
theorem _root_.TangentBundle.geodesicJacobiPropagator_eq_mfderiv_riemannianExp_tangentBundle
    (z : TangentBundle I M) {t : ℝ} (ht : t ∈ geodesicInterval I M z.proj z.2)
    (ξ : TangentSpace I.tangent z) :
    TangentBundle.geodesicJacobiPropagator z t ξ =
      mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E z.proj (t • z.2))
        (mfderiv I.tangent I.tangent
          (fun w : TangentBundle I M ↦ TotalSpace.mk' E w.proj (t • w.2)) z ξ) := by
  rw [TangentBundle.geodesicJacobiPropagator_def]
  let f : TangentBundle I M → TangentBundle I M :=
    fun w ↦ TotalSpace.mk' E w.proj (t • w.2)
  let g : TangentBundle I M → M := fun w ↦ riemannianExp I M w.proj w.2
  have hf : MDifferentiableAt I.tangent I.tangent f z :=
    ((TauCeti.contMDiff_totalSpaceMk_smul (I := I) (V := TangentSpace I) (n := ∞) t)
      z).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt I.tangent I g (f z) :=
    mdifferentiableAt_riemannianExp_tangentBundle_smul ht
  have hcomp := mfderiv_comp_apply z hg hf ξ
  have hfun : (fun w : TangentBundle I M ↦ maximalGeodesic I M w.proj w.2 t) = g ∘ f :=
    funext fun w ↦ (riemannianExp_smul w.proj w.2 t).symm
  have htan := congrArg (fun k : TangentBundle I M → M ↦
    tangentMap I.tangent I k (TotalSpace.mk' (E × E) z ξ)) hfun
  exact (eq_of_heq (TotalSpace.ext_iff.mp htan).2).trans hcomp

/-- Differentiating `(x, v) ↦ exp_x v` along the ray-rescaled curve `q ↦ ⟨(σ q).proj, t • (σ q).2⟩`
gives `TangentBundle.geodesicJacobiPropagator` applied to the velocity of `σ`. -/
theorem mfderiv_riemannianExp_tangentBundle_curveVelocity_eq_geodesicJacobiPropagator
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    {t : ℝ} (ht : t ∈ geodesicInterval I M (σ 0).proj (σ 0).2) :
    mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) =
      TangentBundle.geodesicJacobiPropagator (σ 0) t (curveVelocity I.tangent σ 0) := by
  let f : TangentBundle I M → TangentBundle I M :=
    fun w ↦ TotalSpace.mk' E w.proj (t • w.2)
  have hf : MDifferentiableAt I.tangent I.tangent f (σ 0) :=
    ((TauCeti.contMDiff_totalSpaceMk_smul (I := I) (V := TangentSpace I) (n := ∞) t)
      (σ 0)).mdifferentiableAt (by simp)
  have hvel : curveVelocity I.tangent (f ∘ σ) 0 =
      mfderiv I.tangent I.tangent f (σ 0) (curveVelocity I.tangent σ 0) := by
    rw [curveVelocity_apply, curveVelocity_apply]
    exact mfderiv_comp_apply 0 hf hσ (1 : ℝ)
  rw [TangentBundle.geodesicJacobiPropagator_eq_mfderiv_riemannianExp_tangentBundle (σ 0) ht,
    ← hvel]
  rfl

/-- **Variation field of a variable-base exponential family.** Along a curve `σ : ℝ → TM`
differentiable at `0`, the variation field of `(q, t) ↦ exp_{(σ q).proj} (t • (σ q).2)` at a time
`t` in the maximal geodesic interval equals the differential of `(x, v) ↦ exp_x v` applied to the
velocity of the ray-rescaled path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩`. -/
theorem variationField_riemannianExp_smul
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    {t : ℝ} (ht : t ∈ geodesicInterval I M (σ 0).proj (σ 0).2) :
    variationField I (fun q r ↦ riemannianExp I M (σ q).proj (r • (σ q).2)) t =
      mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) := by
  let σ_t : ℝ → TangentBundle I M := fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)
  have hσ_t : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ_t 0 :=
    (((TauCeti.contMDiff_totalSpaceMk_smul (I := I) (V := TangentSpace I) (n := ∞) t)
      (σ 0)).mdifferentiableAt (by simp)).comp 0 hσ
  have hexp : MDifferentiableAt I.tangent I
      (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2) (σ_t 0) :=
    mdifferentiableAt_riemannianExp_tangentBundle_smul ht
  rw [variationField_apply, curveVelocity_apply, curveVelocity_apply]
  exact mfderiv_comp_apply 0 hexp hσ_t (1 : ℝ)

/-- **The variable-base differential of `exp` along a ray-rescaled curve is a Jacobi field.**
For any curve `σ : ℝ → TM` differentiable at `0`, differentiating `(x, v) ↦ exp_x v` along
`q ↦ ⟨(σ q).proj, t • (σ q).2⟩` defines a Jacobi field along
`t ↦ exp_{(σ 0).proj} (t • (σ 0).2)` on its entire maximal geodesic interval. -/
theorem isJacobiFieldOn_mfderiv_riemannianExp_tangentBundle
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0) :
    IsJacobiFieldOn I (fun t : ℝ ↦ riemannianExp I M (σ 0).proj (t • (σ 0).2))
      (fun t ↦ mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0))
      (geodesicInterval I M (σ 0).proj (σ 0).2) := by
  refine (TangentBundle.isJacobiFieldOn_geodesicJacobiPropagator (σ 0)
    (curveVelocity I.tangent σ 0)).congr_totalSpace fun t ht ↦ TotalSpace.ext
      (riemannianExp_smul (σ 0).proj (σ 0).2 t)
      (heq_of_eq (mfderiv_riemannianExp_tangentBundle_curveVelocity_eq_geodesicJacobiPropagator
        hσ ht))

/-- At `t = 0`, the variable-base differential of `exp` along a ray-rescaled curve evaluates to the
base-point velocity of `σ`, without any differentiability assumption on `σ`. -/
@[simp]
theorem mfderiv_riemannianExp_tangentBundle_curveVelocity_zero
    (σ : ℝ → TangentBundle I M) :
    mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E (σ 0).proj ((0 : ℝ) • (σ 0).2))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj ((0 : ℝ) • (σ q).2)) 0) =
      curveVelocity I (fun q ↦ (σ q).proj) 0 := by
  let c : ℝ → M := fun q ↦ (σ q).proj
  let σ₀ : ℝ → TangentBundle I M := fun q ↦ TotalSpace.mk' E (σ q).proj ((0 : ℝ) • (σ q).2)
  let expTM : TangentBundle I M → M := fun w ↦ riemannianExp I M w.proj w.2
  have hζ : σ₀ = zeroSection E (TangentSpace I) ∘ c := by
    funext q
    simp [σ₀, c, zeroSection]
  by_cases hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0
  · have hσ₀ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ₀ 0 :=
      hζ ▸ (((contMDiff_zeroSection ℝ (TangentSpace I) :
        ContMDiff I I.tangent ∞ _).contMDiffAt).mdifferentiableAt (by simp)).comp 0 hc
    have hexp : MDifferentiableAt I.tangent I expTM (σ₀ 0) :=
      mdifferentiableAt_riemannianExp_tangentBundle_smul zero_mem_geodesicInterval
    have h1 : mfderiv I.tangent I expTM (σ₀ 0) (curveVelocity I.tangent σ₀ 0) =
        curveVelocity I (expTM ∘ σ₀) 0 := by
      rw [curveVelocity_apply, curveVelocity_apply]
      exact (mfderiv_comp_apply 0 hexp hσ₀ (1 : ℝ)).symm
    have h0 : expTM ∘ σ₀ = c := by
      funext q
      simp [expTM, σ₀, c, zero_smul]
    have hlift := congrArg (fun γ : ℝ → M ↦ curveVelocityLift I γ 0) h0
    rw [curveVelocityLift_apply, curveVelocityLift_apply] at hlift
    exact eq_of_heq ((heq_of_eq h1).trans (TotalSpace.ext_iff.mp hlift).2)
  · have hσ₀ : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ₀ 0 := fun h ↦ by
      have hc_eq : c = TotalSpace.proj ∘ σ₀ := rfl
      exact hc (hc_eq ▸ (((Bundle.contMDiff_proj (TangentSpace I) :
        ContMDiff I.tangent I ∞ _).contMDiffAt).mdifferentiableAt (by simp)).comp 0 h)
    have hv₀ : curveVelocity I.tangent σ₀ 0 = 0 := by
      rw [curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hσ₀]
      rfl
    have hvc : curveVelocity I c 0 = 0 := by
      rw [curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hc]
      rfl
    -- Both velocities vanish; `TangentSpace I (expTM (σ₀ 0))` and `TangentSpace I (c 0)` both
    -- reduce to the model space `E` with the same `Zero` instance.
    change mfderiv I.tangent I expTM (σ₀ 0) (curveVelocity I.tangent σ₀ 0) = curveVelocity I c 0
    rw [hv₀]
    exact (map_zero _).trans hvc.symm

/-- **Initial covariant derivative of the variable-base differential of `exp`.** For a curve
`σ : ℝ → TM` differentiable at `0`, the covariant derivative at `t = 0` of the Jacobi field
obtained by differentiating `(x, v) ↦ exp_x v` along `q ↦ ⟨(σ q).proj, t • (σ q).2⟩` is the
covariant derivative of `(σ q).2` along `(σ q).proj` at `0`. -/
@[simp]
theorem alongCurveWithin_mfderiv_riemannianExp_tangentBundle_zero
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0) :
    alongCurveWithin (leviCivitaConnection I M)
        (fun t : ℝ ↦ riemannianExp I M (σ 0).proj (t • (σ 0).2))
        (fun t ↦ mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
          (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
          (curveVelocity I.tangent
            (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0))
        (geodesicInterval I M (σ 0).proj (σ 0).2) 0 =
      alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 := by
  let cov := leviCivitaConnection I M
  have hcurve : (fun t : ℝ ↦ riemannianExp I M (σ 0).proj (t • (σ 0).2)) =
      maximalGeodesic I M (σ 0).proj (σ 0).2 :=
    funext fun t ↦ riemannianExp_smul (σ 0).proj (σ 0).2 t
  have hheq : ∀ t ∈ geodesicInterval I M (σ 0).proj (σ 0).2,
      HEq (mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
            (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
            (curveVelocity I.tangent
              (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0))
        (TangentBundle.geodesicJacobiPropagator (σ 0) t (curveVelocity I.tangent σ 0)) :=
    fun t ht ↦ heq_of_eq
      (mfderiv_riemannianExp_tangentBundle_curveVelocity_eq_geodesicJacobiPropagator hσ ht)
  have hD : HEq
      (alongCurveWithin cov (fun t : ℝ ↦ riemannianExp I M (σ 0).proj (t • (σ 0).2))
        (fun t ↦ mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
          (TotalSpace.mk' E (σ 0).proj (t • (σ 0).2))
          (curveVelocity I.tangent
            (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0))
        (geodesicInterval I M (σ 0).proj (σ 0).2) 0)
      (alongCurveWithin cov (maximalGeodesic I M (σ 0).proj (σ 0).2)
        (fun t ↦ TangentBundle.geodesicJacobiPropagator (σ 0) t (curveVelocity I.tangent σ 0))
        (geodesicInterval I M (σ 0).proj (σ 0).2) 0) :=
    alongCurveWithin_congr_heq cov _ (EventuallyEq.of_eq hcurve) (congrFun hcurve 0)
      (mem_of_superset self_mem_nhdsWithin hheq) (hheq 0 zero_mem_geodesicInterval)
  exact (eq_of_heq hD).trans (TangentBundle.alongCurveWithin_geodesicJacobiPropagator_zero hσ)

/-- **Every Jacobi field along `t ↦ exp_p (t • v)` agrees with the variable-base differential of
`exp` along any matching initial-data curve in `TM`.** Unlike
`IsJacobiFieldOn.eq_mfderiv_riemannianExp`, the initial value `X 0` need not vanish (including along
a constant geodesic `v = 0`). -/
theorem IsJacobiFieldOn.eq_mfderiv_riemannianExp_tangentBundle
    {p : M} {v : TangentSpace I p}
    {X : ∀ t : ℝ, TangentSpace I (riemannianExp I M p (t • v))} {s : Set ℝ}
    (hX : IsJacobiFieldOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) X s)
    (hs : IsPreconnected s) (h0 : (0 : ℝ) ∈ s)
    {σ : ℝ → TangentBundle I M} (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    (hσ0 : σ 0 = TotalSpace.mk' E p v)
    (hX0 : curveVelocity I (fun q ↦ (σ q).proj) 0 = X 0)
    (hDX0 : alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 =
      alongCurveWithin (leviCivitaConnection I M) (fun t : ℝ ↦ riemannianExp I M p (t • v))
        X s 0)
    {t : ℝ} (ht : t ∈ s) :
    X t = mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
      (TotalSpace.mk' E p (t • v))
      (curveVelocity I.tangent
        (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) := by
  have hmax : (fun r : ℝ ↦ riemannianExp I M p (r • v)) = maximalGeodesic I M p v :=
    funext fun r ↦ riemannianExp_smul p v r
  have hsub : s ⊆ geodesicInterval I M p v :=
    (hmax ▸ hX.isGeodesicCurveOn).subset_geodesicInterval_of_maximalGeodesic hs h0
  obtain ⟨hp, hv⟩ := TotalSpace.ext_iff.mp hσ0.symm
  subst hp
  obtain rfl := eq_of_heq hv
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp_tangentBundle hσ
  -- At `t = 0`, `TangentSpace I (exp_{(σ 0).proj} (0 • (σ 0).2))` and `TangentSpace I (σ 0).proj`
  -- both reduce to the model space `E`, so `Eq.trans` chains the initial-data identities directly.
  have hJ0 := (mfderiv_riemannianExp_tangentBundle_curveVelocity_zero σ).trans hX0
  have hDJ0 := (alongCurveWithin_mfderiv_riemannianExp_tangentBundle_zero hσ).trans hDX0
  refine hX.eq_of_eq_of_alongCurveWithin_eq (hJ.mono hX.uniqueDiffOn hsub) hs h0 hJ0.symm ?_ ht
  rw [hJ.alongCurveWithin_subset (hX.uniqueDiffOn 0 h0) hsub h0, hDJ0]

/-- **Every Jacobi field along `t ↦ exp_p (t • v)` arises from differentiating `(x, v) ↦ exp_x v`
along a smooth curve in `TM`.** No completeness, nonzero-velocity, or vanishing-initial-value
hypothesis is imposed. -/
theorem IsJacobiFieldOn.exists_contMDiffAt_eq_mfderiv_riemannianExp_tangentBundle
    {p : M} {v : TangentSpace I p}
    {X : ∀ t : ℝ, TangentSpace I (riemannianExp I M p (t • v))} {s : Set ℝ}
    (hX : IsJacobiFieldOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) X s)
    (hs : IsPreconnected s) (h0 : (0 : ℝ) ∈ s) :
    ∃ σ : ℝ → TangentBundle I M,
      σ 0 = TotalSpace.mk' E p v ∧
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ σ 0 ∧
      curveVelocity I (fun q ↦ (σ q).proj) 0 = X 0 ∧
      alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 =
        alongCurveWithin (leviCivitaConnection I M) (fun t : ℝ ↦ riemannianExp I M p (t • v))
          X s 0 ∧
      ∀ t ∈ s, X t = mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (TotalSpace.mk' E p (t • v))
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) := by
  obtain ⟨σ, hσ0, hσ, hpos, hvel⟩ :=
    TangentSpace.exists_smooth_initialData (v := v) (X 0)
      (alongCurveWithin (leviCivitaConnection I M)
        (fun t : ℝ ↦ riemannianExp I M p (t • v)) X s 0)
  have hσ_at := hσ.self_of_nhds
  exact ⟨σ, hσ0, hσ_at, hpos, hvel, fun _ ht ↦
    hX.eq_mfderiv_riemannianExp_tangentBundle hs h0 (hσ_at.mdifferentiableAt (by simp))
      hσ0 hpos hvel ht⟩

/-! ### Specialization to constant geodesics (`v = 0`) -/

/-- **Variable-base exponential formula along a constant geodesic (`v = 0`).** For any curve
`σ : ℝ → TM` differentiable at `0` through `0_p`, differentiating `(x, v) ↦ exp_x v` along the
ray-rescaled path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩` produces the affine Jacobi field
`t ↦ ∂_q (σ q).proj (0) + t • D_q (σ q).2 (0)` for all `t : ℝ`. -/
theorem mfderiv_riemannianExp_tangentBundle_zeroSection_curveVelocity
    {p : M} {σ : ℝ → TangentBundle I M}
    (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent σ 0)
    (hσ0 : σ 0 = TotalSpace.mk' E p 0) (t : ℝ) :
    mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (zeroSection E (TangentSpace I) p)
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0) =
      curveVelocity I (fun q ↦ (σ q).proj) 0 +
         t • alongCurve (leviCivitaConnection I M) (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0 := by
  obtain ⟨hp, _⟩ := TotalSpace.ext_iff.mp hσ0.symm
  subst hp
  let cov := leviCivitaConnection I M
  let u : TangentSpace I (σ 0).proj := curveVelocity I (fun q ↦ (σ q).proj) 0
  let w : TangentSpace I (σ 0).proj := alongCurve cov (fun q ↦ (σ q).proj) (fun q ↦ (σ q).2) 0
  -- Every `TangentSpace I _` reduces to the model space `E`, so `u + (r - 0) • w` can be typed
  -- directly as a section along `r ↦ exp_{(σ 0).proj} (r • 0)`.
  let X : ∀ r : ℝ,
      TangentSpace I (riemannianExp I M (σ 0).proj (r • (0 : TangentSpace I (σ 0).proj))) :=
    fun r ↦ u + (r - 0) • w
  have hconst :
      (fun r : ℝ ↦ riemannianExp I M (σ 0).proj (r • (0 : TangentSpace I (σ 0).proj))) =
        fun _ ↦ (σ 0).proj := by
    funext r
    rw [smul_zero, riemannianExp_zero]
  have hX_const : IsJacobiFieldOn I (fun _ : ℝ ↦ (σ 0).proj) (fun r ↦ u + (r - 0) • w) univ :=
    isJacobiFieldOn_const_affine uniqueDiffOn_univ u w 0
  have hX : IsJacobiFieldOn I
      (fun r : ℝ ↦ riemannianExp I M (σ 0).proj (r • (0 : TangentSpace I (σ 0).proj))) X univ :=
    hX_const.congr_totalSpace fun r _ ↦ TotalSpace.ext (congrFun hconst r) HEq.rfl
  have hX0 : u = X 0 := by simp [X]
  have hDX0 : w = alongCurveWithin cov
      (fun r : ℝ ↦ riemannianExp I M (σ 0).proj (r • (0 : TangentSpace I (σ 0).proj)))
      X univ 0 := by
    have hD : HEq (alongCurveWithin cov (fun _ : ℝ ↦ (σ 0).proj)
          (fun r ↦ u + (r - 0) • w) univ 0)
        (alongCurveWithin cov
          (fun r : ℝ ↦ riemannianExp I M (σ 0).proj (r • (0 : TangentSpace I (σ 0).proj)))
          X univ 0) :=
      alongCurveWithin_congr_heq cov _ (EventuallyEq.of_eq hconst.symm) (congrFun hconst 0).symm
        (Eventually.of_forall fun _ ↦ HEq.rfl) HEq.rfl
    exact (alongCurveWithin_const_add_smul cov (uniqueDiffOn_univ 0 (mem_univ 0)) u w 0).symm.trans
      (eq_of_heq hD)
  have heq := hX.eq_mfderiv_riemannianExp_tangentBundle isPreconnected_univ (mem_univ 0)
    hσ hσ0 hX0 hDX0 (mem_univ t)
  have hpt : TotalSpace.mk' E (σ 0).proj (t • (0 : TangentSpace I (σ 0).proj)) =
      zeroSection E (TangentSpace I) (σ 0).proj := by
    simp [zeroSection]
  -- Every `TangentSpace I.tangent _` reduces to `E × E`, so the velocity vector is heterogeneously
  -- equal to itself across the equal base points in `hpt`.
  have h1 : HEq
      (mfderiv I.tangent I (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2)
        (zeroSection E (TangentSpace I) (σ 0).proj)
        (curveVelocity I.tangent
          (fun q ↦ TotalSpace.mk' E (σ q).proj (t • (σ q).2)) 0))
      (X t) :=
    (TauCeti.heq_mfderiv_apply (I := I.tangent) (J := I)
      (fun w : TangentBundle I M ↦ riemannianExp I M w.proj w.2) hpt.symm HEq.rfl).trans
      (heq_of_eq heq.symm)
  have h2 : HEq (X t) (u + t • w) := heq_of_eq (by simp only [X, sub_zero]; rfl)
  exact eq_of_heq (h1.trans h2)

end TauCeti.Manifold
