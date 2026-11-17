/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Propagator
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InitialData
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
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
interval as the differential of fibrewise scalar multiplication `(x, v) ↦ (x, t • v)` followed by
the differential of `(x, v) ↦ exp_x v`. Consequently:

* For any curve `σ : ℝ → TM` differentiable at `0`, differentiating `(x, v) ↦ exp_x v` along the
  ray-rescaled path `q ↦ ⟨(σ q).proj, t • (σ q).2⟩` produces a Jacobi field along
  `t ↦ exp_{(σ 0).proj} (t • (σ 0).2)` on its entire maximal geodesic interval, with initial value
  `∂_q (σ q).proj (0)` (proved unconditionally in
  `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_curveVelocity_zero`) and initial covariant
  derivative `D_q (σ q).2 (0)`.
* Conversely, every Jacobi field `X` along `t ↦ exp_p (t • v)` on a preconnected parameter set
  containing `0` agrees with this differential for any curve `σ` differentiable at `0` with matching
  initial data, and in particular arises from a curve `σ` through `(p, v)` smooth on a neighbourhood
  of `0`, with no completeness, nonzero-velocity, or vanishing-initial-value assumption.
* Along a constant geodesic (`v = 0`), for any curve `σ` differentiable at `0` through `0_p`, the
  variable-base differential formula reduces directly to the affine expression
  `∂_q (σ q).proj (0) + t • D_q (σ q).2 (0)` for all `t : ℝ` (see
  `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_zeroSection_curveVelocity` and
  `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_zeroSection_apply` in
  `TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.VariableBase`).

## Main results

* `TangentBundle.geodesicJacobiPropagator_eq_mfderiv_riemannianExp_tangentBundle`: factorization of
  `geodesicJacobiPropagator` through the differential of fibre rescaling and `mfderiv` of
  `(x, v) ↦ exp_x v`.
* `TauCeti.Manifold.mfderiv_riemannianExp_tangentBundle_curveVelocity_eq_geodesicJacobiPropagator`:
  evaluating `mfderiv` of `(x, v) ↦ exp_x v` along the ray-rescaled curve recovers
  `geodesicJacobiPropagator`.
* `TauCeti.Manifold.isJacobiFieldOn_mfderiv_riemannianExp_tangentBundle` and
  `TauCeti.Manifold.alongCurveWithin_mfderiv_riemannianExp_tangentBundle_zero`: the variable-base
  differential of `exp` along a ray-rescaled curve in `TM` is a Jacobi field on the maximal geodesic
  interval with initial covariant derivative `D_q (σ q).2 (0)`.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_mfderiv_riemannianExp_tangentBundle`: on a preconnected
  parameter set containing `0`, every Jacobi field along `t ↦ exp_p (t • v)` agrees with the
  variable-base differential of `exp` along any curve `σ` differentiable at `0` with matching
  initial data.
* `TauCeti.Manifold.IsJacobiFieldOn.exists_contMDiffAt_eq_mfderiv_riemannianExp_tangentBundle`: on a
  preconnected parameter set containing `0`, every Jacobi field along `t ↦ exp_p (t • v)` is
  realized by differentiating `(x, v) ↦ exp_x v` along a curve `σ` in `TM` smooth on a neighbourhood
  of `0`.

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
    ((contMDiffAt_const (c := t)).smul_totalSpace contMDiffAt_id).mdifferentiableAt
      (n := 1) one_ne_zero
  have hg : MDifferentiableAt I.tangent I g (f z) :=
    (contMDiffAt_riemannianExp_tangentBundle
      (mem_geodesicInterval_iff_smul_mem_expDomain.mp ht)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_apply z hg hf ξ
  have hfun : (fun w : TangentBundle I M ↦ maximalGeodesic I M w.proj w.2 t) = g ∘ f :=
    funext fun w ↦ (riemannianExp_smul w.proj w.2 t).symm
  exact (DFunLike.congr_fun (mfderiv_congr (I := I.tangent) (I' := I) hfun) ξ).trans hcomp

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
    ((contMDiffAt_const (c := t)).smul_totalSpace contMDiffAt_id).mdifferentiableAt
      (n := 1) one_ne_zero
  have hvel : curveVelocity I.tangent (f ∘ σ) 0 =
      mfderiv I.tangent I.tangent f (σ 0) (curveVelocity I.tangent σ 0) := by
    rw [curveVelocity_apply, curveVelocity_apply]
    exact mfderiv_comp_apply 0 hf hσ (1 : ℝ)
  rw [TangentBundle.geodesicJacobiPropagator_eq_mfderiv_riemannianExp_tangentBundle (σ 0) ht,
    ← hvel]
  simp only [f, Function.comp_def]

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
  -- At `t = 0`, `TangentSpace I (exp_{(σ 0).proj} (0 • (σ 0).2))` and
  -- `TangentSpace I (maximalGeodesic I M (σ 0).proj (σ 0).2 0)` both reduce to `E`.
  exact (eq_of_heq hD).trans (TangentBundle.alongCurveWithin_geodesicJacobiPropagator_zero hσ)

/-- **Every Jacobi field along `t ↦ exp_p (t • v)` on a preconnected parameter set containing `0`
agrees with the variable-base differential of `exp` along any matching initial-data curve in `TM`
differentiable at `0`.** Unlike `IsJacobiFieldOn.eq_mfderiv_riemannianExp`, the initial value `X 0`
need not vanish (including along a constant geodesic `v = 0`). -/
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

/-- **Every Jacobi field along `t ↦ exp_p (t • v)` on a preconnected parameter set containing `0`
arises from differentiating `(x, v) ↦ exp_x v` along a curve in `TM` smooth on a neighbourhood of
`0`.** No completeness, nonzero-velocity, or vanishing-initial-value hypothesis is imposed. -/
theorem IsJacobiFieldOn.exists_contMDiffAt_eq_mfderiv_riemannianExp_tangentBundle
    {p : M} {v : TangentSpace I p}
    {X : ∀ t : ℝ, TangentSpace I (riemannianExp I M p (t • v))} {s : Set ℝ}
    (hX : IsJacobiFieldOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) X s)
    (hs : IsPreconnected s) (h0 : (0 : ℝ) ∈ s) :
    ∃ σ : ℝ → TangentBundle I M,
      σ 0 = TotalSpace.mk' E p v ∧
      (∀ᶠ q in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ σ q) ∧
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
  exact ⟨σ, hσ0, hσ, hpos, hvel, fun _ ht ↦
    hX.eq_mfderiv_riemannianExp_tangentBundle hs h0 (hσ.self_of_nhds.mdifferentiableAt (by simp))
      hσ0 hpos hvel ht⟩

end TauCeti.Manifold
