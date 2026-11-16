/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Constant metric rescaling of asymptotically Euclidean ends

Multiplying a `C^m` Riemannian metric `g` on a `C¹` manifold `M` by a positive constant `c > 0`
turns an asymptotically Euclidean end `e` of order `t` with excised radius `R` into an
asymptotically Euclidean end `e.rescale m hc` of the same order `t` on
`WithMetric (rescaledMetric m hc)` with excised radius `√c * R` and parametrization
`y ↦ toWithMetric _ (e.toFun ((√c)⁻¹ • y))`.

The compensating coordinate dilation `y ↦ (√c)⁻¹ • y` cancels the metric scaling factor `c` in
the pulled-back metric coefficients, giving

`(e.rescale m hc).metricCoeff y i j = e.metricCoeff ((√c)⁻¹ • y) i j`

on the exterior domain `√c * e.radius < ‖y‖`. Because `fderiv_comp_smul` and
`fderiv_const_smul_field` require no differentiability hypotheses, this holds for every smoothness
order `m : ℕ∞ω` of the ambient metric.

## Main definitions

* `TauCeti.AsymptoticallyEuclideanEnd.rescaledMetric`: the constant rescaling `c • g` (`0 < c`) of
  the ambient `C^m` Riemannian metric on `M`.
* `TauCeti.AsymptoticallyEuclideanEnd.rescale`: the rescaled asymptotically Euclidean end on
  `WithMetric (rescaledMetric m hc)`.

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.radius_rescale`,
  `TauCeti.AsymptoticallyEuclideanEnd.toFun_rescale`,
  `TauCeti.AsymptoticallyEuclideanEnd.range_rescale`: the radius, pointwise formula, and range of
  a rescaled end.
* `TauCeti.AsymptoticallyEuclideanEnd.metricCoeff_rescale`,
  `TauCeti.AsymptoticallyEuclideanEnd.metricMatrix_rescale`: the pulled-back metric coefficients
  and metric matrix transform by `y ↦ (√c)⁻¹ • y`.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

namespace AsymptoticallyEuclideanEnd

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- The constant rescaling `c • g` (`0 < c`) of the ambient `C^m` Riemannian metric on `M`. -/
abbrev rescaledMetric (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)] {c : ℝ} (hc : 0 < c) :
    ContMDiffRiemannianMetric (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x) :=
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := 𝓡 n) (n := m)
    (F := EuclideanSpace ℝ (Fin n)) (V := fun x : M ↦ TangentSpace (𝓡 n) x)).rescale
    (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)

/-- Domain dilation `y ↦ (√c)⁻¹ • y` from `exteriorBall n (√c * R)` to
`exteriorBall n R`. -/
private def rescaleMapDomain {R c : ℝ} (hc : 0 < c) :
    exteriorBall n (Real.sqrt c * R) → exteriorBall n R := fun y ↦
  ⟨(Real.sqrt c)⁻¹ • (y : EuclideanSpace ℝ (Fin n)), mem_exteriorBall.2 <| by
    have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    have hy : Real.sqrt c * R < ‖(y : EuclideanSpace ℝ (Fin n))‖ := mem_exteriorBall.1 y.2
    calc R = (Real.sqrt c)⁻¹ * (Real.sqrt c * R) := by field_simp
      _ < (Real.sqrt c)⁻¹ * ‖(y : EuclideanSpace ℝ (Fin n))‖ :=
        mul_lt_mul_of_pos_left hy (inv_pos.2 hs)⟩

private theorem surjective_rescaleMapDomain {R c : ℝ} (hc : 0 < c) :
    Function.Surjective (rescaleMapDomain (n := n) (R := R) hc) := fun x ↦ by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨⟨Real.sqrt c • (x : EuclideanSpace ℝ (Fin n)), mem_exteriorBall.2 ?_⟩, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_lt_mul_of_pos_left (mem_exteriorBall.1 x.2) hs
  · ext
    simp [rescaleMapDomain, smul_smul, inv_mul_cancel₀ hs.ne']

private theorem contMDiff_rescaleMapDomain {R c : ℝ} (hc : 0 < c) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (rescaleMapDomain (n := n) (R := R) hc) := by
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff (exteriorBall n R)
    (rescaleMapDomain hc)).1 ?_
  exact (contDiff_const_smul (Real.sqrt c)⁻¹).contMDiff.comp contMDiff_subtype_val

private theorem mfderiv_rescaleMapDomain_apply {R c : ℝ} (hc : 0 < c)
    (y : exteriorBall n (Real.sqrt c * R)) (v : TangentSpace (𝓡 n) y) :
    mfderiv (𝓡 n) (𝓡 n) (rescaleMapDomain (n := n) (R := R) hc) y v =
      (Real.sqrt c)⁻¹ • (v : EuclideanSpace ℝ (Fin n)) := by
  have hv := TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply
    (I := 𝓡 n) (I' := 𝓡 n) (f := rescaleMapDomain (n := n) (R := R) hc)
    (A := fun z : EuclideanSpace ℝ (Fin n) ↦ (Real.sqrt c)⁻¹ • z) rfl (x := y) v
  rw [TauCeti.Manifold.tangentSpaceOpenEquiv_apply,
    TauCeti.Manifold.tangentSpaceOpenEquiv_apply] at hv
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ _
  have hL : (fun z : EuclideanSpace ℝ (Fin n) ↦ (Real.sqrt c)⁻¹ • z) = ⇑L :=
    funext fun _ ↦ rfl
  have hf : mfderiv (𝓡 n) (𝓡 n) (⇑L) (y : EuclideanSpace ℝ (Fin n)) = L :=
    (L.hasFDerivAt (x := (y : EuclideanSpace ℝ (Fin n)))).hasMFDerivAt.mfderiv
  have hsmul : mfderiv (𝓡 n) (𝓡 n)
      (fun z : EuclideanSpace ℝ (Fin n) ↦ (Real.sqrt c)⁻¹ • z) (y : _) v =
      (Real.sqrt c)⁻¹ • (v : EuclideanSpace ℝ (Fin n)) := by
    rw [hL]
    exact DFunLike.congr_fun hf (v : EuclideanSpace ℝ (Fin n))
  exact hv.trans hsmul

private theorem openPullbackMetricCoeff_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c)
    {y : EuclideanSpace ℝ (Fin n)} (hy : Real.sqrt c * e.radius < ‖y‖) (i j : Fin n) :
    openPullbackMetricCoeff
        (WithMetric.toWithMetric (rescaledMetric (n := n) (M := M) m hc) ∘
          e.toFun ∘ rescaleMapDomain hc) y i j =
      e.metricCoeff ((Real.sqrt c)⁻¹ • y) i j := by
  set g_c := rescaledMetric (n := n) (M := M) m hc
  set s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hy' : y ∈ exteriorBall n (s * e.radius) := mem_exteriorBall.2 hy
  have hsy' : s⁻¹ • y ∈ exteriorBall n e.radius := (rescaleMapDomain hc ⟨y, hy'⟩).2
  let p : M := e.toFun (rescaleMapDomain hc ⟨y, hy'⟩)
  have hcomp_deriv (k : Fin n) :
      mfderiv (𝓡 n) (𝓡 n) (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc)
          ⟨y, hy'⟩ (EuclideanSpace.basisFun (Fin n) ℝ k) =
        mfderiv (𝓡 n) (𝓡 n) (WithMetric.toWithMetric g_c) p
          (s⁻¹ • mfderiv (𝓡 n) (𝓡 n) e.toFun (rescaleMapDomain hc ⟨y, hy'⟩)
            (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    have h1 := mfderiv_comp_apply (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n) ⟨y, hy'⟩
      ((WithMetric.contMDiff_toWithMetric (g := g_c) (k := ∞)).mdifferentiable (by simp) _)
      ((e.contMDiff.comp (contMDiff_rescaleMapDomain hc)).mdifferentiable (by simp) _)
      (EuclideanSpace.basisFun (Fin n) ℝ k)
    have h2 := mfderiv_comp_apply (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n) ⟨y, hy'⟩
      (e.contMDiff.mdifferentiable (by simp) _)
      ((contMDiff_rescaleMapDomain hc).mdifferentiable (by simp) _)
      (EuclideanSpace.basisFun (Fin n) ℝ k)
    have h3 : mfderiv (𝓡 n) (𝓡 n) e.toFun (rescaleMapDomain hc ⟨y, hy'⟩)
        (mfderiv (𝓡 n) (𝓡 n) (rescaleMapDomain hc) ⟨y, hy'⟩
          (EuclideanSpace.basisFun (Fin n) ℝ k)) =
        s⁻¹ • mfderiv (𝓡 n) (𝓡 n) e.toFun (rescaleMapDomain hc ⟨y, hy'⟩)
          (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      let v : TangentSpace (𝓡 n) (rescaleMapDomain hc ⟨y, hy'⟩) :=
        EuclideanSpace.basisFun (Fin n) ℝ k
      have hmd : mfderiv (𝓡 n) (𝓡 n) (rescaleMapDomain hc) ⟨y, hy'⟩
          (EuclideanSpace.basisFun (Fin n) ℝ k) = s⁻¹ • v :=
        mfderiv_rescaleMapDomain_apply hc ⟨y, hy'⟩ (EuclideanSpace.basisFun (Fin n) ℝ k)
      rw [hmd, map_smul]
    rw [h1, h2, h3]
    rfl
  rw [openPullbackMetricCoeff_of_mem _ hy', e.metricCoeff_of_mem hsy',
    hcomp_deriv i, hcomp_deriv j, WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
    ContMDiffRiemannianMetric.rescale_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  have hbilin (u v : TangentSpace (𝓡 n) p) :
      RiemannianBundle.g.inner p (s⁻¹ • u) (s⁻¹ • v) =
        s⁻¹ * (s⁻¹ * RiemannianBundle.g.inner p u v) := by
    rw [map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hbilin]
  have hcs : c * (s⁻¹ * s⁻¹) = 1 := by
    have hs2 : s * s = c := Real.mul_self_sqrt hc.le
    field_simp [hs.ne']
    linarith
  have hinner : RiemannianBundle.g.inner p
      (mfderiv (𝓡 n) (𝓡 n) e.toFun (rescaleMapDomain hc ⟨y, hy'⟩)
        (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) e.toFun (rescaleMapDomain hc ⟨y, hy'⟩)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      inner ℝ
        (mfderiv (𝓡 n) (𝓡 n) e.toFun ⟨s⁻¹ • y, hsy'⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) e.toFun ⟨s⁻¹ • y, hsy'⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)) :=
    rfl
  rw [hinner]
  calc c * (s⁻¹ * (s⁻¹ * inner ℝ _ _))
      = (c * (s⁻¹ * s⁻¹)) * inner ℝ _ _ := by ring
    _ = inner ℝ _ _ := by rw [hcs, one_mul]

/-- Rescaling a `C^m` Riemannian metric by a positive constant `c` turns an asymptotically
Euclidean end `e` of `M` into an asymptotically Euclidean end of
`WithMetric (rescaledMetric m hc)` with radius `√c * e.radius` and parametrization
`y ↦ toWithMetric _ (e.toFun ((√c)⁻¹ • y))`. -/
def rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c) :
    AsymptoticallyEuclideanEnd n (WithMetric (rescaledMetric (n := n) (M := M) m hc)) t :=
  let g_c := rescaledMetric (n := n) (M := M) m hc
  let s : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  { radius := s * e.radius
    radius_pos := mul_pos hs e.radius_pos
    toFun := WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc
    contMDiff := WithMetric.contMDiff_toWithMetric.comp
      (e.contMDiff.comp (contMDiff_rescaleMapDomain hc))
    injective := (WithMetric.toWithMetric_injective _).comp <| e.injective.comp fun x y hxy ↦ by
      have hv :
          s⁻¹ • (x : EuclideanSpace ℝ (Fin n)) = s⁻¹ • (y : EuclideanSpace ℝ (Fin n)) :=
        congrArg Subtype.val hxy
      exact Subtype.ext (smul_right_injective _ (inv_ne_zero hs.ne') hv)
    mfderiv_bijective := fun y ↦ by
      rw [mfderiv_comp y
          ((WithMetric.contMDiff_toWithMetric (g := g_c) (k := ∞)).mdifferentiable (by simp) _)
          ((e.contMDiff.comp (contMDiff_rescaleMapDomain hc)).mdifferentiable (by simp) y),
        mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) _)
          ((contMDiff_rescaleMapDomain hc).mdifferentiable (by simp) y),
        WithMetric.mfderiv_toWithMetric]
      have hsmul_bij : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (rescaleMapDomain hc) y) :=
        ⟨fun u v huv ↦ by
          have hu := mfderiv_rescaleMapDomain_apply hc y u
          have hv := mfderiv_rescaleMapDomain_apply hc y v
          have h : s⁻¹ • (u : EuclideanSpace ℝ (Fin n)) =
              s⁻¹ • (v : EuclideanSpace ℝ (Fin n)) := by
            rw [← hu, ← hv, huv]
          exact smul_right_injective _ (inv_ne_zero hs.ne') h,
         fun v ↦ by
          let vE : EuclideanSpace ℝ (Fin n) := v
          let w : TangentSpace (𝓡 n) y := s • vE
          refine ⟨w, ?_⟩
          have h :
              (mfderiv (𝓡 n) (𝓡 n) (rescaleMapDomain hc) y w : EuclideanSpace ℝ (Fin n)) =
                s⁻¹ • (s • vE) :=
            mfderiv_rescaleMapDomain_apply hc y w
          exact h.trans (by rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul])⟩
      exact Function.bijective_id.comp
        ((e.mfderiv_bijective (rescaleMapDomain hc y)).comp hsmul_bij)
    decay := by
      obtain ⟨C, hC⟩ := e.decay
      simp only [← e.metricCoeff_eq_openPullbackMetricCoeff] at hC
      refine ⟨C * s ^ t, fun y hy i j ↦ ?_⟩
      let f : EuclideanSpace ℝ (Fin n) → ℝ := fun w ↦ e.metricCoeff w i j
      have hsy : e.radius < ‖s⁻¹ • y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
        calc e.radius = s⁻¹ * (s * e.radius) := by field_simp
          _ < s⁻¹ * ‖y‖ := mul_lt_mul_of_pos_left hy (inv_pos.2 hs)
      have hy0 : 0 < ‖y‖ := (mul_pos hs e.radius_pos).trans hy
      have hnorm : ‖s⁻¹ • y‖ = s⁻¹ * ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      have hev : (fun z ↦ openPullbackMetricCoeff
            (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc) z i j) =ᶠ[𝓝 y]
          (fun z ↦ f (s⁻¹ • z)) :=
        eventually_of_mem ((exteriorBall n (s * e.radius)).isOpen.mem_nhds (mem_exteriorBall.2 hy))
          fun z hz ↦ openPullbackMetricCoeff_rescale m e hc (mem_exteriorBall.1 hz) i j
      have hf1 : fderiv ℝ (fun w ↦ f (s⁻¹ • w)) = fun z ↦ s⁻¹ • fderiv ℝ f (s⁻¹ • z) :=
        funext fun z ↦ fderiv_comp_smul (f := f) (x := z) s⁻¹
      have hf2 : fderiv ℝ (fderiv ℝ (fun w ↦ f (s⁻¹ • w))) y =
          (s⁻¹ * s⁻¹) • fderiv ℝ (fderiv ℝ f) (s⁻¹ • y) := by
        rw [hf1]
        have hpi : (fun z ↦ s⁻¹ • fderiv ℝ f (s⁻¹ • z)) =
            s⁻¹ • (fun z ↦ fderiv ℝ f (s⁻¹ • z)) := rfl
        have hsmul : fderiv ℝ (s⁻¹ • fun z ↦ fderiv ℝ f (s⁻¹ • z)) y =
            s⁻¹ • fderiv ℝ (fun z ↦ fderiv ℝ f (s⁻¹ • z)) y :=
          congrFun (fderiv_const_smul_field (𝕜 := ℝ)
            (f := fun z ↦ fderiv ℝ f (s⁻¹ • z)) s⁻¹) y
        rw [hpi, hsmul, fderiv_comp_smul (f := fderiv ℝ f) (x := y) s⁻¹, smul_smul]
      obtain ⟨h0, h1, h2⟩ := hC (s⁻¹ • y) hsy i j
      have hev0 : openPullbackMetricCoeff
            (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc) y i j =
          f (s⁻¹ • y) := hev.self_of_nhds
      have hev1 : fderiv ℝ (fun z ↦ openPullbackMetricCoeff
            (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc) z i j) y =
          s⁻¹ • fderiv ℝ f (s⁻¹ • y) := by
        rw [hev.fderiv_eq, hf1]
      have hev2 : fderiv ℝ (fderiv ℝ (fun z ↦ openPullbackMetricCoeff
            (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc) z i j)) y =
          (s⁻¹ * s⁻¹) • fderiv ℝ (fderiv ℝ f) (s⁻¹ • y) :=
        hev.fderiv.fderiv_eq.trans hf2
      refine ⟨?_, ?_, ?_⟩
      · rw [hev0]
        have hrpow : ‖s⁻¹ • y‖ ^ (-t) = s ^ t * ‖y‖ ^ (-t) := by
          rw [hnorm, Real.mul_rpow (inv_nonneg.2 hs.le) hy0.le, Real.inv_rpow hs.le,
            Real.rpow_neg hs.le, inv_inv]
        calc |f (s⁻¹ • y) - if i = j then 1 else 0|
            ≤ C * ‖s⁻¹ • y‖ ^ (-t) := h0
          _ = C * s ^ t * ‖y‖ ^ (-t) := by rw [hrpow]; ring
      · rw [hev1]
        have hrpow :
            s⁻¹ * (C * ‖s⁻¹ • y‖ ^ (-t - 1)) = C * s ^ t * ‖y‖ ^ (-t - 1) := by
          rw [hnorm, Real.mul_rpow (inv_nonneg.2 hs.le) hy0.le, Real.inv_rpow hs.le,
            Real.rpow_sub hs, Real.rpow_neg hs.le, Real.rpow_one, inv_div, div_inv_eq_mul]
          field_simp [hs.ne']
        calc ‖s⁻¹ • fderiv ℝ f (s⁻¹ • y)‖
            ≤ ‖s⁻¹‖ * ‖fderiv ℝ f (s⁻¹ • y)‖ := ContinuousLinearMap.opNorm_smul_le _ _
          _ = s⁻¹ * ‖fderiv ℝ f (s⁻¹ • y)‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
          _ ≤ s⁻¹ * (C * ‖s⁻¹ • y‖ ^ (-t - 1)) :=
              mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs.le)
          _ = C * s ^ t * ‖y‖ ^ (-t - 1) := hrpow
      · rw [hev2]
        have hrpow :
            s⁻¹ * s⁻¹ * (C * ‖s⁻¹ • y‖ ^ (-t - 2)) = C * s ^ t * ‖y‖ ^ (-t - 2) := by
          rw [hnorm, Real.mul_rpow (inv_nonneg.2 hs.le) hy0.le, Real.inv_rpow hs.le,
            Real.rpow_sub hs, Real.rpow_neg hs.le, Real.rpow_two, inv_div, div_inv_eq_mul]
          field_simp [hs.ne']
        calc ‖(s⁻¹ * s⁻¹) • fderiv ℝ (fderiv ℝ f) (s⁻¹ • y)‖
            ≤ ‖s⁻¹ * s⁻¹‖ * ‖fderiv ℝ (fderiv ℝ f) (s⁻¹ • y)‖ :=
              ContinuousLinearMap.opNorm_smul_le _ _
          _ = (s⁻¹ * s⁻¹) * ‖fderiv ℝ (fderiv ℝ f) (s⁻¹ • y)‖ := by
              rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hs.le) (inv_nonneg.2 hs.le))]
          _ ≤ s⁻¹ * s⁻¹ * (C * ‖s⁻¹ • y‖ ^ (-t - 2)) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg (inv_nonneg.2 hs.le) (inv_nonneg.2 hs.le))
          _ = C * s ^ t * ‖y‖ ^ (-t - 2) := hrpow }

@[simp]
theorem radius_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c) :
    (e.rescale m hc).radius = Real.sqrt c * e.radius := by
  rfl

/-- Pointwise evaluation of the rescaled end parametrization:
`(e.rescale m hc).toFun y = WithMetric.toWithMetric _ (e.toFun ((√c)⁻¹ • y))`. -/
theorem toFun_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ exteriorBall n (e.rescale m hc).radius)
    (hy' : (Real.sqrt c)⁻¹ • y ∈ exteriorBall n e.radius) :
    (e.rescale m hc).toFun ⟨y, hy⟩ =
      WithMetric.toWithMetric (rescaledMetric (n := n) (M := M) m hc)
        (e.toFun ⟨(Real.sqrt c)⁻¹ • y, hy'⟩) := by
  rfl

/-- The range of a rescaled end is the image of the original end's range under
`WithMetric.toWithMetric`. -/
theorem range_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c) :
    Set.range (e.rescale m hc).toFun =
      WithMetric.toWithMetric (rescaledMetric (n := n) (M := M) m hc) '' Set.range e.toFun := by
  dsimp only [rescale]
  rw [Set.range_comp, Set.range_comp, (surjective_rescaleMapDomain hc).range_eq, Set.image_univ]

/-- Under constant metric rescaling `g ↦ c • g`, the pulled-back metric coefficients satisfy
`(e.rescale m hc).metricCoeff y = e.metricCoeff ((√c)⁻¹ • y)` on the exterior domain. -/
theorem metricCoeff_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c)
    {y : EuclideanSpace ℝ (Fin n)} (hy : Real.sqrt c * e.radius < ‖y‖) (i j : Fin n) :
    (e.rescale m hc).metricCoeff y i j = e.metricCoeff ((Real.sqrt c)⁻¹ • y) i j := by
  rw [metricCoeff_eq_openPullbackMetricCoeff]
  exact openPullbackMetricCoeff_rescale m e hc hy i j

/-- Under constant metric rescaling `g ↦ c • g`, the pulled-back metric matrix satisfies
`(e.rescale m hc).metricMatrix y = e.metricMatrix ((√c)⁻¹ • y)` on the exterior domain. -/
theorem metricMatrix_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) {c : ℝ} (hc : 0 < c)
    {y : EuclideanSpace ℝ (Fin n)} (hy : Real.sqrt c * e.radius < ‖y‖) :
    (e.rescale m hc).metricMatrix y = e.metricMatrix ((Real.sqrt c)⁻¹ • y) := by
  ext i j
  rw [metricMatrix_apply, metricMatrix_apply]
  exact e.metricCoeff_rescale m hc hy i j

end AsymptoticallyEuclideanEnd

end TauCeti

end
