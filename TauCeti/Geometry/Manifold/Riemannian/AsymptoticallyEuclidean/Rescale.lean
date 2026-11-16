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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Constant metric rescaling of asymptotically Euclidean ends

Multiplying a `C^m` Riemannian metric `g` on a `C¹` manifold `M` by a positive constant `c > 0`
turns an asymptotically Euclidean end `e` of order `t` with excised radius `R` into an
asymptotically Euclidean end `e.rescale m hc` of the same order `t` on
`WithMetric (rescaledMetric I M m hc)` with excised radius `√c * R` and parametrization
`y ↦ toWithMetric _ (e.toFun ((√c)⁻¹ • y))`.

Rescaling `g` alone multiplies the asymptotic metric limit by `c` (sending `δ_ij` to `c δ_ij`), so
the compensating coordinate dilation `y ↦ (√c)⁻¹ • y` cancels `c` in the pulled-back metric
coefficients and restores the Euclidean limit `δ_ij`, yielding

`(e.rescale m hc).metricCoeff y i j = e.metricCoeff ((√c)⁻¹ • y) i j`

for every `y : EuclideanSpace ℝ (Fin n)`. Because an asymptotically Euclidean end `e` already
guarantees `C²` regularity and second-order decay of `e.metricCoeff` on its exterior domain, and
smooth linear dilation preserves both properties, `e.rescale m hc` requires no `2 ≤ m` assumption on
the ambient metric.

## Main definitions

* `TauCeti.AsymptoticallyEuclideanEnd.rescale`: the rescaled asymptotically Euclidean end on
  `WithMetric (rescaledMetric I M m hc)`.

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

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {t : ℝ}

/-- Membership in the dilated exterior ball is equivalent to membership of the scaled point in the
original exterior ball. -/
private theorem mem_exteriorBall_inv_sqrt_smul_iff {R c : ℝ} (hc : 0 < c)
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) (Real.sqrt c * R) ↔
      (Real.sqrt c)⁻¹ • y ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) R := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  simp only [mem_exteriorBall, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  exact (lt_inv_mul_iff₀ hs).symm

/-- Domain dilation `y ↦ (√c)⁻¹ • y` as a smooth diffeomorphism from
`exteriorBall (EuclideanSpace ℝ (Fin n)) (√c * R)` to
`exteriorBall (EuclideanSpace ℝ (Fin n)) R`. -/
private def rescaleMapDomain {R c : ℝ} (hc : 0 < c) :
    exteriorBall (EuclideanSpace ℝ (Fin n)) (Real.sqrt c * R) ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯
      exteriorBall (EuclideanSpace ℝ (Fin n)) R :=
  ((Units.mk0 (Real.sqrt c)⁻¹ (inv_ne_zero (Real.sqrt_pos.2 hc).ne') •
    ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).toDiffeomorph).subtype
    (fun x ↦ by simpa using mem_exteriorBall_inv_sqrt_smul_iff hc x)

/-- Pointwise coercion formula for `rescaleMapDomain`. -/
private theorem rescaleMapDomain_val {R c : ℝ} (hc : 0 < c)
    (y : exteriorBall (EuclideanSpace ℝ (Fin n)) (Real.sqrt c * R)) :
    (rescaleMapDomain hc y : EuclideanSpace ℝ (Fin n)) =
      (Real.sqrt c)⁻¹ • (y : EuclideanSpace ℝ (Fin n)) := by
  rw [rescaleMapDomain, Diffeomorph.subtype_apply_coe]; simp

/-- The second Fréchet derivative of a scalar-dilated function `w ↦ f (a • w)` scales by `a * a`. -/
private theorem fderiv_fderiv_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (a : ℝ) (y : F) :
    fderiv ℝ (fderiv ℝ (fun w ↦ f (a • w))) y = (a * a) • fderiv ℝ (fderiv ℝ f) (a • y) := by
  have hf1 : fderiv ℝ (fun w ↦ f (a • w)) = a • (fun z ↦ fderiv ℝ f (a • z)) :=
    funext fun z ↦ fderiv_comp_smul (f := f) (x := z) a
  have hsmul : fderiv ℝ (a • fun z ↦ fderiv ℝ f (a • z)) y =
      a • fderiv ℝ (fun z ↦ fderiv ℝ f (a • z)) y :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun z ↦ fderiv ℝ f (a • z)) a) y
  rw [hf1, hsmul, fderiv_comp_smul (f := fderiv ℝ f) (x := y) a, smul_smul]

/-- Dilation scaling identity for the `k`-th order decay bound under `y ↦ s⁻¹ • y`. -/
private theorem inv_pow_mul_rpow_smul {s r t C : ℝ} (hs : 0 < s) (hr : 0 < r) (k : ℕ) :
    s⁻¹ ^ k * (C * (s⁻¹ * r) ^ (-t - k)) = C * s ^ t * r ^ (-t - k) := by
  rw [Real.mul_rpow (inv_nonneg.2 hs.le) hr.le, Real.inv_rpow hs.le,
    Real.rpow_sub hs, Real.rpow_neg hs.le, Real.rpow_natCast, inv_div, div_inv_eq_mul, inv_pow]
  have hsk : s ^ k ≠ 0 := pow_ne_zero k hs.ne'
  field_simp [hs.ne', hsk]

section Rescale

variable (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
  (e : AsymptoticallyEuclideanEnd n I M t) {c : ℝ} (hc : 0 < c)

/-- Postcomposing a total map `ψ : ℝⁿ → M` with `WithMetric.toWithMetric (rescaledMetric I M m hc)`
multiplies its pulled-back metric coefficients by `c`. -/
private theorem pullbackMetricCoeff_toWithMetric_rescaledMetric_comp
    (ψ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff I (WithMetric.toWithMetric (rescaledMetric I M m hc) ∘ ψ) x i j =
      c * pullbackMetricCoeff I ψ x i j := by
  set g_c := rescaledMetric I M m hc
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) I (WithMetric.toWithMetric g_c ∘ ψ) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        mfderiv I I (WithMetric.toWithMetric g_c) (ψ x)
          (mfderiv (𝓡 n) I ψ x (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    have h := (WithMetric.diffeomorph g_c ∞).symm.mfderiv_diffeomorph_comp (K := 𝓡 n)
      (hn := by simp) (f := ψ) (x := x)
    rw [WithMetric.coe_diffeomorph_symm] at h
    exact (DFunLike.congr_fun h _).trans (ContinuousLinearMap.comp_apply _ _ _)
  rw [pullbackMetricCoeff_def, pullbackMetricCoeff_def, hderiv i, hderiv j,
    WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric]
  -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
  exact (ContMDiffRiemannianMetric.rescaleConst_inner _ hc (ψ x) _ _).trans
    (congrArg (c * ·) (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner (ψ x) _ _))

/-- On the dilated exterior ball, the pulled-back metric coefficients of the rescaled end agree
with `e.metricCoeff` evaluated at `(√c)⁻¹ • y`. -/
private theorem openPullbackMetricCoeff_rescale
    {y : EuclideanSpace ℝ (Fin n)} (hy : Real.sqrt c * e.radius < ‖y‖) (i j : Fin n) :
    openPullbackMetricCoeff I
        (WithMetric.toWithMetric (rescaledMetric I M m hc) ∘ e.toFun ∘ rescaleMapDomain hc)
        y i j =
      e.metricCoeff ((Real.sqrt c)⁻¹ • y) i j := by
  set g_c := rescaledMetric I M m hc
  set s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hy' : y ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) (s * e.radius) := mem_exteriorBall.2 hy
  have hsy' : s⁻¹ • y ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius :=
    (mem_exteriorBall_inv_sqrt_smul_iff hc y).1 hy'
  -- Extend `e.toFun` to a total map so metric rescaling and scalar dilation factor cleanly.
  let ψ : EuclideanSpace ℝ (Fin n) → M :=
    Subtype.val.extend e.toFun (fun _ ↦ e.toFun ⟨s⁻¹ • y, hsy'⟩)
  have hψ : ∀ z : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius, ψ z.1 = e.toFun z :=
    Subtype.val_injective.extend_apply e.toFun _
  have heq_rescaled :
      ∀ z : exteriorBall (EuclideanSpace ℝ (Fin n)) (s * e.radius),
        (fun w ↦ (WithMetric.toWithMetric g_c ∘ ψ) (s⁻¹ • w)) z.1 =
          (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc) z := fun z ↦ by
    change WithMetric.toWithMetric g_c (ψ (s⁻¹ • z.1)) =
      WithMetric.toWithMetric g_c (e.toFun (rescaleMapDomain hc z))
    rw [← rescaleMapDomain_val hc z, hψ (rescaleMapDomain hc z)]
  rw [openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn
        (ψ := fun w ↦ (WithMetric.toWithMetric g_c ∘ ψ) (s⁻¹ • w)) heq_rescaled hy' i j,
    e.metricCoeff_eq_pullbackMetricCoeff_of_eqOn hψ (mem_exteriorBall.1 hsy') i j,
    pullbackMetricCoeff_comp_smul (WithMetric.toWithMetric g_c ∘ ψ) (inv_ne_zero hs.ne') y i j,
    pullbackMetricCoeff_toWithMetric_rescaledMetric_comp m hc ψ (s⁻¹ • y) i j]
  have hcs : s⁻¹ ^ 2 * c = 1 := by
    rw [← Real.sq_sqrt hc.le, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]
  rw [← mul_assoc, hcs, one_mul]

/-- Rescaling a `C^m` Riemannian metric by a positive constant `c` turns an asymptotically
Euclidean end `e` of `M` into an asymptotically Euclidean end of
`WithMetric (rescaledMetric I M m hc)` with radius `√c * e.radius` and parametrization
`y ↦ toWithMetric _ (e.toFun ((√c)⁻¹ • y))`. -/
def rescale : AsymptoticallyEuclideanEnd n I (WithMetric (rescaledMetric I M m hc)) t :=
  let g_c := rescaledMetric I M m hc
  let s : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  { radius := s * e.radius
    radius_pos := mul_pos hs e.radius_pos
    toFun := WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc
    contMDiff := WithMetric.contMDiff_toWithMetric.comp
      (e.contMDiff.comp (rescaleMapDomain hc).contMDiff)
    injective := (WithMetric.toWithMetric_injective g_c).comp
      (e.injective.comp (rescaleMapDomain hc).injective)
    mfderiv_bijective y := by
      rw [mfderiv_comp y
          ((WithMetric.contMDiff_toWithMetric (g := g_c) (k := ∞)).mdifferentiable (by simp) _)
          ((e.contMDiff.comp (rescaleMapDomain hc).contMDiff).mdifferentiable (by simp) y),
        mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) _)
          ((rescaleMapDomain hc).contMDiff.mdifferentiable (by simp) y),
        WithMetric.mfderiv_toWithMetric]
      exact Function.bijective_id.comp
        ((e.mfderiv_bijective (rescaleMapDomain hc y)).comp
          ((rescaleMapDomain hc).isInvertible_mfderiv (by simp)).bijective)
    contDiffOn_openPullbackMetricCoeff i j := by
      -- Transport `C²` regularity of `e.metricCoeff` along the smooth dilation `y ↦ s⁻¹ • y`.
      have hmaps : Set.MapsTo (fun y : EuclideanSpace ℝ (Fin n) ↦ s⁻¹ • y)
          (exteriorBall (EuclideanSpace ℝ (Fin n)) (s * e.radius) : Set _)
          (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set _) :=
        fun y hy ↦ (mem_exteriorBall_inv_sqrt_smul_iff hc y).1 hy
      exact ((e.contDiffOn_two_metricCoeff i j).comp
        (contDiff_const_smul s⁻¹).contDiffOn hmaps).congr fun y hy ↦
          openPullbackMetricCoeff_rescale m e hc (mem_exteriorBall.1 hy) i j
    decay := by
      obtain ⟨C, hC⟩ := e.decay
      simp only [← e.metricCoeff_eq_openPullbackMetricCoeff] at hC
      refine ⟨C * s ^ t, fun y hy i j ↦ ?_⟩
      let f : EuclideanSpace ℝ (Fin n) → ℝ := fun w ↦ e.metricCoeff w i j
      have hsy : e.radius < ‖s⁻¹ • y‖ :=
        mem_exteriorBall.1 ((mem_exteriorBall_inv_sqrt_smul_iff hc y).1 (mem_exteriorBall.2 hy))
      have hy0 : 0 < ‖y‖ := (mul_pos hs e.radius_pos).trans hy
      have hnorm : ‖s⁻¹ • y‖ = s⁻¹ * ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      -- Locally near `y`, the rescaled coefficients equal `z ↦ f (s⁻¹ • z)`.
      have hev : (fun z ↦ openPullbackMetricCoeff I
            (WithMetric.toWithMetric g_c ∘ e.toFun ∘ rescaleMapDomain hc) z i j) =ᶠ[𝓝 y]
          (fun z ↦ f (s⁻¹ • z)) :=
        eventually_of_mem
          ((exteriorBall (EuclideanSpace ℝ (Fin n)) (s * e.radius)).isOpen.mem_nhds
            (mem_exteriorBall.2 hy))
          fun z hz ↦ openPullbackMetricCoeff_rescale m e hc (mem_exteriorBall.1 hz) i j
      obtain ⟨h0, h1, h2⟩ := hC (s⁻¹ • y) hsy i j
      -- Transfer the 0th-, 1st-, and 2nd-order bounds via `inv_pow_mul_rpow_smul`.
      refine ⟨?_, ?_, ?_⟩
      · rw [openPullbackMetricCoeff_rescale m e hc hy i j]
        have hrpow := inv_pow_mul_rpow_smul (C := C) (t := t) hs hy0 0
        simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, ← hnorm] at hrpow
        exact h0.trans_eq hrpow
      · rw [hev.fderiv_eq, fderiv_comp_smul (f := f) (x := y) s⁻¹]
        have hrpow := inv_pow_mul_rpow_smul (C := C) (t := t) hs hy0 1
        simp only [pow_one, Nat.cast_one, ← hnorm] at hrpow
        have hs' : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
        exact ((ContinuousLinearMap.opNorm_smul_le _ _).trans_eq
          (by rw [Real.norm_of_nonneg hs'])).trans
          ((mul_le_mul_of_nonneg_left h1 hs').trans_eq hrpow)
      · rw [hev.fderiv.fderiv_eq, fderiv_fderiv_comp_smul f s⁻¹ y]
        have hrpow := inv_pow_mul_rpow_smul (C := C) (t := t) hs hy0 2
        simp only [sq, Nat.cast_ofNat, ← hnorm] at hrpow
        have hs2 : 0 ≤ s⁻¹ * s⁻¹ := mul_nonneg (inv_nonneg.2 hs.le) (inv_nonneg.2 hs.le)
        exact ((ContinuousLinearMap.opNorm_smul_le _ _).trans_eq
          (by rw [Real.norm_of_nonneg hs2])).trans
          ((mul_le_mul_of_nonneg_left h2 hs2).trans_eq hrpow) }

@[simp]
theorem radius_rescale : (e.rescale m hc).radius = Real.sqrt c * e.radius := by rfl

/-- Pointwise evaluation of the rescaled end parametrization:
`(e.rescale m hc).toFun y = WithMetric.toWithMetric _ (e.toFun ((√c)⁻¹ • y))`. -/
@[simp]
theorem toFun_rescale (y : exteriorBall (EuclideanSpace ℝ (Fin n)) (e.rescale m hc).radius) :
    (e.rescale m hc).toFun y =
      WithMetric.toWithMetric (rescaledMetric I M m hc)
        (e.toFun ⟨(Real.sqrt c)⁻¹ • y.1, mem_exteriorBall.2 <| by
          have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), lt_inv_mul_iff₀ hs]
          simpa only [radius_rescale] using mem_exteriorBall.1 y.2⟩) := by
  dsimp only [rescale, Function.comp_apply]
  exact congrArg (WithMetric.toWithMetric (rescaledMetric I M m hc) ∘ e.toFun)
    (Subtype.ext (rescaleMapDomain_val hc y))

/-- The range of a rescaled end is the image of the original end's range under
`WithMetric.toWithMetric`. -/
@[simp]
theorem range_rescale :
    Set.range (e.rescale m hc).toFun =
      WithMetric.toWithMetric (rescaledMetric I M m hc) '' Set.range e.toFun := by
  dsimp only [rescale]
  have hsurj : Function.Surjective (rescaleMapDomain (n := n) (R := e.radius) hc) :=
    (rescaleMapDomain hc).surjective
  rw [Set.range_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- Under constant metric rescaling `g ↦ c • g`, the pulled-back metric coefficients satisfy
`(e.rescale m hc).metricCoeff y = e.metricCoeff ((√c)⁻¹ • y)` everywhere on `ℝⁿ`. -/
@[simp]
theorem metricCoeff_rescale (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    (e.rescale m hc).metricCoeff y i j = e.metricCoeff ((Real.sqrt c)⁻¹ • y) i j := by
  by_cases hy : y ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) (Real.sqrt c * e.radius)
  · rw [metricCoeff_eq_openPullbackMetricCoeff]
    exact openPullbackMetricCoeff_rescale m e hc (mem_exteriorBall.1 hy) i j
  · have hy' : y ∉ exteriorBall (EuclideanSpace ℝ (Fin n)) (e.rescale m hc).radius := by
      simpa only [radius_rescale] using hy
    have hsy' : (Real.sqrt c)⁻¹ • y ∉ exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius :=
      mt (mem_exteriorBall_inv_sqrt_smul_iff hc y).2 hy
    rw [(e.rescale m hc).metricCoeff_of_notMem hy', e.metricCoeff_of_notMem hsy']

/-- Under constant metric rescaling `g ↦ c • g`, the pulled-back metric matrix satisfies
`(e.rescale m hc).metricMatrix y = e.metricMatrix ((√c)⁻¹ • y)` everywhere on `ℝⁿ`. -/
@[simp]
theorem metricMatrix_rescale (y : EuclideanSpace ℝ (Fin n)) :
    (e.rescale m hc).metricMatrix y = e.metricMatrix ((Real.sqrt c)⁻¹ • y) := by
  ext i j; rw [metricMatrix_apply, metricMatrix_apply]; exact e.metricCoeff_rescale m hc y i j

end Rescale

end AsymptoticallyEuclideanEnd

end TauCeti

end
