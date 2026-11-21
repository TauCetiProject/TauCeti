/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Constant metric rescaling of asymptotically Euclidean ends

Multiplying a `C^m` Riemannian metric `g` on a `C¹` manifold `M` by a positive constant `c > 0`
turns an asymptotically Euclidean end `φ` of order `t` on `(closedBall 0 R)ᶜ` into an
asymptotically Euclidean end of the same order `t` on `WithMetric (rescaledMetric I M m hc)` with
excised radius `√c * R` and parametrization `y ↦ toWithMetric _ (φ ((√c)⁻¹ • y))`.

Rescaling `g` alone multiplies the asymptotic metric limit by `c` (sending `δ_ij` to `c δ_ij`), so
the compensating coordinate dilation `y ↦ (√c)⁻¹ • y` cancels `c` in the pulled-back metric
coefficients and restores the Euclidean limit `δ_ij`, yielding

`pullbackMetricCoeff I (fun z ↦ toWithMetric _ (φ ((√c)⁻¹ • z))) y =`
`  pullbackMetricCoeff I φ ((√c)⁻¹ • y)`

for every `y : EuclideanSpace ℝ (Fin n)`. Because an asymptotically Euclidean end already guarantees
`C²` regularity and second-order decay of `pullbackMetricCoeff I φ` on its exterior domain, and
smooth linear dilation preserves both properties, `IsAsymptoticallyEuclideanEnd.rescale` requires
no `2 ≤ m` assumption on the ambient metric.

## Main results

* `TauCeti.pullbackMetricCoeff_comp_smul`: precomposing with a nonzero scalar dilation scales
  `pullbackMetricCoeff` by `a ^ 2`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescaledMetric_comp`: postcomposing with
  `WithMetric.toWithMetric (rescaledMetric I M m hc)` scales `pullbackMetricCoeff` by `c`.
* `TauCeti.pullbackMetricCoeff_rescale`: the pulled-back metric coefficients of the rescaled
  parametrization equal `pullbackMetricCoeff I φ ((√c)⁻¹ • y)`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.rescale`: constant metric rescaling of an asymptotically
  Euclidean end.
-/

public section

noncomputable section

open Bundle Filter Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Helper: the manifold derivative of `y ↦ a • y` on a real normed space acts by `a • ·` under
`NormedSpace.fromTangentSpace`. -/
private theorem mfderiv_const_smul_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (x v : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y : F ↦ a • y) x ((NormedSpace.fromTangentSpace x).symm v) =
      a • (NormedSpace.fromTangentSpace (a • x)).symm v := by
  apply (NormedSpace.fromTangentSpace (a • x)).injective
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, ← mvfderiv_apply_eq_mfderiv_apply]
  change mvfderiv 𝓘(ℝ, F) (a • id) x _ = a • v
  simp [mvfderiv_const_smul_field, mvfderiv_eq_fderiv]

/-- Precomposing `φ : ℝⁿ → M` with a nonzero scalar dilation `y ↦ a • y` multiplies its
pulled-back metric coefficients at `x` by `a ^ 2`, evaluated at `a • x`. -/
theorem pullbackMetricCoeff_comp_smul (φ : EuclideanSpace ℝ (Fin n) → M) {a : ℝ} (ha : a ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (fun y ↦ φ (a • y)) x =
      a ^ 2 • pullbackMetricCoeff I φ (a • x) := by
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Units.mk0 a ha • ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))
  have hA : (⇑A.toDiffeomorph : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = (a • ·) :=
    funext fun y ↦ by simp [A]
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) I (fun y ↦ φ (a • y)) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        a • mfderiv (𝓡 n) I φ (a • x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    have hcomp := DFunLike.congr_fun
      (A.toDiffeomorph.mfderiv_comp_diffeomorph (K := I) (hn := by simp) (f := φ) (x := x))
      ((NormedSpace.fromTangentSpace x).symm (EuclideanSpace.basisFun (Fin n) ℝ k))
    change mfderiv (𝓡 n) I (φ ∘ ⇑A.toDiffeomorph) x _ =
      mfderiv (𝓡 n) I φ (⇑A.toDiffeomorph x) (mfderiv (𝓡 n) (𝓡 n) ⇑A.toDiffeomorph x _) at hcomp
    rw [hA, mfderiv_const_smul_apply, map_smul] at hcomp
    exact hcomp
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, pullbackMetricCoeff_apply, pullbackMetricCoeff_apply,
    hderiv i, hderiv j, real_inner_smul_left, real_inner_smul_right]
  ring

section Rescale

variable (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)] {c : ℝ} (hc : 0 < c)

/-- Postcomposing a map `ψ : ℝⁿ → M` with `WithMetric.toWithMetric (rescaledMetric I M m hc)`
multiplies its pulled-back metric coefficients by `c`. -/
theorem pullbackMetricCoeff_toWithMetric_rescaledMetric_comp
    (ψ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (WithMetric.toWithMetric (rescaledMetric I M m hc) ∘ ψ) x =
      c • pullbackMetricCoeff I ψ x := by
  set g_c := rescaledMetric I M m hc
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) I (WithMetric.toWithMetric g_c ∘ ψ) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        mfderiv I I (WithMetric.toWithMetric g_c) (ψ x)
          (mfderiv (𝓡 n) I ψ x (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    have h := (WithMetric.diffeomorph g_c ∞).symm.mfderiv_diffeomorph_comp (K := 𝓡 n)
      (hn := by simp) (f := ψ) (x := x)
    rw [WithMetric.coe_diffeomorph_symm] at h
    exact (DFunLike.congr_fun h _).trans (ContinuousLinearMap.comp_apply _ _ _)
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, pullbackMetricCoeff_apply, pullbackMetricCoeff_apply,
    hderiv i, hderiv j, WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
    WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric]
  exact (ContMDiffRiemannianMetric.rescaleConst_inner _ hc (ψ x) _ _).trans
    (congrArg (c * ·) (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner (ψ x) _ _))

/-- Under constant metric rescaling `g ↦ c • g` paired with the coordinate dilation
`y ↦ (√c)⁻¹ • y`, the pulled-back metric coefficients satisfy
`pullbackMetricCoeff I (toWithMetric _ ∘ φ ∘ ((√c)⁻¹ • ·)) y = pullbackMetricCoeff I φ ((√c)⁻¹ • y)`
everywhere on `ℝⁿ`. -/
theorem pullbackMetricCoeff_rescale (φ : EuclideanSpace ℝ (Fin n) → M)
    (y : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I
        (fun z ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ ((Real.sqrt c)⁻¹ • z))) y =
      pullbackMetricCoeff I φ ((Real.sqrt c)⁻¹ • y) := by
  set s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hcomp :
      (fun z ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ (s⁻¹ • z))) =
        fun z ↦ (WithMetric.toWithMetric (rescaledMetric I M m hc) ∘ φ) (s⁻¹ • z) := rfl
  rw [hcomp, pullbackMetricCoeff_comp_smul (I := I) _ (inv_ne_zero hs.ne') y,
    pullbackMetricCoeff_toWithMetric_rescaledMetric_comp m hc φ (s⁻¹ • y), smul_smul]
  have hcs : s⁻¹ ^ 2 * c = 1 := by
    rw [← Real.sq_sqrt hc.le, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]
  rw [hcs, one_smul]

end Rescale

namespace IsAsymptoticallyEuclideanEnd

/-- Dilation scaling identity for the `k`-th order decay bound under `y ↦ s⁻¹ • y`. -/
private theorem inv_pow_mul_rpow_smul {s r t C : ℝ} (hs : 0 < s) (hr : 0 < r) (k : ℕ) :
    C * (s⁻¹ * r) ^ (-t - k) * s⁻¹ ^ k = C * s ^ t * r ^ (-t - k) := by
  rw [Real.mul_rpow (inv_nonneg.2 hs.le) hr.le, Real.inv_rpow hs.le,
    Real.rpow_sub hs, Real.rpow_neg hs.le, Real.rpow_natCast, inv_div, div_inv_eq_mul, inv_pow]
  have hsk : s ^ k ≠ 0 := pow_ne_zero k hs.ne'
  field_simp [hs.ne', hsk]

/-- Membership in the dilated exterior ball is equivalent to membership of the scaled point in the
original exterior ball. -/
private theorem smul_mem_compl_closedBall_iff {R s : ℝ} (hs : 0 < s)
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R))ᶜ ↔
      s⁻¹ • y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
  simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  exact (lt_inv_mul_iff₀ hs).symm

/-- Precomposing a scalar function with `w ↦ a • w` (`a ≠ 0`) scales the norm of its `k`-th
iterated Fréchet derivative by at most `|a| ^ k`. -/
private theorem norm_iteratedFDeriv_comp_smul_le (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {a : ℝ} (ha : a ≠ 0) (y : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w ↦ f (a • w)) y‖ ≤ |a| ^ k * ‖iteratedFDeriv ℝ k f (a • y)‖ := by
  let g : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
  let s : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    a⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
  have hgs : Function.RightInverse s g := fun w ↦ by simp [g, s, smul_smul, ha]
  have hnorm_g : ‖g‖ ≤ |a| := (ContinuousLinearMap.opNorm_smul_le _ _).trans <| by
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg a) ContinuousLinearMap.norm_id_le
  have hle := g.norm_iteratedFDeriv_comp_right_le_of_rightInverse s hgs f y k
  exact hle.trans <| by
    rw [mul_comm (|a| ^ k)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hnorm_g k) (norm_nonneg _)

/-- Rescaling a `C^m` Riemannian metric by a positive constant `c` turns an asymptotically
Euclidean end `φ` of `M` of order `t` on `(closedBall 0 R)ᶜ` into an asymptotically Euclidean end
of `WithMetric (rescaledMetric I M m hc)` of order `t` on `(closedBall 0 (√c * R))ᶜ` with
parametrization `y ↦ toWithMetric _ (φ ((√c)⁻¹ • y))`. -/
theorem rescale (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M} {c : ℝ} (hc : 0 < c)
    (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    IsAsymptoticallyEuclideanEnd I t (Real.sqrt c * R)
      (fun y ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ ((Real.sqrt c)⁻¹ • y))) := by
  set g_c := rescaledMetric I M m hc
  set s : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Units.mk0 s⁻¹ (inv_ne_zero hs.ne') • ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))
  have hA_coe : (A.toDiffeomorph : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      (s⁻¹ • ·) := funext fun y ↦ by simp [A]
  have hmaps : MapsTo (s⁻¹ • ·)
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R))ᶜ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    fun y hy ↦ (smul_mem_compl_closedBall_iff hs y).1 hy
  have hcoeff_eq : ∀ y,
      pullbackMetricCoeff I (fun z ↦ WithMetric.toWithMetric g_c (φ (s⁻¹ • z))) y =
        pullbackMetricCoeff I φ (s⁻¹ • y) :=
    fun y ↦ pullbackMetricCoeff_rescale m hc φ y
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  refine
    { radius_pos := mul_pos hs h.radius_pos
      dim_pos := h.dim_pos
      contMDiffOn := by
        have h1 : ContMDiffOn (𝓡 n) I ∞ (WithMetric.toWithMetric g_c ∘ φ)
            (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
          WithMetric.contMDiff_toWithMetric.comp_contMDiffOn h.contMDiffOn
        exact h1.comp (contDiff_const_smul s⁻¹).contDiffOn.contMDiffOn hmaps
      injOn := fun x hx y hy hxy ↦ by
        have hxy' : φ (s⁻¹ • x) = φ (s⁻¹ • y) := WithMetric.toWithMetric_injective g_c hxy
        exact smul_right_injective _ (inv_ne_zero hs.ne')
          (h.injOn (hmaps hx) (hmaps hy) hxy')
      isInvertible_mfderiv := fun x hx ↦ ?_
      contDiffOn_pullbackMetricCoeff := fun i j ↦
        ((h.contDiffOn_pullbackMetricCoeff i j).comp
          (contDiff_const_smul s⁻¹).contDiffOn hmaps).congr
          fun y _ ↦ congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j) (hcoeff_eq y)
      exists_norm_iteratedFDeriv_le := ⟨max C 0 * s ^ t, fun k hk i j y hy ↦ ?_⟩ }
  · have hopen : IsOpen (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
      isClosed_closedBall.isOpen_compl
    have hφ : MDifferentiableAt (𝓡 n) I φ (A.toDiffeomorph x) := by
      rw [hA_coe]
      exact (h.contMDiffOn.contMDiffAt (hopen.mem_nhds (hmaps hx))).mdifferentiableAt (by simp)
    have hto : MDifferentiableAt I I (WithMetric.toWithMetric g_c) (φ (A.toDiffeomorph x)) :=
      (WithMetric.hasMFDerivAt_toWithMetric _).mdifferentiableAt
    have hsmul : MDifferentiableAt (𝓡 n) (𝓡 n) (⇑A.toDiffeomorph) x :=
      A.toDiffeomorph.contMDiff.mdifferentiableAt (by simp)
    have hfun_eq :
        (fun z ↦ WithMetric.toWithMetric g_c (φ (s⁻¹ • z))) =
          WithMetric.toWithMetric g_c ∘ φ ∘ ⇑A.toDiffeomorph := by
      funext z; change WithMetric.toWithMetric g_c (φ (s⁻¹ • z)) =
        WithMetric.toWithMetric g_c (φ (A.toDiffeomorph z))
      rw [hA_coe]
    rw [hfun_eq, mfderiv_comp x hto (hφ.comp x hsmul),
      mfderiv_comp x hφ hsmul, WithMetric.mfderiv_toWithMetric]
    refine ContinuousLinearMap.IsInvertible.comp ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
      ((h.isInvertible_mfderiv (A.toDiffeomorph x) (by rw [hA_coe]; exact hmaps hx)).comp
        (A.toDiffeomorph.isInvertible_mfderiv (by simp)))
  · have heq_fun :
        (fun w ↦ (pullbackMetricCoeff I (fun z ↦ WithMetric.toWithMetric g_c (φ (s⁻¹ • z))) w -
          1) i j) =
        fun w ↦ (pullbackMetricCoeff I φ (s⁻¹ • w) - 1) i j := by
      funext w; rw [hcoeff_eq w]
    rw [heq_fun]
    have hbound1 := norm_iteratedFDeriv_comp_smul_le
      (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) (inv_ne_zero hs.ne') y k
    rw [abs_of_nonneg (inv_nonneg.2 hs.le)] at hbound1
    have hnorm : ‖s⁻¹ • y‖ = s⁻¹ * ‖y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    have hy0 : 0 < ‖y‖ := (mul_pos hs h.radius_pos).trans (by simpa using hy)
    have hf_bound :
        ‖iteratedFDeriv ℝ k (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) (s⁻¹ • y)‖ ≤
          max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k) := by
      calc ‖iteratedFDeriv ℝ k (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) (s⁻¹ • y)‖
          ≤ C * ‖s⁻¹ • y‖ ^ (-t - k) := hC k hk i j (s⁻¹ • y) (hmaps hy)
        _ ≤ max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k) := by
            rw [hnorm]
            exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by positivity) _)
    calc ‖iteratedFDeriv ℝ k (fun w ↦ (pullbackMetricCoeff I φ (s⁻¹ • w) - 1) i j) y‖
        ≤ s⁻¹ ^ k *
            ‖iteratedFDeriv ℝ k (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) (s⁻¹ • y)‖ :=
          hbound1
      _ ≤ s⁻¹ ^ k * (max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k)) :=
          mul_le_mul_of_nonneg_left hf_bound (pow_nonneg (inv_nonneg.2 hs.le) k)
      _ = max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k) * s⁻¹ ^ k := by ring
      _ = max C 0 * s ^ t * ‖y‖ ^ (-t - k) := inv_pow_mul_rpow_smul hs hy0 k

end IsAsymptoticallyEuclideanEnd

end TauCeti

end
