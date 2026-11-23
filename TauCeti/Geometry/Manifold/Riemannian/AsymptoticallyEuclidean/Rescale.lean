/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Constant metric rescaling of asymptotically Euclidean ends

Multiplying a `C^m` Riemannian metric `g` on a `C¹` manifold `M` by a positive constant `c > 0`
turns an asymptotically Euclidean end `φ` of order `t` on `(closedBall 0 R)ᶜ` into an
asymptotically Euclidean end of the same order `t` on `WithMetric (rescaledMetric I M m hc)` with
excised radius `√c * R` and parametrization `y ↦ toWithMetric _ (φ ((√c)⁻¹ • y))`.

For arbitrary `t : ℝ`, the compensating coordinate dilation `y ↦ (√c)⁻¹ • y` cancels the factor
`c` in the pulled-back metric coefficients, yielding the exact identity

`pullbackMetricCoeff I (fun z ↦ toWithMetric _ (φ ((√c)⁻¹ • z))) y =`
`  pullbackMetricCoeff I φ ((√c)⁻¹ • y)`

for every `y : EuclideanSpace ℝ (Fin n)`, and preserving `IsAsymptoticallyEuclideanEnd` of the same
order `t`. In particular, when `0 < t` (so that the pulled-back metric coefficients converge to
`δ_ij`), rescaling `g` alone multiplies the asymptotic metric limit by `c` (sending `δ_ij` to
`c δ_ij`), and the compensating coordinate dilation restores the Euclidean limit `δ_ij`. Because an
asymptotically Euclidean end already guarantees `C²` regularity and second-order decay of
`pullbackMetricCoeff I φ` on its exterior domain, and smooth linear dilation preserves both
properties, `IsAsymptoticallyEuclideanEnd.rescale` requires no `2 ≤ m` assumption on the ambient
metric.

## Main definitions

* `TauCeti.rescaledMetric`: constant rescaling `c • g` (`0 < c`) of the ambient `C^m` Riemannian
  metric on the tangent bundle of a `C¹` manifold.

## Main results

* `TauCeti.rescaledMetric_inner`: the fibrewise inner product of `rescaledMetric` scales by `c`.
* `TauCeti.pullbackMetricCoeff_comp_smul`: precomposing with a scalar dilation scales
  `pullbackMetricCoeff` by `a ^ 2`.
* `TauCeti.pullbackMetricCoeff_toWithMetric_rescaledMetric_comp`: postcomposing with
  `WithMetric.toWithMetric (rescaledMetric I M m hc)` scales `pullbackMetricCoeff` by `c`.
* `TauCeti.pullbackMetricCoeff_rescale`: the pulled-back metric coefficients of the rescaled
  parametrization equal `pullbackMetricCoeff I φ ((√c)⁻¹ • y)`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.smul_mem_compl_closedBall_iff` and
  `TauCeti.IsAsymptoticallyEuclideanEnd.image_inv_smul_compl_closedBall`: coordinate dilation
  between exterior balls.
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

/-- The constant rescaling `c • g` (`0 < c`) of the ambient `C^m` Riemannian metric on the tangent
bundle of a `C¹` manifold `M`. -/
def rescaledMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (m : ℕ∞ω)
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ} (hc : 0 < c) :
    ContMDiffRiemannianMetric I m E (fun x : M ↦ TangentSpace I x) :=
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := m)
    (F := E) (V := fun x : M ↦ TangentSpace I x)).rescale (fun _ ↦ c) contMDiff_const
      (fun _ ↦ hc)

/-- The fibrewise inner product of `rescaledMetric` is `c` times the ambient inner product. -/
@[simp]
theorem rescaledMetric_inner {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {m : ℕ∞ω}
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ} (hc : 0 < c) (x : M) (v w : TangentSpace I x) :
    (rescaledMetric I M m hc).inner x v w = c * ⟪v, w⟫ := by
  rw [rescaledMetric, ContMDiffRiemannianMetric.rescale_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]; rfl

/-- Helper: scalar dilation `y ↦ a • y` on `EuclideanSpace ℝ (Fin n)` as a smooth diffeomorphism
for `a ≠ 0`. -/
private def smulDiffeomorph (n : ℕ) {a : ℝ} (ha : a ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ EuclideanSpace ℝ (Fin n) :=
  (Units.mk0 a ha • ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).toDiffeomorph

/-- Helper: the underlying function of `smulDiffeomorph n ha` is `a • ·`. -/
private theorem coe_smulDiffeomorph (n : ℕ) {a : ℝ} (ha : a ≠ 0) :
    (⇑(smulDiffeomorph n ha) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = (a • ·) :=
  funext fun y ↦ by simp [smulDiffeomorph]

/-- Precomposing `φ : ℝⁿ → M` with a scalar dilation `y ↦ a • y` multiplies its pulled-back metric
coefficients at `x` by `a ^ 2`, evaluated at `a • x`. -/
theorem pullbackMetricCoeff_comp_smul (φ : EuclideanSpace ℝ (Fin n) → M) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I (fun y ↦ φ (a • y)) x =
      a ^ 2 • pullbackMetricCoeff I φ (a • x) := by
  by_cases ha : a = 0
  · subst ha
    have h0 : (fun y : EuclideanSpace ℝ (Fin n) ↦ φ ((0 : ℝ) • y)) =
        fun _ ↦ φ ((0 : ℝ) • x) :=
      funext fun _ ↦ by rw [zero_smul, zero_smul]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, zero_pow two_ne_zero, zero_mul, pullbackMetricCoeff_apply,
      h0, mfderiv_const]
    -- The tangent space of `EuclideanSpace ℝ (Fin n)` is definitionally the model space itself,
    -- so `zero_apply` applies only after viewing the basis vector as a tangent vector via
    -- `fromTangentSpace`.
    rw [← NormedSpace.fromTangentSpace_symm_apply x (EuclideanSpace.basisFun (Fin n) ℝ i),
      ← NormedSpace.fromTangentSpace_symm_apply x (EuclideanSpace.basisFun (Fin n) ℝ j),
      zero_apply, zero_apply, inner_zero_left]
  · let A := smulDiffeomorph n ha
    have hfun : (fun y : EuclideanSpace ℝ (Fin n) ↦ φ (a • y)) = φ ∘ ⇑A := by
      rw [coe_smulDiffeomorph]; rfl
    have hderiv (k : Fin n) :
        mfderiv (𝓡 n) I (fun y ↦ φ (a • y)) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
          a • mfderiv (𝓡 n) I φ (a • x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      have hcomp := DFunLike.congr_fun
        (A.mfderiv_comp_diffeomorph (K := I) (hn := by simp) (f := φ) (x := x))
        ((NormedSpace.fromTangentSpace x).symm (EuclideanSpace.basisFun (Fin n) ℝ k))
      rw [ContinuousLinearMap.comp_apply, ← hfun, coe_smulDiffeomorph] at hcomp
      rw [mfderiv_const_smul_apply, map_smul] at hcomp
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
  exact rescaledMetric_inner hc (ψ x) _ _

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
  rw [hcomp, pullbackMetricCoeff_comp_smul (I := I) _ s⁻¹ y,
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
theorem smul_mem_compl_closedBall_iff {R s : ℝ} (hs : 0 < s)
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R))ᶜ ↔
      s⁻¹ • y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
  simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  exact (lt_inv_mul_iff₀ hs).symm

/-- Scaling by `s⁻¹` (`0 < s`) maps the exterior of `closedBall 0 (s * R)` onto the exterior of
`closedBall 0 R`. -/
theorem image_inv_smul_compl_closedBall {R s : ℝ} (hs : 0 < s) :
    (s⁻¹ • ·) '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R))ᶜ =
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
  ext z
  rw [mem_image]
  refine ⟨?_, fun hz ↦ ⟨s • z, ?_, by simp [smul_smul, hs.ne']⟩⟩
  · rintro ⟨w, hw, rfl⟩
    exact (smul_mem_compl_closedBall_iff hs w).1 hw
  · exact (smul_mem_compl_closedBall_iff hs (s • z)).2 (by simpa [smul_smul, hs.ne'] using hz)

/-- Invertibility of `mfderiv` of `z ↦ toWithMetric (rescaledMetric I M m hc) (φ (s⁻¹ • z))` on the
dilated exterior ball. -/
private theorem isInvertible_mfderiv_rescale (m : ℕ∞ω) [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M} {c : ℝ} (hc : 0 < c)
    (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt c * R))ᶜ) :
    (mfderiv (𝓡 n) I
      (fun y ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ ((Real.sqrt c)⁻¹ • y)))
      x).IsInvertible := by
  set g_c := rescaledMetric I M m hc
  set s : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  let A := smulDiffeomorph n (inv_ne_zero hs.ne')
  have hmaps : s⁻¹ • x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    (smul_mem_compl_closedBall_iff hs x).1 hx
  have hφ : MDifferentiableAt (𝓡 n) I φ (A x) := by
    rw [coe_smulDiffeomorph]
    exact (h.contMDiffOn.contMDiffAt
      (isClosed_closedBall.isOpen_compl.mem_nhds hmaps)).mdifferentiableAt (by simp)
  have hto : MDifferentiableAt I I (WithMetric.toWithMetric g_c) (φ (A x)) :=
    (WithMetric.hasMFDerivAt_toWithMetric _).mdifferentiableAt
  have hsmul : MDifferentiableAt (𝓡 n) (𝓡 n) (⇑A) x :=
    A.contMDiff.mdifferentiableAt (by simp)
  have hfun_eq :
      (fun z ↦ WithMetric.toWithMetric g_c (φ (s⁻¹ • z))) =
        WithMetric.toWithMetric g_c ∘ φ ∘ ⇑A := by
    rw [coe_smulDiffeomorph]; rfl
  rw [hfun_eq, mfderiv_comp x hto (hφ.comp x hsmul), mfderiv_comp x hφ hsmul,
    WithMetric.mfderiv_toWithMetric]
  refine ContinuousLinearMap.IsInvertible.comp ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    ((h.isInvertible_mfderiv (A x) (by rw [coe_smulDiffeomorph]; exact hmaps)).comp
      (A.isInvertible_mfderiv (by simp)))

/-- Transport of the `k`-th order metric decay bound under constant rescaling and dilation. -/
private theorem norm_iteratedFDeriv_rescale_le (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {t R C : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M} {c : ℝ} (hc : 0 < c)
    (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (hC : ∀ k ≤ 2, ∀ (i j : Fin n), ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ,
      ‖iteratedFDeriv ℝ k (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) x‖ ≤ C * ‖x‖ ^ (-t - k))
    {k : ℕ} (hk : k ≤ 2) (i j : Fin n) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt c * R))ᶜ) :
    ‖iteratedFDeriv ℝ k
      (fun w ↦ (pullbackMetricCoeff I
        (fun z ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ ((Real.sqrt c)⁻¹ • z))) w -
        1) i j) y‖ ≤
      max C 0 * Real.sqrt c ^ t * ‖y‖ ^ (-t - k) := by
  set s : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hmaps : s⁻¹ • y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    (smul_mem_compl_closedBall_iff hs y).1 hy
  have heq_fun :
      (fun w ↦ (pullbackMetricCoeff I
        (fun z ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ (s⁻¹ • z))) w - 1) i j) =
      fun w ↦ (pullbackMetricCoeff I φ (s⁻¹ • w) - 1) i j :=
    funext fun w ↦ by rw [pullbackMetricCoeff_rescale m hc φ w]
  rw [heq_fun, norm_iteratedFDeriv_comp_const_smul
    (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) s⁻¹ y k, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 hs.le)]
  have hnorm : ‖s⁻¹ • y‖ = s⁻¹ * ‖y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  have hy0 : 0 < ‖y‖ := (mul_pos hs h.radius_pos).trans (by simpa using hy)
  have hf_bound :
      ‖iteratedFDeriv ℝ k (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) (s⁻¹ • y)‖ ≤
        max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k) :=
    (hC k hk i j (s⁻¹ • y) hmaps).trans <| by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by positivity) _)
  calc s⁻¹ ^ k *
        ‖iteratedFDeriv ℝ k (fun w ↦ (pullbackMetricCoeff I φ w - 1) i j) (s⁻¹ • y)‖
      ≤ s⁻¹ ^ k * (max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k)) :=
        mul_le_mul_of_nonneg_left hf_bound (pow_nonneg (inv_nonneg.2 hs.le) k)
    _ = max C 0 * (s⁻¹ * ‖y‖) ^ (-t - k) * s⁻¹ ^ k := by ring
    _ = max C 0 * s ^ t * ‖y‖ ^ (-t - k) := inv_pow_mul_rpow_smul hs hy0 k

/-- Rescaling a `C^m` Riemannian metric by a positive constant `c` turns an asymptotically
Euclidean end `φ` of `M` of order `t` on `(closedBall 0 R)ᶜ` into an asymptotically Euclidean end
of `WithMetric (rescaledMetric I M m hc)` of order `t` on `(closedBall 0 (√c * R))ᶜ` with
parametrization `y ↦ toWithMetric _ (φ ((√c)⁻¹ • y))`. -/
theorem rescale (m : ℕ∞ω) [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M} {c : ℝ} (hc : 0 < c)
    (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    let _ := h.finiteDimensional
    IsAsymptoticallyEuclideanEnd I t (Real.sqrt c * R)
      (fun y ↦ WithMetric.toWithMetric (rescaledMetric I M m hc) (φ ((Real.sqrt c)⁻¹ • y))) := by
  have : FiniteDimensional ℝ E := h.finiteDimensional
  set g_c := rescaledMetric I M m hc
  set s : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hmaps : MapsTo (s⁻¹ • ·)
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R))ᶜ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    fun y hy ↦ (smul_mem_compl_closedBall_iff hs y).1 hy
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  -- Assemble the end conditions by transporting smoothness, injectivity, invertible differential,
  -- `C²` regularity, and decay bounds along the dilation `s⁻¹ • ·`.
  refine
    { radius_pos := mul_pos hs h.radius_pos
      dim_pos := h.dim_pos
      contMDiffOn :=
        (WithMetric.contMDiff_toWithMetric.comp_contMDiffOn h.contMDiffOn).comp
          (contDiff_const_smul s⁻¹).contDiffOn.contMDiffOn hmaps
      injOn := fun x hx y hy hxy ↦
        smul_right_injective _ (inv_ne_zero hs.ne')
          (h.injOn (hmaps hx) (hmaps hy) (WithMetric.toWithMetric_injective g_c hxy))
      isInvertible_mfderiv := fun _ hx ↦ h.isInvertible_mfderiv_rescale m hc hx
      contDiffOn_pullbackMetricCoeff := fun i j ↦
        ((h.contDiffOn_pullbackMetricCoeff i j).comp
          (contDiff_const_smul s⁻¹).contDiffOn hmaps).congr
          fun y _ ↦ congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j)
            (pullbackMetricCoeff_rescale m hc φ y)
      exists_norm_iteratedFDeriv_le :=
        ⟨max C 0 * s ^ t, fun _ hk i j _ hy ↦ h.norm_iteratedFDeriv_rescale_le m hc hC hk i j hy⟩ }

end IsAsymptoticallyEuclideanEnd

end TauCeti

end
