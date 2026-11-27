/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Conformal
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Constant metric rescaling of asymptotically Euclidean ends

Multiplying a `C^m` Riemannian metric `g` on a `C¹` manifold `M` by a positive constant `c > 0`
(via `TauCeti.rescaledMetric`) turns an asymptotically Euclidean end `φ` of order `t` on
`(closedBall 0 R)ᶜ` into an asymptotically Euclidean end of the same order `t` on
`WithMetric (rescaledMetric I M m hc)` with excised radius `√c * R` and parametrization
`y ↦ toWithMetric _ (φ ((√c)⁻¹ • y))`.

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

## Main results

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
open scoped ContDiff Manifold Matrix Pointwise RealInnerProductSpace Topology

namespace TauCeti

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

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
        fun z ↦ (WithMetric.toWithMetric (rescaledMetric I M m hc) ∘ φ) (s⁻¹ • z) :=
    funext fun z ↦ by simp only [Function.comp_apply]
  rw [hcomp, pullbackMetricCoeff_comp_smul (I := I) _ s⁻¹ y,
    pullbackMetricCoeff_toWithMetric_rescaledMetric_comp m hc φ (s⁻¹ • y), smul_smul]
  have hcs : s⁻¹ ^ 2 * c = 1 := by
    rw [← Real.sq_sqrt hc.le, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]
  rw [hcs, one_smul]

end Rescale

namespace IsAsymptoticallyEuclideanEnd

/-- The inverse dilation `s⁻¹ • ·` (`0 < s`) maps `(closedBall 0 (s * R))ᶜ` into
`(closedBall 0 R)ᶜ`. -/
private theorem mapsTo_inv_smul_compl_closedBall {s R : ℝ} (hs : 0 < s) :
    MapsTo (s⁻¹ • ·) (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s * R))ᶜ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
  rw [mapsTo_iff_image_subset, image_smul, smul_compl_closedBall (inv_ne_zero hs.ne'),
    smul_zero, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_cancel_left₀ hs.ne']

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
  let A : EuclideanSpace ℝ (Fin n) ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ EuclideanSpace ℝ (Fin n) :=
    Diffeomorph.smulAdd ∞ s⁻¹ 0 (inv_ne_zero hs.ne')
  have hmaps : s⁻¹ • x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    mapsTo_inv_smul_compl_closedBall hs hx
  have hAx : A x = s⁻¹ • x := by simp [A]
  have hφ : MDifferentiableAt (𝓡 n) I φ (A x) :=
    (h.contMDiffOn.contMDiffAt
      (isClosed_closedBall.isOpen_compl.mem_nhds (hAx ▸ hmaps))).mdifferentiableAt (by simp)
  have hto : MDifferentiableAt I I (WithMetric.toWithMetric g_c) (φ (A x)) :=
    (WithMetric.hasMFDerivAt_toWithMetric _).mdifferentiableAt
  have hsmul : MDifferentiableAt (𝓡 n) (𝓡 n) (⇑A) x :=
    A.contMDiff.mdifferentiableAt (by simp)
  have hfun_eq :
      (fun z ↦ WithMetric.toWithMetric g_c (φ (s⁻¹ • z))) =
        WithMetric.toWithMetric g_c ∘ φ ∘ ⇑A :=
    funext fun z ↦ by simp only [Function.comp_apply, A, Diffeomorph.smulAdd_apply, add_zero]
  rw [hfun_eq, mfderiv_comp x hto (hφ.comp x hsmul), mfderiv_comp x hφ hsmul,
    WithMetric.mfderiv_toWithMetric]
  refine ContinuousLinearMap.IsInvertible.comp ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    ((h.isInvertible_mfderiv (A x) (hAx ▸ hmaps)).comp (A.isInvertible_mfderiv (by simp)))

/-- Transport of the `k`-th order metric decay bound under constant rescaling and dilation. -/
private theorem norm_iteratedFDeriv_rescale_le (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {t R C : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M} {c : ℝ} (hc : 0 < c)
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
    mapsTo_inv_smul_compl_closedBall hs hy
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
    _ = max C 0 * ((s⁻¹ * ‖y‖) ^ (-t - (k : ℝ)) * s⁻¹ ^ (k : ℝ)) := by
        rw [Real.rpow_natCast]; ring
    _ = max C 0 * s ^ t * ‖y‖ ^ (-t - k) := by
        rw [Real.mul_rpow_sub_mul_rpow (inv_pos.2 hs) (norm_nonneg y), Real.inv_rpow hs.le,
          Real.rpow_neg hs.le, inv_inv]
        ring

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
    mapsTo_inv_smul_compl_closedBall hs
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
        ⟨max C 0 * s ^ t, fun _ hk i j _ hy ↦
          norm_iteratedFDeriv_rescale_le m hc hC hk i j hy⟩ }

end IsAsymptoticallyEuclideanEnd

end TauCeti

end
