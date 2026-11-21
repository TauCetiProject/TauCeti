/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Rescale
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Exponential

/-!
# Behavior of the injectivity radius under isometries, metric rescaling, and on inner-product spaces

Smooth Riemannian isometries preserve normal domains, `inj(p)`, and `inj(M)`; consequently `inj`
is constant and strictly positive on nonempty homogeneous Riemannian manifolds. Multiplying a
smooth metric `g` by `c > 0` leaves `riemannianExp` unchanged while scaling tangent norms by `√c`,
multiplying both `inj(p)` and `inj(M)` by `ENNReal.ofReal √c` (proved in both `TauCeti.WithMetric`
and `letI` forms). Finally, every finite-dimensional real inner-product space has `inj = ⊤`.

## Main results

* `TauCeti.RiemannianIsometry.isNormalDomain_mfderiv_image`,
  `TauCeti.RiemannianIsometry.isNormalDomain_ball_iff`,
  `TauCeti.RiemannianIsometry.injectivityRadiusAt_apply`,
  `TauCeti.RiemannianIsometry.injectivityRadius_eq`: invariance under Riemannian isometries.
* `TauCeti.injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive`,
  `TauCeti.injectivityRadius_pos_of_isPretransitive`: constancy and positivity on homogeneous
  Riemannian manifolds.
* `TauCeti.WithMetric.injectivityRadiusAt_toWithMetric`,
  `TauCeti.WithMetric.injectivityRadius_eq`,
  `TauCeti.WithMetric.injectivityRadiusAt_congr`,
  `TauCeti.WithMetric.injectivityRadius_congr`: `WithMetric` transport and congruence.
* `TauCeti.WithMetric.isNormalDomain_ball_rescale_const_iff`,
  `TauCeti.WithMetric.injectivityRadiusAt_rescale_const`,
  `TauCeti.WithMetric.injectivityRadius_rescale_const`, and their `letI` counterparts in
  `Bundle.ContMDiffRiemannianMetric`: scaling by `√c` under `g ↦ c g`.
* `TauCeti.Manifold.injectivityRadiusAt_model_space`,
  `TauCeti.Manifold.injectivityRadius_model_space`: `inj = ⊤` on real inner-product spaces.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Definition 4.1.23, p. 151.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 5,
  6, and 10.
-/

public section

open Bundle Function Manifold Metric Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

/-! ### Invariance under smooth Riemannian isometries -/

namespace TauCeti.RiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- The differential of a smooth Riemannian isometry carries normal domains at `p` to normal domains
at `Φ p`. -/
theorem isNormalDomain_mfderiv_image (Φ : RiemannianIsometry I J M N) {p : M}
    {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U) :
    IsNormalDomain J N (Φ p) (mfderiv I J Φ p '' U) := by
  let L : TangentSpace I p ≃L[ℝ] TangentSpace J (Φ p) :=
    (Φ.mfderivToLinearIsometryEquiv p).toContinuousLinearEquiv
  have hL : ⇑L = mfderiv I J Φ p := funext (Φ.mfderivToLinearIsometryEquiv_apply p)
  have hexp : riemannianExp J N (Φ p) = (Φ ∘ riemannianExp I M p) ∘ L.symm := funext fun w ↦ by
    simp only [Function.comp_apply, ← Φ.riemannianExp_mfderiv p (L.symm w), ← hL,
      L.apply_symm_apply]
  refine ⟨hL ▸ L.toHomeomorph.isOpenMap U h.isOpen, ⟨0, h.zero_mem, map_zero _⟩,
    map_zero (mfderiv I J Φ p) ▸ h.starConvex.linear_image (mfderiv I J Φ p).toLinearMap,
    Φ.mfderiv_image_expDomain p ▸ image_mono h.subset_expDomain, ?_, ?_⟩
  · rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ heq
    rw [Φ.riemannianExp_mfderiv, Φ.riemannianExp_mfderiv] at heq
    exact congrArg (mfderiv I J Φ p) (h.injOn hv₁ hv₂ (EquivLike.injective Φ heq))
  · rintro ⟨_, v, hv, rfl⟩; rw [hexp]
    have hvL : L.symm (mfderiv I J Φ p v) = v := by rw [← hL, L.symm_apply_apply]
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace J (Φ p)) 𝓘(ℝ, TangentSpace I p) ∞ L.symm
        (mfderiv I J Φ p v) := by
      simpa only [ContinuousLinearEquiv.coe_toDiffeomorph] using
        L.symm.toDiffeomorph.isLocalDiffeomorph (mfderiv I J Φ p v)
    exact (h1.comp (hg := hvL.symm ▸ h.isLocalDiffeomorphOn ⟨v, hv⟩)).comp
      (hg := Φ.toDiffeomorph.isLocalDiffeomorph _)

/-- A smooth Riemannian isometry preserves whether an open tangent ball of radius `r` is a normal
domain. -/
theorem isNormalDomain_ball_iff (Φ : RiemannianIsometry I J M N) (p : M) (r : ℝ) :
    IsNormalDomain J N (Φ p) (Metric.ball 0 r) ↔ IsNormalDomain I M p (Metric.ball 0 r) := by
  refine ⟨fun h ↦ ?_, fun h ↦
    by simpa only [Φ.mfderiv_image_ball, map_zero] using Φ.isNormalDomain_mfderiv_image h⟩
  have : T2Space N := Φ.toDiffeomorph.toHomeomorph.t2Space
  have h' := Φ.symm.isNormalDomain_mfderiv_image h
  rw [Φ.symm.mfderiv_image_ball, map_zero] at h'; exact Φ.symm_apply_apply p ▸ h'

/-- **Isometry invariance of the pointwise injectivity radius.** -/
@[simp] theorem injectivityRadiusAt_apply (Φ : RiemannianIsometry I J M N) (p : M) :
    injectivityRadiusAt J N (Φ p) = injectivityRadiusAt I M p := by
  simp only [injectivityRadiusAt_def, Φ.isNormalDomain_ball_iff]

/-- **Isometry invariance of the global injectivity radius.** -/
theorem injectivityRadius_eq (Φ : RiemannianIsometry I J M N) :
    injectivityRadius J N = injectivityRadius I M := by
  rw [injectivityRadius_def, injectivityRadius_def, ← Φ.surjective.iInf_comp]
  exact iInf_congr fun p ↦ Φ.injectivityRadiusAt_apply p

end TauCeti.RiemannianIsometry

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- An element of a group acting smoothly by Riemannian isometries preserves the pointwise
injectivity radius. -/
theorem injectivityRadiusAt_smul {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
    (a : G) (ha : ∀ (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w) (x : M) :
    injectivityRadiusAt I M (a • x) = injectivityRadiusAt I M x := by
  simpa only [RiemannianIsometry.coe_constSMul] using
    (RiemannianIsometry.constSMul a ha).injectivityRadiusAt_apply x

/-- On a homogeneous Riemannian manifold (`MulAction.IsPretransitive (Isom I M) M`), the pointwise
injectivity radius is independent of the basepoint. -/
theorem injectivityRadiusAt_eq_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] (p q : M) :
    injectivityRadiusAt I M p = injectivityRadiusAt I M q :=
  let ⟨Φ, hΦ⟩ := MulAction.exists_smul_eq (Isom I M) q p
  hΦ ▸ Φ.injectivityRadiusAt_apply q

/-- On a homogeneous Riemannian manifold, the global injectivity radius equals the pointwise
injectivity radius at any point. -/
theorem injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] (p : M) :
    injectivityRadius I M = injectivityRadiusAt I M p :=
  le_antisymm (injectivityRadius_le p) (le_injectivityRadius_iff.2 fun q ↦
    (injectivityRadiusAt_eq_of_isPretransitive q p).ge)

/-- Every nonempty homogeneous Riemannian manifold (compact or noncompact) has strictly positive
global injectivity radius. -/
theorem injectivityRadius_pos_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] [Nonempty M] : 0 < injectivityRadius I M :=
  let ⟨p⟩ := ‹Nonempty M›
  injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive (I := I) p ▸
    injectivityRadiusAt_pos p

end TauCeti

/-! ### `WithMetric` transport and constant rescaling -/

namespace TauCeti.WithMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section RiemannianIsometry

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w)

include hg

/-- The pointwise injectivity radius on `WithMetric g` agrees with that on `M` when `M` carries the
inner product of `g`. -/
theorem injectivityRadiusAt_toWithMetric [I.Boundaryless] [T2Space M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (p : M) :
    injectivityRadiusAt I (WithMetric g) (toWithMetric g p) = injectivityRadiusAt I M p := by
  simpa only [riemannianIsometry_apply, ofWithMetric_toWithMetric] using
    ((riemannianIsometry g hg).injectivityRadiusAt_apply (toWithMetric g p)).symm

/-- The global injectivity radius on `WithMetric g` agrees with that on `M` when `M` carries the
inner product of `g`. -/
theorem injectivityRadius_eq [I.Boundaryless] [T2Space M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    injectivityRadius I (WithMetric g) = injectivityRadius I M :=
  (riemannianIsometry g hg).injectivityRadius_eq.symm

end RiemannianIsometry

section InnerEq

variable (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w)

include h

/-- Pointwise equal smooth Riemannian metrics have equal pointwise injectivity radius on their
`WithMetric` copies. -/
theorem injectivityRadiusAt_congr [I.Boundaryless] [T2Space M] (p : M) :
    injectivityRadiusAt I (WithMetric g₁) (toWithMetric g₁ p) =
      injectivityRadiusAt I (WithMetric g₂) (toWithMetric g₂ p) := by
  simpa only [riemannianIsometryOfInnerEq_apply, ofWithMetric_toWithMetric] using
    ((riemannianIsometryOfInnerEq g₁ g₂ h).injectivityRadiusAt_apply (toWithMetric g₁ p)).symm

/-- Pointwise equal smooth Riemannian metrics have equal global injectivity radius on their
`WithMetric` copies. -/
theorem injectivityRadius_congr [I.Boundaryless] [T2Space M] :
    injectivityRadius I (WithMetric g₁) = injectivityRadius I (WithMetric g₂) :=
  (riemannianIsometryOfInnerEq g₁ g₂ h).injectivityRadius_eq.symm

end InnerEq

section Rescale

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  [I.Boundaryless] [T2Space M]

/-- Forward implication for normal tangent balls under constant rescaling of `g` by `c > 0`. -/
private theorem isNormalDomain_ball_rescale_const_of_div {c : ℝ} (hc : 0 < c) {p : M} {r : ℝ}
    (h : IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c))) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
      (toWithMetric _ p) (Metric.ball 0 r) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set p₀ : WithMetric g := toWithMetric g p
  set p_c : WithMetric g_c := toWithMetric g_c p
  have hsqrt : 0 < √c := Real.sqrt_pos.2 hc
  have hr : 0 < r := (mul_pos (by simpa only [Metric.mem_ball, dist_self] using h.zero_mem)
    hsqrt).trans_eq (div_mul_cancel₀ _ hsqrt.ne')
  let L : TangentSpace I p_c ≃L[ℝ] TangentSpace I p₀ :=
    (diffeomorphWithMetric g_c g ∞).mfderivToContinuousLinearEquiv (by simp) p_c
  have hL_of (v : TangentSpace I p_c) :
      mfderiv I I ofWithMetric p₀ (L v) = mfderiv I I ofWithMetric p_c v := by
    rw [mfderiv_ofWithMetric_apply, mfderiv_ofWithMetric_apply]
    exact DFunLike.congr_fun ((Diffeomorph.mfderivToContinuousLinearEquiv_coe _ (by simp)).trans
      (mfderiv_diffeomorphWithMetric g ∞ p_c)) v
  have hL_mem {v : TangentSpace I p_c} (hv : v ∈ Metric.ball 0 r) : L v ∈ Metric.ball 0 (r / √c) :=
    mem_ball_zero_iff.2 <| (lt_div_iff₀ hsqrt).2 <| by
      have hnorm : ‖v‖ = √c * ‖L v‖ := (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 <| by
        rw [mul_pow, Real.sq_sqrt hc.le, ← real_inner_self_eq_norm_sq,
          ← real_inner_self_eq_norm_sq, inner_def, inner_def, hL_of,
          ContMDiffRiemannianMetric.rescale_inner]
      linarith [mem_ball_zero_iff.1 hv]
  have hexp (v : TangentSpace I p_c) : riemannianExp I (WithMetric g_c) p_c v =
      diffeomorphWithMetric g g_c ∞ (riemannianExp I (WithMetric g) p₀ (L v)) :=
    ofWithMetric_injective <| by
      simp only [diffeomorphWithMetric_apply, ofWithMetric_toWithMetric]
      rw [ofWithMetric_riemannianExp_toWithMetric g_c p v,
        ofWithMetric_riemannianExp_toWithMetric g p (L v), hL_of, g.riemannianExp_rescale_const hc]
  refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball (0 : TangentSpace I p_c) r).starConvex (Metric.mem_ball_self hr), fun v hv ↦ ?_,
    fun v₁ hv₁ v₂ hv₂ heq ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · rw [mem_expDomain_toWithMetric_iff g_c, ← hL_of, g.expDomain_rescale_const hc p,
      ← mem_expDomain_toWithMetric_iff g]; exact h.subset_expDomain (hL_mem hv)
  · rw [hexp, hexp] at heq
    exact L.injective (h.injOn (hL_mem hv₁) (hL_mem hv₂) (EquivLike.injective _ heq))
  · rw [funext hexp]
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p_c) 𝓘(ℝ, TangentSpace I p₀) ∞ L v := by
      simpa only [ContinuousLinearEquiv.coe_toDiffeomorph] using
        L.toDiffeomorph.isLocalDiffeomorph v
    exact (h1.comp (hg := h.isLocalDiffeomorphOn ⟨L v, hL_mem hv⟩)).comp
      (hg := (diffeomorphWithMetric g g_c ∞).isLocalDiffeomorph _)

/-- **Normal tangent balls under constant metric rescaling.** Multiplying `g` by `c > 0` scales the
radius of normal tangent balls by `√c`. -/
theorem isNormalDomain_ball_rescale_const_iff {c : ℝ} (hc : 0 < c) (p : M) (r : ℝ) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (toWithMetric _ p) (Metric.ball 0 r) ↔
      IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c)) := by
  refine ⟨fun h ↦ ?_, isNormalDomain_ball_rescale_const_of_div g hc⟩
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set g' := g_c.rescale (fun _ ↦ c⁻¹) contMDiff_const fun _ ↦ inv_pos.2 hc
  have hr_eq : (r / √c) / √c⁻¹ = r := by
    rw [Real.sqrt_inv, div_inv_eq_mul, div_mul_cancel₀ _ (Real.sqrt_pos.2 hc).ne']
  let Ψ := riemannianIsometryOfInnerEq g' g fun x v w ↦ by simp [g', g_c, inv_mul_cancel₀ hc.ne']
  exact (riemannianIsometryOfInnerEq_apply g' g _ (toWithMetric g' p) : Ψ _ = _) ▸
    (Ψ.isNormalDomain_ball_iff (toWithMetric g' p) (r / √c)).2
      (isNormalDomain_ball_rescale_const_of_div g_c (inv_pos.2 hc) (hr_eq.symm ▸ h))

/-- **Scaling of the pointwise injectivity radius (`WithMetric` form).** Multiplying a smooth
Riemannian metric `g` by a positive constant `c` multiplies `inj(p)` by `ENNReal.ofReal √c`. -/
@[simp] theorem injectivityRadiusAt_rescale_const {c : ℝ} (hc : 0 < c) (p : M) :
    injectivityRadiusAt I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (toWithMetric _ p) =
      ENNReal.ofReal √c * injectivityRadiusAt I (WithMetric g) (toWithMetric g p) := by
  have hsqrt : 0 < √c := Real.sqrt_pos.2 hc
  refine le_antisymm ?_ ?_
  · rw [injectivityRadiusAt_def]; refine iSup₂_le fun r hr ↦ ?_
    have hr_eq : ENNReal.ofReal r = ENNReal.ofReal √c * ENNReal.ofReal (r / √c) := by
      rw [← ENNReal.ofReal_mul hsqrt.le, mul_div_cancel₀ _ hsqrt.ne']
    exact hr_eq ▸ mul_le_mul_of_nonneg_left
      ((isNormalDomain_ball_rescale_const_iff g hc p r).1 hr).ofReal_le_injectivityRadiusAt zero_le
  · rw [injectivityRadiusAt_def, ENNReal.mul_iSup]; simp_rw [ENNReal.mul_iSup]
    refine iSup₂_le fun s hs ↦ ?_; rw [← ENNReal.ofReal_mul hsqrt.le]
    exact ((isNormalDomain_ball_rescale_const_iff g hc p (√c * s)).2
      (by rwa [mul_div_cancel_left₀ s hsqrt.ne'])).ofReal_le_injectivityRadiusAt

/-- **Scaling of the global injectivity radius (`WithMetric` form).** Multiplying a smooth
Riemannian metric `g` by a positive constant `c` multiplies `inj(M)` by `ENNReal.ofReal √c`. -/
@[simp] theorem injectivityRadius_rescale_const {c : ℝ} (hc : 0 < c) :
    injectivityRadius I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)) =
      ENNReal.ofReal √c * injectivityRadius I (WithMetric g) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  rw [injectivityRadius_def, injectivityRadius_def, ← (equiv g_c).symm.surjective.iInf_comp,
    ← (equiv g).symm.surjective.iInf_comp,
    ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne' ENNReal.ofReal_ne_top]
  exact iInf_congr fun p ↦ by
    simpa only [equiv_symm_apply] using injectivityRadiusAt_rescale_const g hc p

end Rescale

end TauCeti.WithMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Scaling of the pointwise injectivity radius under constant rescaling (`letI` form).** -/
theorem injectivityRadiusAt_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (p : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle _;
      injectivityRadiusAt I M p) =
    ENNReal.ofReal √c *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
          Bundle.instIsContMDiffRiemannianBundle g;
        injectivityRadiusAt I M p) := by
  have h (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
      (letI : RiemannianBundle _ := ⟨g₀.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g₀;
        injectivityRadiusAt I M p) =
      injectivityRadiusAt I (TauCeti.WithMetric g₀) (TauCeti.WithMetric.toWithMetric g₀ p) :=
    let _ : RiemannianBundle _ := ⟨g₀.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g₀
    (TauCeti.WithMetric.injectivityRadiusAt_toWithMetric g₀ (fun _ _ _ ↦ rfl) p).symm
  rw [h _, h g, TauCeti.WithMetric.injectivityRadiusAt_rescale_const g hc p]

/-- **Scaling of the global injectivity radius under constant rescaling (`letI` form).** -/
theorem injectivityRadius_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle _;
      injectivityRadius I M) =
    ENNReal.ofReal √c *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
          Bundle.instIsContMDiffRiemannianBundle g;
        injectivityRadius I M) := by
  have h (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
      (letI : RiemannianBundle _ := ⟨g₀.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g₀;
        injectivityRadius I M) = injectivityRadius I (TauCeti.WithMetric g₀) :=
    let _ : RiemannianBundle _ := ⟨g₀.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g₀
    (TauCeti.WithMetric.injectivityRadius_eq g₀ fun _ _ _ ↦ rfl).symm
  rw [h _, h g, TauCeti.WithMetric.injectivityRadius_rescale_const g hc]

end Bundle.ContMDiffRiemannianMetric

/-! ### Finite-dimensional inner-product spaces -/

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every point of a finite-dimensional real inner-product space has infinite injectivity radius. -/
@[simp] theorem injectivityRadiusAt_model_space (p : F) : injectivityRadiusAt 𝓘(ℝ, F) F p = ⊤ :=
  injectivityRadiusAt_eq_top_iff_isNormalDomain_univ.2
    (isNormalDomain_model_space p isOpen_univ (mem_univ 0) (starConvex_univ 0))

/-- A finite-dimensional real inner-product space has infinite global injectivity radius. -/
@[simp] theorem injectivityRadius_model_space : injectivityRadius 𝓘(ℝ, F) F = ⊤ := by
  simp [injectivityRadius_def]

end TauCeti.Manifold

end
