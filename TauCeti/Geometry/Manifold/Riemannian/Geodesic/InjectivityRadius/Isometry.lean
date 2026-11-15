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
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic

/-!
# Behavior of the injectivity radius under isometries, metric rescaling, and on inner-product spaces

A smooth Riemannian isometry `Φ : M → N` intertwines the exponential maps (`Φ ∘ exp_p = exp_{Φ p} ∘
dΦ_p`) while its differential `dΦ_p : T_p M ≃ₗᵢ[ℝ] T_{Φ p} N` maps open tangent balls of radius `r`
onto open tangent balls of radius `r`. Consequently `Φ` preserves normal domains, the pointwise
injectivity radius (`inj(Φ p) = inj(p)`), and the global injectivity radius (`inj(N) = inj(M)`). In
particular, on a homogeneous Riemannian manifold (`MulAction.IsPretransitive (Isom I M) M`), the
pointwise injectivity radius is constant, equals `inj(M)`, and is strictly positive whenever `M` is
nonempty.

When a smooth Riemannian metric `g` is multiplied by a positive constant `c`, the Levi-Civita
connection and exponential map are unchanged (`riemannianExp_rescale_const`), whereas tangent norms
scale by `√c`. Hence open tangent balls of radius `r` for `c • g` correspond to open tangent balls
of radius `r / √c` for `g`, and both `inj(p)` and `inj(M)` scale by `ENNReal.ofReal √c`. We provide
both the carrier-separated `TauCeti.WithMetric` formulations and the `letI` formulations on `M`.

Finally, on any finite-dimensional real inner-product space `F` (including dimension zero), the
exponential map at `p` is translation by `p` on all of `T_p F`, so every point has infinite
injectivity radius and `inj(F) = ⊤`.

## Main results

* `TauCeti.RiemannianIsometry.isNormalDomain_mfderiv_image`,
  `TauCeti.RiemannianIsometry.isNormalDomain_ball_iff`: Riemannian isometries preserve normal
  domains and normal tangent balls.
* `TauCeti.RiemannianIsometry.injectivityRadiusAt_apply`,
  `TauCeti.RiemannianIsometry.injectivityRadius_eq`: isometry invariance of `inj(p)` and `inj(M)`.
* `TauCeti.injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive`,
  `TauCeti.injectivityRadius_pos_of_isPretransitive`: constancy and positivity of `inj(M)` on
  homogeneous Riemannian manifolds (`MulAction.IsPretransitive (Isom I M) M`).
* `TauCeti.WithMetric.riemannianIsometry`, `TauCeti.WithMetric.riemannianIsometryOfInnerEq`,
  `TauCeti.WithMetric.injectivityRadiusAt_congr`, `TauCeti.WithMetric.injectivityRadius_congr`:
  tautological `RiemannianIsometry` for `WithMetric` and invariance under pointwise equal metrics.
* `TauCeti.WithMetric.isNormalDomain_ball_rescale_const_iff`,
  `TauCeti.WithMetric.injectivityRadiusAt_rescale_const`,
  `TauCeti.WithMetric.injectivityRadius_rescale_const`, and their `letI` counterparts in
  `Bundle.ContMDiffRiemannianMetric`: scaling by `√c` under constant metric rescaling `c • g`.
* `TauCeti.Manifold.injectivityRadiusAt_model_space`,
  `TauCeti.Manifold.injectivityRadius_model_space`: `inj(p) = ⊤` and `inj(F) = ⊤` on a
  finite-dimensional real inner-product space `F`.

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
  have hL : ⇑L = mfderiv I J Φ p := by
    ext v
    exact Φ.mfderivToLinearIsometryEquiv_apply p v
  have hexp : riemannianExp J N (Φ p) = (Φ ∘ riemannianExp I M p) ∘ L.symm := by
    ext w
    simp only [Function.comp_apply, ← Φ.riemannianExp_mfderiv p (L.symm w), ← hL,
      L.apply_symm_apply]
  refine
    { isOpen := hL ▸ L.toHomeomorph.isOpenMap U h.isOpen
      zero_mem := ⟨0, h.zero_mem, map_zero _⟩
      starConvex := map_zero (mfderiv I J Φ p) ▸
        h.starConvex.linear_image (mfderiv I J Φ p).toLinearMap
      subset_expDomain := Φ.mfderiv_image_expDomain p ▸ image_mono h.subset_expDomain
      injOn := ?_
      isLocalDiffeomorphOn := ?_ }
  · rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ heq
    rw [Φ.riemannianExp_mfderiv, Φ.riemannianExp_mfderiv] at heq
    exact congrArg (mfderiv I J Φ p) (h.injOn hv₁ hv₂ (EquivLike.injective Φ heq))
  · rintro ⟨w, v, hv, rfl⟩
    rw [hexp]
    have hvL : L.symm (mfderiv I J Φ p v) = v := by
      rw [← hL, L.symm_apply_apply]
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace J (Φ p)) 𝓘(ℝ, TangentSpace I p) ∞ L.symm
        (mfderiv I J Φ p v) := by
      simpa only [ContinuousLinearEquiv.coe_toDiffeomorph] using
        L.symm.toDiffeomorph.isLocalDiffeomorph (mfderiv I J Φ p v)
    have h2 : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
        (L.symm (mfderiv I J Φ p v)) :=
      hvL.symm ▸ h.isLocalDiffeomorphOn ⟨v, hv⟩
    have h3 : IsLocalDiffeomorphAt I J ∞ Φ
        (riemannianExp I M p (L.symm (mfderiv I J Φ p v))) :=
      Φ.toDiffeomorph.isLocalDiffeomorph _
    exact (h1.comp (hg := h2)).comp (hg := h3)

/-- A smooth Riemannian isometry preserves whether an open tangent ball of radius `r` is a normal
domain. -/
theorem isNormalDomain_ball_iff (Φ : RiemannianIsometry I J M N) (p : M) (r : ℝ) :
    IsNormalDomain J N (Φ p) (Metric.ball 0 r) ↔ IsNormalDomain I M p (Metric.ball 0 r) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : T2Space N := Φ.toDiffeomorph.toHomeomorph.t2Space
    have himg := Φ.symm.isNormalDomain_mfderiv_image h
    rwa [Φ.symm.mfderiv_image_ball, map_zero, Φ.symm_apply_apply] at himg
  · have himg := Φ.isNormalDomain_mfderiv_image h
    rwa [Φ.mfderiv_image_ball, map_zero] at himg

/-- **Isometry invariance of the pointwise injectivity radius.** -/
@[simp]
theorem injectivityRadiusAt_apply (Φ : RiemannianIsometry I J M N) (p : M) :
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
    (a : G)
    (ha : ∀ (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    (x : M) :
    injectivityRadiusAt I M (a • x) = injectivityRadiusAt I M x := by
  simpa only [RiemannianIsometry.coe_constSMul] using
    (RiemannianIsometry.constSMul a ha).injectivityRadiusAt_apply x

/-- On a homogeneous Riemannian manifold (`MulAction.IsPretransitive (Isom I M) M`), the pointwise
injectivity radius is independent of the basepoint. -/
theorem injectivityRadiusAt_eq_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] (p q : M) :
    injectivityRadiusAt I M p = injectivityRadiusAt I M q := by
  obtain ⟨Φ, rfl⟩ := MulAction.exists_smul_eq (Isom I M) q p
  exact Φ.injectivityRadiusAt_apply q

/-- On a homogeneous Riemannian manifold, the global injectivity radius equals the pointwise
injectivity radius at any point. -/
theorem injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] (p : M) :
    injectivityRadius I M = injectivityRadiusAt I M p := by
  refine le_antisymm (injectivityRadius_le p) (le_injectivityRadius_iff.2 fun q ↦ ?_)
  rw [injectivityRadiusAt_eq_of_isPretransitive q p]

/-- Every nonempty homogeneous Riemannian manifold (compact or noncompact) has strictly positive
global injectivity radius. -/
theorem injectivityRadius_pos_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] [Nonempty M] :
    0 < injectivityRadius I M := by
  obtain ⟨p⟩ := ‹Nonempty M›
  rw [injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive p]
  exact injectivityRadiusAt_pos p

end TauCeti

/-! ### `WithMetric` transport and constant rescaling -/

namespace TauCeti.WithMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The tautological diffeomorphism `WithMetric g → M` upgraded to a `RiemannianIsometry` whenever
the ambient `RiemannianBundle` on `M` has inner product `g.inner`. -/
def riemannianIsometry
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w) :
    RiemannianIsometry I I (WithMetric g) M where
  toDiffeomorph := WithMetric.diffeomorph g ∞
  inner_mfderiv' x v w := by
    rw [WithMetric.coe_diffeomorph, hg, WithMetric.inner_def]

@[simp]
theorem coe_riemannianIsometry
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w) :
    ⇑(riemannianIsometry g hg) = ofWithMetric := by
  rw [← RiemannianIsometry.coe_toDiffeomorph]
  exact WithMetric.coe_diffeomorph ∞

@[simp]
theorem riemannianIsometry_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w) (x : WithMetric g) :
    riemannianIsometry g hg x = x.ofWithMetric :=
  congrFun (coe_riemannianIsometry g hg) x

@[simp]
theorem riemannianIsometry_symm_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w) (x : M) :
    (riemannianIsometry g hg).symm x = toWithMetric g x :=
  congrFun ((riemannianIsometry g hg).coe_symm.trans (WithMetric.coe_diffeomorph_symm ∞)) x

/-- Two smooth Riemannian metrics on `M` with pointwise equal inner products have isometric
`WithMetric` copies via the identity diffeomorphism. -/
def riemannianIsometryOfInnerEq
    (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) :
    RiemannianIsometry I I (WithMetric g₁) (WithMetric g₂) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  (riemannianIsometry g₁ fun _ _ _ ↦ rfl).trans (riemannianIsometry g₂ h).symm

@[simp]
theorem riemannianIsometryOfInnerEq_apply
    (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) (x : WithMetric g₁) :
    riemannianIsometryOfInnerEq g₁ g₂ h x = toWithMetric g₂ x.ofWithMetric := by
  dsimp only [riemannianIsometryOfInnerEq]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  exact (RiemannianIsometry.trans_apply _ _ x).trans <|
    (riemannianIsometry_symm_apply g₂ h _).trans
      (congrArg (toWithMetric g₂) (riemannianIsometry_apply g₁ _ x))

/-- Membership in `expDomain` on `WithMetric g` reduces to `M` when `M` carries `g`. -/
theorem mem_expDomain_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w)
    {x : WithMetric g} {v : TangentSpace I x} :
    v ∈ expDomain I (WithMetric g) x ↔
      mfderiv I I ofWithMetric x v ∈ expDomain I M x.ofWithMetric := by
  have h := (riemannianIsometry g hg).mfderiv_mem_expDomain_iff (p := x) (v := v)
  rw [coe_riemannianIsometry] at h
  exact h.symm

section Boundaryless

variable [I.Boundaryless] [T2Space M]

/-- Pointwise equal smooth Riemannian metrics have equal pointwise injectivity radius on their
`WithMetric` copies. -/
theorem injectivityRadiusAt_congr
    (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) (p : M) :
    injectivityRadiusAt I (WithMetric g₁) (toWithMetric g₁ p) =
      injectivityRadiusAt I (WithMetric g₂) (toWithMetric g₂ p) := by
  simpa only [riemannianIsometryOfInnerEq_apply, ofWithMetric_toWithMetric] using
    ((riemannianIsometryOfInnerEq g₁ g₂ h).injectivityRadiusAt_apply (toWithMetric g₁ p)).symm

/-- Pointwise equal smooth Riemannian metrics have equal global injectivity radius on their
`WithMetric` copies. -/
theorem injectivityRadius_congr
    (g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) :
    injectivityRadius I (WithMetric g₁) = injectivityRadius I (WithMetric g₂) :=
  (riemannianIsometryOfInnerEq g₁ g₂ h).injectivityRadius_eq.symm

/-- `ofWithMetric` intertwines `riemannianExp` on `WithMetric g` with `riemannianExp` on `M` when
`M` carries `g`. -/
theorem ofWithMetric_riemannianExp
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w)
    (x : WithMetric g) (v : TangentSpace I x) :
    (riemannianExp I (WithMetric g) x v).ofWithMetric =
      riemannianExp I M x.ofWithMetric (mfderiv I I ofWithMetric x v) := by
  have h := (riemannianIsometry g hg).riemannianExp_mfderiv x v
  rw [coe_riemannianIsometry] at h
  exact h.symm

/-- The pointwise injectivity radius on `WithMetric g` agrees with that on `M` when `M` carries the
inner product of `g`. -/
theorem injectivityRadiusAt_toWithMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w) (p : M) :
    injectivityRadiusAt I (WithMetric g) (toWithMetric g p) = injectivityRadiusAt I M p := by
  simpa only [riemannianIsometry_apply, ofWithMetric_toWithMetric] using
    ((riemannianIsometry g hg).injectivityRadiusAt_apply (toWithMetric g p)).symm

/-- The global injectivity radius on `WithMetric g` agrees with that on `M` when `M` carries the
inner product of `g`. -/
theorem injectivityRadius_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), inner ℝ v w = g.inner x v w) :
    injectivityRadius I (WithMetric g) = injectivityRadius I M :=
  (riemannianIsometry g hg).injectivityRadius_eq.symm

/-- Forward implication for normal tangent balls under constant rescaling of `g` by `c > 0`. -/
private theorem isNormalDomain_ball_rescale_const_of_div
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) {p : M} {r : ℝ}
    (h : IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c))) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
      (toWithMetric _ p) (Metric.ball 0 r) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set p₀ : WithMetric g := toWithMetric g p
  set p_c : WithMetric g_c := toWithMetric g_c p
  have hsqrt : 0 < √c := Real.sqrt_pos.2 hc
  have hrdiv : 0 < r / √c := by simpa only [Metric.mem_ball, dist_self] using h.zero_mem
  have hr : 0 < r := by
    have := mul_pos hrdiv hsqrt
    rwa [div_mul_cancel₀ _ hsqrt.ne'] at this
  let L : TangentSpace I p_c ≃L[ℝ] TangentSpace I p₀ :=
    (diffeomorphWithMetric g_c g ∞).mfderivToContinuousLinearEquiv (by simp) p_c
  have hL_apply (v : TangentSpace I p_c) :
      L v = mfderiv I I (diffeomorphWithMetric g_c g ∞) p_c v :=
    DFunLike.congr_fun
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe (diffeomorphWithMetric g_c g ∞) (by simp)) v
  have hL_of (v : TangentSpace I p_c) :
      mfderiv I I ofWithMetric p₀ (L v) = mfderiv I I ofWithMetric p_c v := by
    rw [mfderiv_ofWithMetric_apply, mfderiv_ofWithMetric_apply, hL_apply]
    exact DFunLike.congr_fun (mfderiv_diffeomorphWithMetric g ∞ p_c) v
  have hL_norm (v : TangentSpace I p_c) : ‖v‖ = √c * ‖L v‖ := by
    have hsq : ‖v‖ ^ 2 = (√c * ‖L v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        inner_def, inner_def, hL_of, ContMDiffRiemannianMetric.rescale_inner]
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  have hL_mem {v : TangentSpace I p_c} (hv : v ∈ Metric.ball 0 r) :
      L v ∈ Metric.ball 0 (r / √c) := by
    rw [mem_ball_zero_iff] at hv ⊢
    exact (lt_div_iff₀ hsqrt).2 (by linarith [hL_norm v])
  have hdom (v : TangentSpace I p_c) :
      v ∈ expDomain I (WithMetric g_c) p_c ↔ L v ∈ expDomain I (WithMetric g) p₀ := by
    have h₁ : v ∈ expDomain I (WithMetric g_c) p_c ↔
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
          mfderiv I I ofWithMetric p_c v ∈ expDomain I M p) := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g_c
      exact mem_expDomain_iff g_c fun _ _ _ ↦ rfl
    have h₂ : L v ∈ expDomain I (WithMetric g) p₀ ↔
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          mfderiv I I ofWithMetric p₀ (L v) ∈ expDomain I M p) := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g
      exact mem_expDomain_iff g fun _ _ _ ↦ rfl
    rw [h₁, h₂, hL_of, g.expDomain_rescale_const hc p]
  have hexp (v : TangentSpace I p_c) :
      riemannianExp I (WithMetric g_c) p_c v =
        diffeomorphWithMetric g g_c ∞ (riemannianExp I (WithMetric g) p₀ (L v)) := by
    apply ofWithMetric_injective
    have h₁ : (riemannianExp I (WithMetric g_c) p_c v).ofWithMetric =
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
          riemannianExp I M p (mfderiv I I ofWithMetric p_c v)) := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g_c
      exact ofWithMetric_riemannianExp g_c (fun _ _ _ ↦ rfl) p_c v
    have h₂ : (riemannianExp I (WithMetric g) p₀ (L v)).ofWithMetric =
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          riemannianExp I M p (mfderiv I I ofWithMetric p₀ (L v))) := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g
      exact ofWithMetric_riemannianExp g (fun _ _ _ ↦ rfl) p₀ (L v)
    simp only [diffeomorphWithMetric_apply, ofWithMetric_toWithMetric, h₁, h₂, hL_of]
    exact g.riemannianExp_rescale_const hc p _
  refine
    { isOpen := Metric.isOpen_ball
      zero_mem := Metric.mem_ball_self hr
      starConvex := (convex_ball (0 : TangentSpace I p_c) r).starConvex (Metric.mem_ball_self hr)
      subset_expDomain := fun v hv ↦ (hdom v).2 (h.subset_expDomain (hL_mem hv))
      injOn := fun v₁ hv₁ v₂ hv₂ heq ↦ by
        rw [hexp, hexp] at heq
        exact L.injective
          (h.injOn (hL_mem hv₁) (hL_mem hv₂)
            (EquivLike.injective (diffeomorphWithMetric g g_c ∞) heq))
      isLocalDiffeomorphOn := fun ⟨v, hv⟩ ↦ by
        rw [funext hexp]
        have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p_c) 𝓘(ℝ, TangentSpace I p₀) ∞ L v := by
          simpa only [ContinuousLinearEquiv.coe_toDiffeomorph] using
            L.toDiffeomorph.isLocalDiffeomorph v
        have h2 : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p₀) I ∞
            (riemannianExp I (WithMetric g) p₀) (L v) :=
          h.isLocalDiffeomorphOn ⟨L v, hL_mem hv⟩
        have h3 : IsLocalDiffeomorphAt I I ∞ (diffeomorphWithMetric g g_c ∞)
            (riemannianExp I (WithMetric g) p₀ (L v)) :=
          (diffeomorphWithMetric g g_c ∞).isLocalDiffeomorph _
        exact (h1.comp (hg := h2)).comp (hg := h3) }

/-- **Normal tangent balls under constant metric rescaling.** Multiplying `g` by `c > 0` scales the
radius of normal tangent balls by `√c`. -/
theorem isNormalDomain_ball_rescale_const_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (p : M) (r : ℝ) :
    IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (toWithMetric _ p) (Metric.ball 0 r) ↔
      IsNormalDomain I (WithMetric g) (toWithMetric g p) (Metric.ball 0 (r / √c)) := by
  refine ⟨fun h ↦ ?_, isNormalDomain_ball_rescale_const_of_div g hc⟩
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  set g' := g_c.rescale (fun _ ↦ c⁻¹) contMDiff_const fun _ ↦ inv_pos.2 hc
  have hr_eq : (r / √c) / √c⁻¹ = r := by
    rw [Real.sqrt_inv, div_inv_eq_mul, div_mul_cancel₀ _ (Real.sqrt_pos.2 hc).ne']
  have h' : IsNormalDomain I (WithMetric g') (toWithMetric g' p) (Metric.ball 0 (r / √c)) :=
    isNormalDomain_ball_rescale_const_of_div g_c (inv_pos.2 hc) (hr_eq.symm ▸ h)
  let Ψ := riemannianIsometryOfInnerEq g' g fun x v w ↦ by
    simp [g', g_c, inv_mul_cancel₀ hc.ne']
  have hΨ : Ψ (toWithMetric g' p) = toWithMetric g p :=
    riemannianIsometryOfInnerEq_apply g' g _ (toWithMetric g' p)
  have himg := (Ψ.isNormalDomain_ball_iff (toWithMetric g' p) (r / √c)).2 h'
  rwa [hΨ] at himg

/-- **Scaling of the pointwise injectivity radius (`WithMetric` form).** Multiplying a smooth
Riemannian metric `g` by a positive constant `c` multiplies `inj(p)` by `ENNReal.ofReal √c`. -/
@[simp]
theorem injectivityRadiusAt_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (p : M) :
    injectivityRadiusAt I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (toWithMetric _ p) =
      ENNReal.ofReal √c * injectivityRadiusAt I (WithMetric g) (toWithMetric g p) := by
  have hsqrt : 0 < √c := Real.sqrt_pos.2 hc
  refine le_antisymm ?_ ?_
  · rw [injectivityRadiusAt_def]
    refine iSup₂_le fun r hr ↦ ?_
    have hr' := (isNormalDomain_ball_rescale_const_iff g hc p r).1 hr
    have heq : ENNReal.ofReal r = ENNReal.ofReal √c * ENNReal.ofReal (r / √c) := by
      rw [← ENNReal.ofReal_mul hsqrt.le, mul_div_cancel₀ _ hsqrt.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hr'.ofReal_le_injectivityRadiusAt zero_le
  · rw [injectivityRadiusAt_def, ENNReal.mul_iSup]
    simp_rw [ENNReal.mul_iSup]
    refine iSup₂_le fun s hs ↦ ?_
    have hs' : IsNormalDomain I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (toWithMetric _ p) (Metric.ball 0 (√c * s)) :=
      (isNormalDomain_ball_rescale_const_iff g hc p (√c * s)).2
        (by rwa [mul_div_cancel_left₀ s hsqrt.ne'])
    rw [← ENNReal.ofReal_mul hsqrt.le]
    exact hs'.ofReal_le_injectivityRadiusAt

/-- **Scaling of the global injectivity radius (`WithMetric` form).** Multiplying a smooth
Riemannian metric `g` by a positive constant `c` multiplies `inj(M)` by `ENNReal.ofReal √c`. -/
@[simp]
theorem injectivityRadius_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) :
    injectivityRadius I (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)) =
      ENNReal.ofReal √c * injectivityRadius I (WithMetric g) := by
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have h0 : ENNReal.ofReal √c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne'
  rw [injectivityRadius_def, injectivityRadius_def,
    ← (equiv g_c).symm.surjective.iInf_comp, ← (equiv g).symm.surjective.iInf_comp,
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun p ↦ ?_
  simp only [equiv_symm_apply]
  exact injectivityRadiusAt_rescale_const g hc p

end Boundaryless

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
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have h₁ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g_c;
      injectivityRadiusAt I M p) =
      injectivityRadiusAt I (TauCeti.WithMetric g_c) (TauCeti.WithMetric.toWithMetric g_c p) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContMDiffRiemannianBundle g_c
    exact (TauCeti.WithMetric.injectivityRadiusAt_toWithMetric g_c (fun _ _ _ ↦ rfl) p).symm
  have h₂ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g;
      injectivityRadiusAt I M p) =
      injectivityRadiusAt I (TauCeti.WithMetric g) (TauCeti.WithMetric.toWithMetric g p) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContMDiffRiemannianBundle g
    exact (TauCeti.WithMetric.injectivityRadiusAt_toWithMetric g (fun _ _ _ ↦ rfl) p).symm
  rw [h₁, h₂, TauCeti.WithMetric.injectivityRadiusAt_rescale_const g hc p]

/-- **Scaling of the global injectivity radius under constant rescaling (`letI` form).** -/
theorem injectivityRadius_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) :
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
  set g_c := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have h₁ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g_c;
      injectivityRadius I M) =
      injectivityRadius I (TauCeti.WithMetric g_c) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g_c.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContMDiffRiemannianBundle g_c
    exact (TauCeti.WithMetric.injectivityRadius_eq g_c fun _ _ _ ↦ rfl).symm
  have h₂ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g;
      injectivityRadius I M) =
      injectivityRadius I (TauCeti.WithMetric g) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Bundle.instIsContMDiffRiemannianBundle g
    exact (TauCeti.WithMetric.injectivityRadius_eq g fun _ _ _ ↦ rfl).symm
  rw [h₁, h₂, TauCeti.WithMetric.injectivityRadius_rescale_const g hc]

end Bundle.ContMDiffRiemannianMetric

/-! ### Finite-dimensional inner-product spaces -/

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every point of a finite-dimensional real inner-product space has infinite injectivity radius. -/
@[simp]
theorem injectivityRadiusAt_model_space (p : F) :
    injectivityRadiusAt 𝓘(ℝ, F) F p = ⊤ :=
  injectivityRadiusAt_eq_top_iff_isNormalDomain_univ.2
    (isNormalDomain_model_space p isOpen_univ (mem_univ 0) (starConvex_univ 0))

/-- A finite-dimensional real inner-product space has infinite global injectivity radius. -/
@[simp]
theorem injectivityRadius_model_space :
    injectivityRadius 𝓘(ℝ, F) F = ⊤ := by
  simp [injectivityRadius_def]

end TauCeti.Manifold

end
