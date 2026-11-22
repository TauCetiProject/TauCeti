/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Rescale
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential

/-!
# Behavior of the injectivity radius under isometries and metric rescaling

Smooth Riemannian isometries preserve `inj(p)` and `inj(M)`; consequently `inj` is constant and
strictly positive on homogeneous Riemannian manifolds. Multiplying a smooth metric `g` by `c > 0`
multiplies both `inj(p)` and `inj(M)` by `ENNReal.ofReal √c` (proved in both `TauCeti.WithMetric`
and `letI` forms).

## Main results

* `TauCeti.RiemannianIsometry.injectivityRadiusAt_apply`,
  `TauCeti.RiemannianIsometry.injectivityRadius_eq`: invariance under Riemannian isometries.
* `TauCeti.injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive`,
  `TauCeti.injectivityRadius_pos_of_isPretransitive`: constancy and positivity on homogeneous
  Riemannian manifolds.
* `TauCeti.WithMetric.injectivityRadiusAt_toWithMetric`,
  `TauCeti.WithMetric.injectivityRadius_eq`,
  `TauCeti.WithMetric.injectivityRadiusAt_congr`,
  `TauCeti.WithMetric.injectivityRadius_congr`,
  `Bundle.ContMDiffRiemannianMetric.injectivityRadiusAt_eq_withMetric`,
  `Bundle.ContMDiffRiemannianMetric.injectivityRadius_eq_withMetric`: `WithMetric` transport and
  congruence.
* `TauCeti.WithMetric.injectivityRadiusAt_rescale_const`,
  `TauCeti.WithMetric.injectivityRadius_rescale_const`, and their `letI` counterparts in
  `Bundle.ContMDiffRiemannianMetric`: scaling by `√c` under `g ↦ c g`.

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

/-- Every homogeneous Riemannian manifold (compact or noncompact; if empty, `inj(M) = ⊤`) has
strictly positive global injectivity radius. -/
theorem injectivityRadius_pos_of_isPretransitive
    [MulAction.IsPretransitive (Isom I M) M] : 0 < injectivityRadius I M := by
  rcases isEmpty_or_nonempty M with _ | ⟨⟨p⟩⟩
  · simp
  · exact injectivityRadius_eq_injectivityRadiusAt_of_isPretransitive (I := I) p ▸
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
  simpa only [riemannianIsometryOfInner_apply, ofWithMetric_toWithMetric] using
    ((riemannianIsometryOfInner g hg).injectivityRadiusAt_apply (toWithMetric g p)).symm

/-- The global injectivity radius on `WithMetric g` agrees with that on `M` when `M` carries the
inner product of `g`. -/
theorem injectivityRadius_eq [I.Boundaryless] [T2Space M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    injectivityRadius I (WithMetric g) = injectivityRadius I M :=
  (riemannianIsometryOfInner g hg).injectivityRadius_eq.symm

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

/-- Pointwise injectivity radius in the `letI`-installed metric `g` equals that of
`TauCeti.WithMetric g`. -/
theorem injectivityRadiusAt_eq_withMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (p : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g;
      injectivityRadiusAt I M p) =
      injectivityRadiusAt I (TauCeti.WithMetric g) (TauCeti.WithMetric.toWithMetric g p) :=
  let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g
  (TauCeti.WithMetric.injectivityRadiusAt_toWithMetric g g.inner_riemannianBundle p).symm

/-- Global injectivity radius in the `letI`-installed metric `g` equals that of
`TauCeti.WithMetric g`. -/
theorem injectivityRadius_eq_withMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle g;
      injectivityRadius I M) =
      injectivityRadius I (TauCeti.WithMetric g) :=
  let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I ∞ E _ := Bundle.instIsContMDiffRiemannianBundle g
  (TauCeti.WithMetric.injectivityRadius_eq g g.inner_riemannianBundle).symm

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
  rw [injectivityRadiusAt_eq_withMetric _, injectivityRadiusAt_eq_withMetric g,
    TauCeti.WithMetric.injectivityRadiusAt_rescale_const g hc p]

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
  rw [injectivityRadius_eq_withMetric _, injectivityRadius_eq_withMetric g,
    TauCeti.WithMetric.injectivityRadius_rescale_const g hc]

end Bundle.ContMDiffRiemannianMetric

end
