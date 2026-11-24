/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Domain
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Opens
public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Clairaut
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed

/-!
# Geodesics and Clairaut's theorem for surfaces of revolution

For the genuine induced Riemannian metric on an open regular parameter domain, the native
geodesic equation is the angular/meridional second-order system. Clairaut's angular momentum
is constant on each connected time domain with unique derivatives. Coordinate velocities and
accelerations use derivatives within that domain; the angle form includes the speed factor.

Ported from Yangyang Li's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/tree/b442a9f3077a4be3823b712ec92b2335dd34e771/ForTauCeti/Geometry/Manifold/Riemannian/Surface/Revolution).

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*,
  [electronic edition](https://academicweb.nd.edu/~lnicolae/Lectures.pdf),
  Example 5.1.16 and Theorem 5.1.17, pp. 211–212.
-/

public noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff

namespace TauCeti.SurfaceOfRevolution

open TauCeti.Manifold

local notation "P" => ℝ × ℝ
local notation "IP" => 𝓘(ℝ, P)

/-- Differentiating a curve on a revolution surface differentiates the parametrization
on its coordinate velocity. -/
theorem derivWithin_parametrization_subtype {f g : ℝ → ℝ} {U : Opens P}
    {γ : ℝ → U} {s : Set ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t).val.2) (hg : DifferentiableAt ℝ g (γ t).val.2)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) IP γ s t) (hs : UniqueDiffWithinAt ℝ s t) :
    derivWithin (fun r ↦ parametrization f g (γ r).val) s t =
      fderiv ℝ (parametrization f g) (γ t).val
        (derivWithin (fun r ↦ (γ r).val) s t) := by
  have hc : DifferentiableWithinAt ℝ (fun r ↦ (γ r).val) s t :=
    (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero |>.comp_mdifferentiableWithinAt t hγ)
      |>.differentiableWithinAt
  exact ((differentiableAt_parametrization hf hg).hasFDerivAt.comp_hasDerivWithinAt t
    hc.hasDerivWithinAt).derivWithin hs

section Speed

variable {f g : ℝ → ℝ} {U : Opens P}
  [RiemannianBundle (fun p : U ↦ TangentSpace IP p)]
  (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
    metric f g p.val
      (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p w))
      (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p z)))

include hmetric

/-- The Euclidean speed of the immersed curve equals its native Riemannian speed. -/
theorem norm_derivWithin_parametrization_eq {γ : ℝ → U} {s : Set ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t).val.2) (hg : DifferentiableAt ℝ g (γ t).val.2)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) IP γ s t) (hs : UniqueDiffWithinAt ℝ s t) :
    ‖derivWithin (fun r ↦ parametrization f g (γ r).val) s t‖ =
      ‖curveVelocityWithin IP γ s t‖ := by
  rw [derivWithin_parametrization_subtype hf hg hγ hs,
    norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    inner_curveVelocityWithin_self_eq_metric hmetric hγ hs, metric_eq_inner_fderiv hf hg]

/-- At unit native speed and nonnegative radius, the radius-angle quantity is the
coordinate angular momentum. -/
theorem radius_mul_cos_angle_eq_angularMomentum {γ : ℝ → U} {s : Set ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t).val.2) (hg : DifferentiableAt ℝ g (γ t).val.2)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) IP γ s t) (hs : UniqueDiffWithinAt ℝ s t)
    (hr : 0 ≤ f (γ t).val.2) (hw : ‖curveVelocityWithin IP γ s t‖ = 1) :
    f (γ t).val.2 * Real.cos (InnerProductGeometry.angle
      (derivWithin (fun r ↦ parametrization f g (γ r).val) s t)
      (fderiv ℝ (parametrization f g) (γ t).val (1, 0))) =
        angularMomentum f (γ t).val.2 (derivWithin (fun r ↦ (γ r).val) s t).1 := by
  have hv := norm_derivWithin_parametrization_eq hmetric hf hg hγ hs
  rw [derivWithin_parametrization_subtype hf hg hγ hs] at hv ⊢
  simpa only [angularMomentum_def] using
    radius_mul_cos_angle_eq_sq_mul_fst hf hg hr (hv.trans hw)

end Speed

section NativeMetric

variable {f g : ℝ → ℝ} {U : Opens P}
  [RiemannianBundle (fun p : U ↦ TangentSpace IP p)]
  [IsContMDiffRiemannianBundle IP 1 P (fun p : U ↦ TangentSpace IP p)]
  (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
    metric f g p.val
      (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w))
      (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p z)))
  (hf : ∀ p : U, ContDiffAt ℝ 2 f p.val.2)
  (hg : ∀ p : U, ContDiffAt ℝ 2 g p.val.2)

include hmetric hf hg

/-- The two explicit scalar geodesic equations, in an arbitrary regular profile parameter,
are equivalent to the native Levi-Civita geodesic predicate. -/
theorem isGeodesicCurveOn_iff {γ : ℝ → U} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    IsGeodesicCurveOn IP γ s ↔ ContMDiffOn 𝓘(ℝ) IP 2 γ s ∧ ∀ t ∈ s,
      let c := fun r ↦ (γ r).val
      (derivWithin (derivWithin c s) s t).1 + 2 * (deriv f (c t).2 / f (c t).2) *
          (derivWithin c s t).1 * (derivWithin c s t).2 = 0 ∧
      (derivWithin (derivWithin c s) s t).2 -
        f (c t).2 * deriv f (c t).2 / profileSpeedSq f g (c t).2 *
          (derivWithin c s t).1 ^ 2 +
        (deriv f (c t).2 * deriv (deriv f) (c t).2 +
            deriv g (c t).2 * deriv (deriv g) (c t).2) / profileSpeedSq f g (c t).2 *
          (derivWithin c s t).2 ^ 2 = 0 := by
  have hregular (p : U) : f p.val.2 ≠ 0 ∧ 0 < profileSpeedSq f g p.val.2 := by
    let e := (tangentSpaceOpenEquiv (I := IP) p).trans
      (NormedSpace.fromTangentSpace p.val)
    have hp (w : P) (hw : w ≠ 0) : 0 < metric f g p.val w w := by
      have hne : e.symm w ≠ 0 := by simpa using hw
      have h := real_inner_self_pos.mpr hne
      rw [hmetric] at h
      have he : NormedSpace.fromTangentSpace p.val
          (tangentSpaceOpenEquiv (I := IP) p (e.symm w)) = w := e.apply_symm_apply w
      rwa [he] at h
    have h₁ := hp (1, 0) (by norm_num)
    have h₂ := hp (0, 1) (by norm_num)
    simp only [metric_apply] at h₁ h₂
    constructor
    · intro hz
      simp [hz] at h₁
    · simpa using h₂
  rw [isGeodesicCurveOn_iff_christoffelSecondKind hmetric hs]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro t ht
  rw [christoffelSecondKind_metric ((hf (γ t)).differentiableAt (by norm_num))
    (((hf (γ t)).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (((hg (γ t)).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (hregular (γ t)).1 (hregular (γ t)).2.ne']
  rw [Prod.ext_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, neg_div]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith [h₁, h₂]

/-- Clairaut's angular momentum is constant along a native geodesic on a connected
time domain with unique derivatives. No unit-speed assumption is needed. -/
theorem angularMomentum_eq {γ : ℝ → U} {s : Set ℝ}
    (hc : IsPreconnected s) (hγ : IsGeodesicCurveOn IP γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    angularMomentum f (γ a).val.2 (derivWithin (fun r ↦ (γ r).val) s a).1 =
      angularMomentum f (γ b).val.2 (derivWithin (fun r ↦ (γ r).val) s b).1 := by
  let c := fun r ↦ (γ r).val
  have hs := hγ.uniqueDiffOn
  have hc₂ : ContDiffOn ℝ 2 c s :=
    (contMDiff_subtypeVal.comp_contMDiffOn hγ.contMDiffOn).contDiffOn
  have heq := ((isGeodesicCurveOn_iff hmetric hf hg hs).mp hγ).2
  have hct (t : ℝ) (ht : t ∈ s) := hc₂.differentiableOn (by norm_num) t ht
  have hdc (t : ℝ) (ht : t ∈ s) :=
    (hc₂.derivWithin hs (m := 1) (by norm_num)).differentiableOn (by norm_num) t ht
  apply angularMomentum_eq_of_derivWithin_add_eq_zero (v := fun r ↦ (c r).2) hc
    (fun t _ ↦ (hf (γ t)).differentiableAt (by norm_num))
    (fun t ht ↦ (hdc t ht).fst) (fun t ht ↦ (hct t ht).snd) ?_ ha hb
  intro t ht
  have hfst : HasDerivWithinAt (fun r ↦ (derivWithin c s r).1)
      (derivWithin (derivWithin c s) s t).1 s t :=
    (hdc t ht).hasDerivWithinAt.fst
  have hsnd : HasDerivWithinAt (fun r ↦ (c r).2) (derivWithin c s t).2 s t :=
    (hct t ht).hasDerivWithinAt.snd
  rw [hfst.derivWithin (hs t ht), hsnd.derivWithin (hs t ht)]
  exact (heq t ht).1

/-- The angle-speed form of Clairaut's theorem along a native geodesic. The radius may
have either sign and the curve need not have unit speed. -/
theorem abs_radius_mul_speed_mul_cos_angle_eq_of_isGeodesicCurveOn
    {γ : ℝ → U} {s : Set ℝ} (hc : IsPreconnected s) (hγ : IsGeodesicCurveOn IP γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    |f (γ a).val.2| * ‖derivWithin (fun r ↦ parametrization f g (γ r).val) s a‖ *
        Real.cos (InnerProductGeometry.angle
          (derivWithin (fun r ↦ parametrization f g (γ r).val) s a)
          (fderiv ℝ (parametrization f g) (γ a).val (1, 0))) =
      |f (γ b).val.2| * ‖derivWithin (fun r ↦ parametrization f g (γ r).val) s b‖ *
        Real.cos (InnerProductGeometry.angle
          (derivWithin (fun r ↦ parametrization f g (γ r).val) s b)
          (fderiv ℝ (parametrization f g) (γ b).val (1, 0))) := by
  have hv (t : ℝ) (ht : t ∈ s) := derivWithin_parametrization_subtype
    ((hf (γ t)).differentiableAt (by norm_num)) ((hg (γ t)).differentiableAt (by norm_num))
    (hγ.mdifferentiableOn t ht) (hγ.uniqueDiffOn t ht)
  rw [hv a ha, hv b hb,
    abs_radius_mul_norm_mul_cos_angle_eq_sq_mul_fst
      ((hf (γ a)).differentiableAt (by norm_num)) ((hg (γ a)).differentiableAt (by norm_num)),
    abs_radius_mul_norm_mul_cos_angle_eq_sq_mul_fst
      ((hf (γ b)).differentiableAt (by norm_num)) ((hg (γ b)).differentiableAt (by norm_num))]
  simpa only [angularMomentum_def] using angularMomentum_eq hmetric hf hg hc hγ ha hb

/-- Clairaut's radius-angle quantity is constant on a connected native geodesic whose
speed is one at a single parameter, provided the endpoint radii are nonnegative. -/
theorem radius_mul_cos_angle_eq_of_isGeodesicCurveOn
    {γ : ℝ → U} {s : Set ℝ} (hc : IsPreconnected s) (hγ : IsGeodesicCurveOn IP γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hra : 0 ≤ f (γ a).val.2) (hrb : 0 ≤ f (γ b).val.2)
    (hw : ‖curveVelocityWithin IP γ s a‖ = 1) :
    f (γ a).val.2 * Real.cos (InnerProductGeometry.angle
        (derivWithin (fun r ↦ parametrization f g (γ r).val) s a)
        (fderiv ℝ (parametrization f g) (γ a).val (1, 0))) =
      f (γ b).val.2 * Real.cos (InnerProductGeometry.angle
        (derivWithin (fun r ↦ parametrization f g (γ r).val) s b)
        (fderiv ℝ (parametrization f g) (γ b).val (1, 0))) := by
  have hw' : ‖curveVelocityWithin IP γ s b‖ = 1 :=
    (hγ.norm_curveVelocityWithin_eq hc hb ha).trans hw
  rw [radius_mul_cos_angle_eq_angularMomentum hmetric
      ((hf (γ a)).differentiableAt (by norm_num)) ((hg (γ a)).differentiableAt (by norm_num))
      (hγ.mdifferentiableOn a ha) (hγ.uniqueDiffOn a ha) hra hw,
    radius_mul_cos_angle_eq_angularMomentum hmetric
      ((hf (γ b)).differentiableAt (by norm_num)) ((hg (γ b)).differentiableAt (by norm_num))
      (hγ.mdifferentiableOn b hb) (hγ.uniqueDiffOn b hb) hrb hw']
  exact angularMomentum_eq hmetric hf hg hc hγ ha hb

end NativeMetric

/-- Clairaut's theorem for the explicitly constructed induced metric, with all geometric
structure supplied by the regular revolution parametrization itself. -/
theorem angularMomentum_eq_of_isGeodesicCurveOn_riemannianMetric {f g : ℝ → ℝ}
    {n : ℕ∞ω} (hn : 1 ≤ n) (U : Opens P)
    (hf : ∀ p : U, ContDiffAt ℝ (n + 1) f p.val.2)
    (hg : ∀ p : U, ContDiffAt ℝ (n + 1) g p.val.2)
    (hr : ∀ p : U, f p.val.2 ≠ 0)
    (hreg : ∀ p : U, 0 < profileSpeedSq f g p.val.2)
    {γ : ℝ → U} {s : Set ℝ} (hc : IsPreconnected s)
    (hγ : letI : RiemannianBundle (fun p : U ↦ TangentSpace IP p) :=
      ⟨(riemannianMetric (n := n) U hf hg hr hreg).toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle IP 1 P (fun p : U ↦ TangentSpace IP p) :=
        IsContMDiffRiemannianBundle.of_le hn
      IsGeodesicCurveOn IP γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    angularMomentum f (γ a).val.2 (derivWithin (fun r ↦ (γ r).val) s a).1 =
      angularMomentum f (γ b).val.2 (derivWithin (fun r ↦ (γ r).val) s b).1 := by
  let : RiemannianBundle (fun p : U ↦ TangentSpace IP p) :=
    ⟨(riemannianMetric (n := n) U hf hg hr hreg).toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle IP 1 P (fun p : U ↦ TangentSpace IP p) :=
    IsContMDiffRiemannianBundle.of_le hn
  have hn₂ : (2 : ℕ∞ω) ≤ n + 1 := calc
    _ = (1 : ℕ∞ω) + 1 := by norm_num
    _ ≤ n + 1 := add_le_add hn (le_refl 1)
  exact angularMomentum_eq (riemannianMetric_inner (n := n) U hf hg hr hreg)
    (fun p ↦ (hf p).of_le hn₂) (fun p ↦ (hg p).of_le hn₂) hc hγ ha hb

end TauCeti.SurfaceOfRevolution
