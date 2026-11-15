/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Clairaut
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Geodesics and Clairaut's theorem for surfaces of revolution

For the genuine induced Riemannian metric on an open regular parameter domain, the native
geodesic equation is the angular/meridional second-order system. Clairaut's angular momentum
is constant on each connected open time interval. Coordinate velocities and accelerations
are the components of the ordinary derivatives of the coordinate curve.

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

section NativeMetric

variable {f g : ℝ → ℝ} {U : Opens P}
  [RiemannianBundle (fun p : U ↦ TangentSpace IP p)]
  [IsContMDiffRiemannianBundle IP ∞ P (fun p : U ↦ TangentSpace IP p)]
  (hmetric : ∀ (p : U) (w z : TangentSpace IP p), inner ℝ w z =
    metric f g p.val
      (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p w))
      (NormedSpace.fromTangentSpace p.val (Manifold.tangentSpaceOpenEquiv (I := IP) p z)))
  (hf : ∀ p : U, ContDiffAt ℝ ∞ f p.val.2)
  (hg : ∀ p : U, ContDiffAt ℝ ∞ g p.val.2)
  (hr : ∀ p : U, f p.val.2 ≠ 0)
  (hreg : ∀ p : U, 0 < profileSpeedSq f g p.val.2)

-- Connection uses the same downgrade, but its local instance is not exported on import.
local instance (priority := 10000) :
    IsContMDiffRiemannianBundle IP 1 P (fun p : U ↦ TangentSpace IP p) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by norm_num)

include hmetric hf hg hr hreg

/-- The two explicit scalar geodesic equations, in an arbitrary regular profile parameter,
are equivalent to the native Levi-Civita geodesic predicate. -/
theorem isGeodesicCurveOn_iff {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s) :
    IsGeodesicCurveOn IP γ s ↔ ContMDiffOn 𝓘(ℝ) IP 2 γ s ∧ ∀ t ∈ s,
      let c := fun r ↦ (γ r).val
      (deriv (deriv c) t).1 + 2 * (deriv f (c t).2 / f (c t).2) *
          (deriv c t).1 * (deriv c t).2 = 0 ∧
      (deriv (deriv c) t).2 - f (c t).2 * deriv f (c t).2 / profileSpeedSq f g (c t).2 *
          (deriv c t).1 ^ 2 +
        (deriv f (c t).2 * deriv (deriv f) (c t).2 +
            deriv g (c t).2 * deriv (deriv g) (c t).2) / profileSpeedSq f g (c t).2 *
          (deriv c t).2 ^ 2 = 0 := by
  rw [isGeodesicCurveOn_iff_coordinateEquation hmetric hs]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro t ht
  rw [christoffelSecondKind_metric ((hf (γ t)).differentiableAt (by simp))
    (((hf (γ t)).derivWithin (m := 1) (by simp)).differentiableAt (by norm_num))
    (((hg (γ t)).derivWithin (m := 1) (by simp)).differentiableAt (by norm_num))
    (hr (γ t)) (hreg (γ t)).ne']
  rw [Prod.ext_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, neg_div]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith [h₁, h₂]

/-- Clairaut's angular momentum is constant along a native geodesic on a connected open
time domain. No unit-speed assumption is needed for this coordinate form. -/
theorem angularMomentum_eq {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s)
    (hc : IsPreconnected s) (hγ : IsGeodesicCurveOn IP γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    angularMomentum f (γ a).val.2 (deriv (fun r ↦ (γ r).val) a).1 =
      angularMomentum f (γ b).val.2 (deriv (fun r ↦ (γ r).val) b).1 := by
  let c := fun r ↦ (γ r).val
  have hc₂ : ContDiffOn ℝ 2 c s :=
    (contMDiff_subtype_val.comp_contMDiffOn hγ.contMDiffOn).contDiffOn
  have heq := ((isGeodesicCurveOn_iff hmetric hf hg hr hreg hs).mp hγ).2
  have hct (t : ℝ) (ht : t ∈ s) :=
    (hc₂.contDiffAt (hs.mem_nhds ht)).differentiableAt (by norm_num)
  have hdc (t : ℝ) (ht : t ∈ s) :=
    ((hc₂.deriv_of_isOpen hs (m := 1) (by norm_num)).contDiffAt
      (hs.mem_nhds ht)).differentiableAt (by norm_num)
  apply angularMomentum_eq_of_coordinateEquation (v := fun r ↦ (c r).2) hs hc
    (fun t _ ↦ (hf (γ t)).differentiableAt (by simp))
    (fun t ht ↦ (hdc t ht).fst) (fun t ht ↦ (hct t ht).snd)
    (fun t _ ↦ hr (γ t)) ?_ ha hb
  intro t ht
  have hfst : HasDerivAt (fun r ↦ (deriv c r).1) (deriv (deriv c) t).1 t :=
    (hdc t ht).hasDerivAt.fst
  have hsnd : HasDerivAt (fun r ↦ (c r).2) (deriv c t).2 t :=
    (hct t ht).hasDerivAt.snd
  rw [hfst.deriv, hsnd.deriv]
  exact (heq t ht).1

/-- The geometric form of Clairaut's theorem for an arclength-parametrized native geodesic:
radius times the cosine of the angle with the positive parallel is constant. -/
theorem radius_mul_cos_angle_eq_of_isGeodesicCurveOn {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s)
    (hc : IsPreconnected s) (hγ : IsGeodesicCurveOn IP γ s)
    (hpos : ∀ t ∈ s, 0 < f (γ t).val.2)
    (hunit : ∀ t ∈ s, ‖deriv (fun r ↦ parametrization f g (γ r).val) t‖ = 1)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    f (γ a).val.2 * Real.cos (InnerProductGeometry.angle
        (deriv (fun r ↦ parametrization f g (γ r).val) a)
        (fderiv ℝ (parametrization f g) (γ a).val (1, 0))) =
      f (γ b).val.2 * Real.cos (InnerProductGeometry.angle
        (deriv (fun r ↦ parametrization f g (γ r).val) b)
        (fderiv ℝ (parametrization f g) (γ b).val (1, 0))) := by
  have hv (t : ℝ) (ht : t ∈ s) :
      deriv (fun r ↦ parametrization f g (γ r).val) t =
        fderiv ℝ (parametrization f g) (γ t).val (deriv (fun r ↦ (γ r).val) t) := by
    have hct : DifferentiableAt ℝ (fun r ↦ (γ r).val) t :=
      ((contMDiff_subtype_val.comp_contMDiffOn hγ.contMDiffOn).contDiffOn.contDiffAt
        (hs.mem_nhds ht)).differentiableAt (by norm_num)
    exact ((differentiableAt_parametrization ((hf (γ t)).differentiableAt (by simp))
      ((hg (γ t)).differentiableAt (by simp))).hasFDerivAt.comp_hasDerivAt t hct.hasDerivAt).deriv
  have hangle (t : ℝ) (ht : t ∈ s) := radius_mul_cos_angle_eq_sq_mul_fst
    ((hf (γ t)).differentiableAt (by simp)) ((hg (γ t)).differentiableAt (by simp))
    (hpos t ht) (hv t ht ▸ hunit t ht)
  rw [hv a ha, hv b hb, hangle a ha, hangle b hb]
  simpa only [angularMomentum_def] using
    angularMomentum_eq hmetric hf hg hr hreg hs hc hγ ha hb

end NativeMetric

/-- Clairaut's theorem for the explicitly constructed induced metric, with all geometric
structure supplied by the regular revolution parametrization itself. -/
theorem angularMomentum_eq_induced {f g : ℝ → ℝ} (U : Opens P)
    (hf : ∀ p : U, ContDiffAt ℝ ∞ f p.val.2)
    (hg : ∀ p : U, ContDiffAt ℝ ∞ g p.val.2)
    (hr : ∀ p : U, f p.val.2 ≠ 0)
    (hreg : ∀ p : U, 0 < profileSpeedSq f g p.val.2)
    {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s) (hc : IsPreconnected s)
    (hγ : letI : RiemannianBundle (fun p : U ↦ TangentSpace IP p) :=
      ⟨(riemannianMetric U hf hg hr hreg).toRiemannianMetric⟩
      IsGeodesicCurveOn IP γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    angularMomentum f (γ a).val.2 (deriv (fun r ↦ (γ r).val) a).1 =
      angularMomentum f (γ b).val.2 (deriv (fun r ↦ (γ r).val) b).1 := by
  let : RiemannianBundle (fun p : U ↦ TangentSpace IP p) :=
    ⟨(riemannianMetric U hf hg hr hreg).toRiemannianMetric⟩
  exact angularMomentum_eq (riemannianMetric_inner U hf hg hr hreg) hf hg hr hreg hs hc hγ ha hb

end TauCeti.SurfaceOfRevolution
