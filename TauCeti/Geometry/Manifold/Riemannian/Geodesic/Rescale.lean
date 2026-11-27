/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Scaling

/-!
# Geodesics and the exponential map under constant rescaling of a metric

Multiplying a Riemannian metric `g` on `M` by a positive constant `c` leaves the Levi-Civita
connection unchanged on differentiable vector fields (`leviCivitaConnection_rescale_const_apply`),
and therefore leaves Christoffel maps, along-curve covariant derivatives, covariant acceleration,
geodesics, the geodesic spray, maximal geodesic intervals, maximal geodesics, `expDomain`, and
`riemannianExp` unchanged.

## Main results

* `Bundle.ContMDiffRiemannianMetric.isGeodesicCurveOn_rescale_const_iff`,
  `Bundle.ContMDiffRiemannianMetric.geodesicSpray_rescale_const`,
  `Bundle.ContMDiffRiemannianMetric.geodesicInterval_rescale_const`,
  `Bundle.ContMDiffRiemannianMetric.maximalGeodesic_rescale_const`,
  `Bundle.ContMDiffRiemannianMetric.expDomain_rescale_const`,
  `Bundle.ContMDiffRiemannianMetric.riemannianExp_rescale_const`: invariance under `g ↦ c g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Chapter 4.
-/

public section

open Bundle CovariantDerivative Module Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section GeodesicEquation

variable [IsManifold I 2 M] {n : ℕ∞ω}
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
  {c : ℝ} (hc : 0 < c)

/-- Multiplying a `C¹` metric by a positive constant does not change covariant differentiation
along a curve for the Levi-Civita connection. -/
theorem alongCurveWithin_leviCivitaConnection_rescale_const
    (γ : ℝ → M) (V : ∀ r, TangentSpace I (γ r)) (s : Set ℝ) (t : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      alongCurveWithin (leviCivitaConnection I M) γ V s t) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      alongCurveWithin (leviCivitaConnection I M) γ V s t) :=
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  alongCurveWithin_congr_covariantDerivative fun _ hY ↦
    leviCivitaConnection_rescale_const_apply g hn hc hY

/-- Multiplying a `C¹` metric by a positive constant does not change the covariant acceleration of
a curve for the Levi-Civita connection. -/
theorem accelerationWithin_leviCivitaConnection_rescale_const (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      accelerationWithin (leviCivitaConnection I M) γ s t) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      accelerationWithin (leviCivitaConnection I M) γ s t) :=
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  accelerationWithin_congr_covariantDerivative fun _ hY ↦
    leviCivitaConnection_rescale_const_apply g hn hc hY

/-- Multiplying a `C¹` metric by a positive constant does not change which curves are geodesics on
a parameter set. -/
theorem isGeodesicCurveOn_rescale_const_iff (γ : ℝ → M) (s : Set ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOn I γ s) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOn I γ s) := by
  have hacc := accelerationWithin_leviCivitaConnection_rescale_const g hn hc γ s
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨hu, hcγ, ha⟩ := h
  · let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hu, hcγ, fun r hr ↦ (hacc r).symm.trans (ha r hr)⟩
  · let _ : RiemannianBundle _ :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hu, hcγ, fun r hr ↦ (hacc r).trans (ha r hr)⟩

/-- Multiplying a `C¹` metric by a positive constant does not change all-time geodesics. -/
theorem isGeodesicCurve_rescale_const_iff (γ : ℝ → M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurve I γ) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurve I γ) := by
  simp only [← isGeodesicCurveOn_univ, isGeodesicCurveOn_rescale_const_iff g hn hc γ univ]

/-- Multiplying a `C¹` metric by a positive constant does not change geodesics with prescribed
initial data. -/
theorem isGeodesicCurveOnFrom_rescale_const_iff
    (γ : ℝ → M) (s : Set ℝ) (p : M) (v : TangentSpace I p) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOnFrom I γ s p v) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      IsGeodesicCurveOnFrom I γ s p v) := by
  have hgeo := isGeodesicCurveOn_rescale_const_iff g hn hc γ s
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨hγ, h0, hi⟩ := h
  · let _ : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hgeo.1 hγ, h0, hi⟩
  · let _ : RiemannianBundle _ :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hgeo.2 hγ, h0, hi⟩

/-- Multiplying a `C¹` metric by a positive constant leaves the geodesic spray unchanged. -/
theorem geodesicSpray_rescale_const :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      geodesicSpray I M) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      geodesicSpray I M) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  funext z; simp only [geodesicSpray_apply]
  exact congrArg (fun Γ : E →L[ℝ] E →L[ℝ] E ↦ (z.snd, -Γ z.snd z.snd))
    (christoffelMap_congr (finBasis ℝ E) _ _ fun _ _ hY ↦
      leviCivitaConnection_rescale_const_apply g hn hc hY)

end GeodesicEquation

section Exponential

variable [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {c : ℝ} (hc : 0 < c)

/-- Multiplying a smooth metric by a positive constant leaves maximal geodesic intervals
unchanged. -/
theorem geodesicInterval_rescale_const (p : M) (v : TangentSpace I p) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      geodesicInterval I M p v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      geodesicInterval I M p v) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  ext t; simp [mem_geodesicInterval_iff, isGeodesicCurveOnFrom_rescale_const_iff g (by simp) hc]

/-- Multiplying a smooth metric by a positive constant leaves maximal geodesics unchanged. -/
theorem maximalGeodesic_rescale_const (p : M) (v : TangentSpace I p) (t : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      maximalGeodesic I M p v t) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      maximalGeodesic I M p v t) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  simp only [maximalGeodesic_def, geodesicSpray_rescale_const g (by simp) hc]

/-- Multiplying a smooth metric by a positive constant leaves the natural domain of the Riemannian
exponential map unchanged. -/
theorem expDomain_rescale_const (p : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      expDomain I M p) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      expDomain I M p) := by
  ext v; simp only [mem_expDomain_iff, geodesicInterval_rescale_const g hc]

/-- Multiplying a smooth metric by a positive constant does not change geodesic completeness at a
point. -/
theorem isGeodesicallyCompleteAt_rescale_const_iff (p : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      IsGeodesicallyCompleteAt I M p) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      IsGeodesicallyCompleteAt I M p) := by
  simp only [← expDomain_eq_univ_iff, expDomain_rescale_const g hc]

/-- Multiplying a smooth metric by a positive constant leaves the Riemannian exponential map
unchanged. -/
theorem riemannianExp_rescale_const (p : M) (v : TangentSpace I p) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      riemannianExp I M p v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianExp I M p v) := by
  simp only [riemannianExp_def, maximalGeodesic_rescale_const g hc]

end Exponential

end Bundle.ContMDiffRiemannianMetric

end
