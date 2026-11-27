/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential

/-!
# Scalar Hessians along curves

Twice differentiating a scalar function along a curve gives its Hessian on the velocity and
its differential on the acceleration. In particular the second derivative along a geodesic
is exactly the diagonal scalar Hessian.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold
open scoped ContDiff InnerProductSpace Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {γ : ℝ → M} {t : ℝ}

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
private theorem eventually_deriv_comp_curve_eq_inner_mgradient
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (γ t)) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    deriv (f ∘ γ) =ᶠ[𝓝 t]
      fun r ↦ inner ℝ (mgradient I f (γ r)) (curveVelocity I γ r) := by
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf
  have hγn := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hγ
  filter_upwards [hγ.continuousAt.tendsto.eventually hfn, hγn] with r hfr hγr
  rw [(hasDerivAt_comp_curve (hfr.mdifferentiableAt two_ne_zero)
    (hasMFDerivAt_curveVelocity (hγr.mdifferentiableAt two_ne_zero))).deriv,
    inner_mgradient]

/-- The scalar second derivative along a `C²` curve is its Hessian on the velocity plus its
differential on the acceleration. -/
theorem hasDerivAt_deriv_comp_curve
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (γ t)) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    HasDerivAt (deriv (f ∘ γ))
      (hessian I f (γ t) (curveVelocity I γ t) (curveVelocity I γ t) +
        mvfderiv I f (γ t) (acceleration (leviCivitaConnection I M) γ t)) t := by
  let _ : IsManifold I (1 + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hgrad := contMDiffAt_mgradient (I := I) (f := f) (n := 1)
    (by simpa only [one_add_one_eq_two] using hf)
  have hγd := hγ.mdifferentiableAt two_ne_zero
  have hG := hgrad.mdifferentiableAt (by simp) |>.comp t hγd
  have hGcoord := differentiableAt_sectionCoord γ (fun r ↦ mgradient I f (γ r)) hG
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hVcoord := hγ.differentiableAt_sectionCoord_curveVelocity (E := E)
  have hd := (isMetricCompatible_leviCivitaConnection I).hasDerivAt_inner_alongCurve
    hγd hGcoord hVcoord
  rw [alongCurve_pullback _ _ _ (hasMFDerivAt_curveVelocity hγd)
      (hgrad.mdifferentiableAt (by simp)), ← I.hessian_eq_inner_leviCivitaConnection_mgradient,
    ← acceleration_def, inner_mgradient] at hd
  exact hd.congr_of_eventuallyEq (eventually_deriv_comp_curve_eq_inner_mgradient hf hγ)

/-- At a point where the acceleration vanishes, the diagonal Hessian is the ordinary second
derivative along the curve. -/
theorem deriv_deriv_comp_curve_of_acceleration_eq_zero
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (γ t)) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (ha : acceleration (leviCivitaConnection I M) γ t = 0) :
    deriv (deriv (f ∘ γ)) t =
      hessian I f (γ t) (curveVelocity I γ t) (curveVelocity I γ t) := by
  simpa only [ha, map_zero, add_zero] using (hasDerivAt_deriv_comp_curve hf hγ).deriv

section Exponential

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {x : M}

/-- The second derivative of `s ↦ f (riemannianExp I M x (s • v))` at `s = 0` equals
the diagonal Hessian of `f` at the base point `x`. -/
theorem deriv_deriv_comp_riemannianExp (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v : TangentSpace I x) :
    deriv (deriv (fun s : ℝ ↦ f (riemannianExp I M x (s • v)))) 0 =
      hessian I f x v v := by
  let c := fun s : ℝ ↦ riemannianExp I M x (s • v)
  have hc : ContMDiffAt 𝓘(ℝ) I 2 c 0 :=
    (contMDiffAt_riemannianExp_smul_zero x v).of_le (by simp)
  have hceq : c = maximalGeodesic I M x v := funext fun s ↦ riemannianExp_smul x v s
  have ha : acceleration (leviCivitaConnection I M) c 0 = 0 := by
    rw [hceq]
    exact acceleration_maximalGeodesic_eq_zero (zero_mem_geodesicInterval (I := I) (v := v))
  have hz : c 0 = x := by simp [c]
  have hv : curveVelocity I c 0 = v := curveVelocity_riemannianExp_smul_zero x v
  have h := deriv_deriv_comp_curve_of_acceleration_eq_zero (by simpa only [hz] using hf) hc ha
  rw [hz, hv] at h
  simpa only [c, Function.comp_def] using h

end Exponential

end TauCeti.Manifold
