/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Volume.Variation
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Integration of the conjugate heat equation along Ricci flow

The general volume differentiation theorem in `RicciFlow.Volume.Variation` gives
derivative `∫ (∂ₜu - Scal u) dV` against the evolving Riemannian volume. On a compact
manifold without boundary, the pairing derivative moves the Laplacian to the test
function and retains a term for the conjugate-heat residual. The equation
`∂ₜu = -Δu + Scal u` therefore
preserves total mass. Pairing such a solution with `v` gives derivative
`∫ (∂ₜv - Δv) u dV`, so heat solutions have
constant pairing and heat subsolutions have nonincreasing pairing with nonnegative densities.

All integrals use the native Riemannian volume at the corresponding time.
Only the monotonicity statement requires a nonnegative density. Time-set conclusions assume
continuity of the actual pairing on the set and the differential hypotheses only on its interior.
No orientation is needed.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapters 6–7.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle MeasureTheory Set Function
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {u : ℝ → M → ℝ} {t₀ : ℝ}

section Boundaryless

variable [I.Boundaryless]

/-- The pairing derivative along Ricci flow is the forward heat pairing plus the test
function paired with the conjugate-heat residual. Only the base-time slices need be `C²`. -/
theorem hasDerivAt_integral_mul_riemannianVolume_of_ricciFlow
    {v : ℝ → M → ℝ}
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hflow : ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t₀).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t₀)
    (hu : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t₀, x))
    (hv : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry v) (t₀, x))
    (hu₂ : ContMDiff I 𝓘(ℝ) 2 (u t₀)) (hv₂ : ContMDiff I 𝓘(ℝ) 2 (v t₀)) :
    HasDerivAt (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t)))
      ((∫ x, (deriv (fun t ↦ v t x.ofWithMetric) t₀ -
        Manifold.laplaceBeltrami I (v t₀ ∘ WithMetric.ofWithMetric) x) * u t₀ x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t₀))) +
        ∫ x, v t₀ x.ofWithMetric * (deriv (fun t ↦ u t x.ofWithMetric) t₀ +
          Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x -
          (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric)
          ∂riemannianVolume I (WithMetric (g t₀))) t₀ := by
  have h := hasDerivAt_integral_riemannianVolume_of_ricciFlow hg hflow
    (u := fun t x ↦ v t x * u t x) (fun x ↦ (hv x).mul (hu x))
  have hu' := hu₂.comp (WithMetric.contMDiff_ofWithMetric (g := g t₀))
  have hv' := hv₂.comp (WithMetric.contMDiff_ofWithMetric (g := g t₀))
  have hp := WithMetric.continuous_ofWithMetric (g := g t₀)
  have hdu := (continuous_deriv_slice_fst_of_contMDiffAt hu).comp hp
  have hdv := (continuous_deriv_slice_fst_of_contMDiffAt hv).comp hp
  have hscalar := (g t₀).continuous_scalarCurvature.comp hp
  let μ := riemannianVolume I (WithMetric (g t₀))
  have integrable {f : WithMetric (g t₀) → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₁ := integrable (hdv.mul hu'.continuous)
  have hi₂ := integrable ((Manifold.continuous_laplaceBeltrami hv').mul hu'.continuous)
  have hi₃ := integrable (hv'.continuous.mul (hdu.sub (hscalar.mul hu'.continuous)))
  have hi₄ := integrable (hv'.continuous.mul (Manifold.continuous_laplaceBeltrami hu'))
  have hgreen := Manifold.integral_mul_laplaceBeltrami_right_eq_left hv'
    (HasCompactSupport.of_compactSpace _) hu'
  simp only [Pi.mul_def, Pi.sub_def, Function.comp_apply] at hi₁ hi₂ hi₃ hi₄ hgreen
  have hprod (x : WithMetric (g t₀)) :
      deriv (fun t ↦ v t x.ofWithMetric * u t x.ofWithMetric) t₀ -
        (g t₀).scalarCurvature x.ofWithMetric * (v t₀ x.ofWithMetric * u t₀ x.ofWithMetric) =
      deriv (fun t ↦ v t x.ofWithMetric) t₀ * u t₀ x.ofWithMetric +
        v t₀ x.ofWithMetric * (deriv (fun t ↦ u t x.ofWithMetric) t₀ -
          (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) := by
    rw [deriv_fun_mul ((hv x.ofWithMetric).differentiableAt_slice_fst one_ne_zero)
      ((hu x.ofWithMetric).differentiableAt_slice_fst one_ne_zero)]
    ring
  have hres (x : WithMetric (g t₀)) :
      v t₀ x.ofWithMetric * (deriv (fun t ↦ u t x.ofWithMetric) t₀ +
        Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x -
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) =
      v t₀ x.ofWithMetric * (deriv (fun t ↦ u t x.ofWithMetric) t₀ -
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) +
        v t₀ x.ofWithMetric * Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x := by
    ring
  have heq : (∫ x : WithMetric (g t₀), deriv
      (fun t ↦ v t x.ofWithMetric * u t x.ofWithMetric) t₀ -
      (g t₀).scalarCurvature x.ofWithMetric * (v t₀ x.ofWithMetric * u t₀ x.ofWithMetric)
      ∂riemannianVolume I (WithMetric (g t₀))) =
      (∫ x, (deriv (fun t ↦ v t x.ofWithMetric) t₀ -
        Manifold.laplaceBeltrami I (v t₀ ∘ WithMetric.ofWithMetric) x) * u t₀ x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t₀))) +
        ∫ x, v t₀ x.ofWithMetric * (deriv (fun t ↦ u t x.ofWithMetric) t₀ +
          Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x -
          (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric)
          ∂riemannianVolume I (WithMetric (g t₀)) := by
    simp_rw [hprod, sub_mul, hres]
    rw [integral_add hi₁ hi₃, integral_sub hi₁ hi₂, integral_add hi₃ hi₄, hgreen]
    ring
  exact heq ▸ h

/-- **Duality for the heat and conjugate-heat operators.** Pairing a conjugate-heat
solution `u` with a test function `v` moves the spatial Laplacian onto `v`:
`d/dt ∫ v u dV = ∫ (∂ₜv - Δv) u dV`. Only the slices at the base time need be `C²`. -/
theorem hasDerivAt_integral_mul_riemannianVolume_of_conjugateHeat
    {v : ℝ → M → ℝ}
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hflow : ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t₀).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t₀)
    (hu : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t₀, x))
    (hv : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry v) (t₀, x))
    (hu₂ : ContMDiff I 𝓘(ℝ) 2 (u t₀)) (hv₂ : ContMDiff I 𝓘(ℝ) 2 (v t₀))
    (hheat : ∀ x : WithMetric (g t₀), deriv (fun t ↦ u t x.ofWithMetric) t₀ =
      -Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x +
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) :
    HasDerivAt (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t)))
      (∫ x, (deriv (fun t ↦ v t x.ofWithMetric) t₀ -
        Manifold.laplaceBeltrami I (v t₀ ∘ WithMetric.ofWithMetric) x) * u t₀ x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t₀))) t₀ := by
  have hres (x : WithMetric (g t₀)) :
      deriv (fun t ↦ u t x.ofWithMetric) t₀ +
        Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x -
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric = 0 := by
    rw [hheat x]
    ring
  simpa only [hres, mul_zero, integral_zero, add_zero] using
    hasDerivAt_integral_mul_riemannianVolume_of_ricciFlow hg hflow hu hv hu₂ hv₂

/-- On a compact manifold without boundary, a conjugate-heat solution along Ricci flow
has total mass derivative zero. No positivity or unit-mass normalization is assumed. -/
theorem hasDerivAt_integral_riemannianVolume_zero_of_conjugateHeat
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hflow : ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t₀).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t₀)
    (hu : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t₀, x))
    (hu₂ : ContMDiff I 𝓘(ℝ) 2 (u t₀))
    (hheat : ∀ x : WithMetric (g t₀), deriv (fun t ↦ u t x.ofWithMetric) t₀ =
      -Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x +
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) :
    HasDerivAt (fun t ↦ ∫ x, u t x.ofWithMetric ∂riemannianVolume I (WithMetric (g t)))
      0 t₀ := by
  simpa only [one_mul, deriv_const, comp_def, Manifold.laplaceBeltrami_const,
    sub_self, zero_mul, integral_zero] using
    hasDerivAt_integral_mul_riemannianVolume_of_conjugateHeat (v := fun _ _ ↦ 1)
      hg hflow hu (fun _ ↦ contMDiffAt_const) hu₂ contMDiff_const hheat

end Boundaryless

/-- A forward heat solution and a conjugate-heat solution have constant pairing against
the evolving Riemannian volume on any convex time set. Continuity is required through the endpoints;
the flow and heat equations are only assumed at interior times. Neither solution needs a sign. -/
theorem integral_mul_riemannianVolume_eq_of_heat_conjugateHeat [I.Boundaryless]
    {v : ℝ → M → ℝ} {s : Set ℝ} (hsc : Convex ℝ s)
    (hcont : ContinuousOn (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) s)
    (hg : ∀ t ∈ interior s, ∀ x : M,
      ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
          ((g p.1).inner p.2)) (t, x))
    (hflow : ∀ t ∈ interior s, ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t)
    (hu : ∀ t ∈ interior s, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t, x))
    (hv : ∀ t ∈ interior s, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry v) (t, x))
    (hu₂ : ∀ t ∈ interior s, ContMDiff I 𝓘(ℝ) 2 (u t))
    (hv₂ : ∀ t ∈ interior s, ContMDiff I 𝓘(ℝ) 2 (v t))
    (hheat : ∀ t ∈ interior s, ∀ x : WithMetric (g t), deriv (fun τ ↦ u τ x.ofWithMetric) t =
      -Manifold.laplaceBeltrami I (u t ∘ WithMetric.ofWithMetric) x +
        (g t).scalarCurvature x.ofWithMetric * u t x.ofWithMetric)
    (hvheat : ∀ t ∈ interior s, ∀ x : WithMetric (g t), deriv (fun τ ↦ v τ x.ofWithMetric) t =
      Manifold.laplaceBeltrami I (v t ∘ WithMetric.ofWithMetric) x)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (∫ x, v a x.ofWithMetric * u a x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g a))) =
      ∫ x, v b x.ofWithMetric * u b x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g b)) := by
  have hd (t : ℝ) (ht : t ∈ interior s) : HasDerivAt
      (fun τ ↦ ∫ x, v τ x.ofWithMetric * u τ x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g τ))) 0 t := by
    simpa only [hvheat t ht, sub_self, zero_mul, integral_zero] using
      hasDerivAt_integral_mul_riemannianVolume_of_conjugateHeat
        (hg t ht) (hflow t ht) (hu t ht) (hv t ht) (hu₂ t ht) (hv₂ t ht) (hheat t ht)
  have hdiff : DifferentiableOn ℝ
      (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t))) (interior s) :=
    fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg hsc hcont hdiff fun t ht ↦ (hd t ht).deriv.ge
  have hanti := antitoneOn_of_deriv_nonpos hsc hcont hdiff fun t ht ↦ (hd t ht).deriv.le
  rcases le_total a b with hab | hab
  · exact le_antisymm (hmono ha hb hab) (hanti ha hb hab)
  · exact (le_antisymm (hmono hb ha hab) (hanti hb ha hab)).symm

/-- Total mass is constant on a convex time set when it is continuous through its endpoints
and the Ricci-flow and conjugate-heat hypotheses hold at interior times. -/
theorem integral_riemannianVolume_eq_of_conjugateHeat [I.Boundaryless]
    {s : Set ℝ} (hsc : Convex ℝ s)
    (hcont : ContinuousOn (fun t ↦ ∫ x, u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) s)
    (hg : ∀ t ∈ interior s, ∀ x : M,
      ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
          ((g p.1).inner p.2)) (t, x))
    (hflow : ∀ t ∈ interior s, ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t)
    (hu : ∀ t ∈ interior s, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t, x))
    (hu₂ : ∀ t ∈ interior s, ContMDiff I 𝓘(ℝ) 2 (u t))
    (hheat : ∀ t ∈ interior s, ∀ x : WithMetric (g t), deriv (fun τ ↦ u τ x.ofWithMetric) t =
      -Manifold.laplaceBeltrami I (u t ∘ WithMetric.ofWithMetric) x +
        (g t).scalarCurvature x.ofWithMetric * u t x.ofWithMetric)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (∫ x, u a x.ofWithMetric ∂riemannianVolume I (WithMetric (g a))) =
      ∫ x, u b x.ofWithMetric ∂riemannianVolume I (WithMetric (g b)) := by
  simpa only [one_mul] using
    integral_mul_riemannianVolume_eq_of_heat_conjugateHeat (v := fun _ _ ↦ 1) hsc
      (by simpa only [one_mul] using hcont) hg hflow hu
      (fun _ _ _ ↦ contMDiffAt_const) hu₂ (fun _ _ ↦ contMDiff_const) hheat
      (fun _ _ _ ↦ by simp only [deriv_const, comp_def, Manifold.laplaceBeltrami_const]) ha hb

/-- Pairing a forward heat subsolution with a nonnegative conjugate-heat solution is
nonincreasing on any convex time set. Continuity is required through the endpoints; the
flow, PDE and sign hypotheses are only assumed at interior times. -/
theorem antitoneOn_integral_mul_riemannianVolume_of_conjugateHeat_of_heat_subsolution
    [I.Boundaryless]
    {v : ℝ → M → ℝ} {s : Set ℝ} (hsc : Convex ℝ s)
    (hcont : ContinuousOn (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) s)
    (hg : ∀ t ∈ interior s, ∀ x : M,
      ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
          ((g p.1).inner p.2)) (t, x))
    (hflow : ∀ t ∈ interior s, ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t)
    (hu : ∀ t ∈ interior s, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t, x))
    (hv : ∀ t ∈ interior s, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry v) (t, x))
    (hu₂ : ∀ t ∈ interior s, ContMDiff I 𝓘(ℝ) 2 (u t))
    (hv₂ : ∀ t ∈ interior s, ContMDiff I 𝓘(ℝ) 2 (v t))
    (hheat : ∀ t ∈ interior s, ∀ x : WithMetric (g t), deriv (fun τ ↦ u τ x.ofWithMetric) t =
      -Manifold.laplaceBeltrami I (u t ∘ WithMetric.ofWithMetric) x +
        (g t).scalarCurvature x.ofWithMetric * u t x.ofWithMetric)
    (hu₀ : ∀ t ∈ interior s, ∀ x, 0 ≤ u t x)
    (hvheat : ∀ t ∈ interior s, ∀ x : WithMetric (g t), deriv (fun τ ↦ v τ x.ofWithMetric) t ≤
      Manifold.laplaceBeltrami I (v t ∘ WithMetric.ofWithMetric) x) :
    AntitoneOn (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) s := by
  have hd (t : ℝ) (ht : t ∈ interior s) :=
    hasDerivAt_integral_mul_riemannianVolume_of_conjugateHeat
      (hg t ht) (hflow t ht) (hu t ht) (hv t ht) (hu₂ t ht) (hv₂ t ht) (hheat t ht)
  apply antitoneOn_of_deriv_nonpos hsc hcont
  · intro t ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t ht).deriv]
    exact integral_nonpos fun x ↦ mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hvheat t ht x))
      (hu₀ t ht x.ofWithMetric)

end TauCeti
