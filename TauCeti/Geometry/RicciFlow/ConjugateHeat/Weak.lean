/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ConjugateHeat.Basic
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weak identities for the conjugate heat equation

On a compact manifold without boundary, the classical conjugate heat equation is
equivalent to its differential pairing identity against every smooth spatial test.
The integrated adjoint identity includes both temporal boundary terms and gives
vanishing spacetime pairings for tests that vanish at the temporal endpoints.

The spatial operator and all measures are the native Laplace--Beltrami operator
and the Riemannian volumes of the evolving metrics. The differential
characterization is pointwise in time. The integrated statements assume continuity
of the pairing through the endpoints and integrability of the spatial integral
of the adjoint expression over time.

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
  [IsManifold I ∞ M] [I.Boundaryless]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {u : ℝ → M → ℝ} {t₀ : ℝ}

section Differential

variable
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

include hg hflow hu hu₂

/-- A conjugate-heat solution has the weak differential identity against every fixed `C²`
spatial test. Smoothness of the metric in space is encoded by its native metric type. -/
theorem hasDerivAt_integral_mul_of_conjugateHeat {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) 2 φ)
    (hheat : ∀ x : WithMetric (g t₀), deriv (fun t ↦ u t x.ofWithMetric) t₀ =
      -Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x +
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) :
    HasDerivAt (fun t ↦ ∫ x, φ x.ofWithMetric * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t)))
      (-(∫ x, Manifold.laplaceBeltrami I (φ ∘ WithMetric.ofWithMetric) x *
        u t₀ x.ofWithMetric ∂riemannianVolume I (WithMetric (g t₀)))) t₀ := by
  simpa only [deriv_const, zero_sub, neg_mul, integral_neg] using
    hasDerivAt_integral_mul_riemannianVolume_of_conjugateHeat
      hg hflow hu (v := fun _ ↦ φ)
      (fun x ↦ (hφ.of_le (by norm_num) x).comp (t₀, x) contMDiffAt_snd) hu₂ hφ hheat

private theorem integral_mul_residual_eq_zero_of_weak
    (hweak : ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ →
      HasDerivAt (fun t ↦ ∫ x, φ x.ofWithMetric * u t x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t)))
        (-(∫ x, Manifold.laplaceBeltrami I (φ ∘ WithMetric.ofWithMetric) x *
          u t₀ x.ofWithMetric ∂riemannianVolume I (WithMetric (g t₀)))) t₀)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    (∫ x : WithMetric (g t₀), φ x.ofWithMetric *
      (deriv (fun t ↦ u t x.ofWithMetric) t₀ +
        Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x -
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric)
      ∂riemannianVolume I (WithMetric (g t₀))) = 0 := by
  have hφ₂ := hφ.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)
  have hd := hasDerivAt_integral_mul_riemannianVolume_of_ricciFlow
    hg hflow hu (v := fun _ ↦ φ)
    (fun x ↦ (hφ₂.of_le (by norm_num) x).comp (t₀, x) contMDiffAt_snd) hu₂ hφ₂
  have heq := hd.unique (hweak φ hφ)
  simp only [deriv_const, zero_sub, neg_mul, integral_neg] at heq
  exact add_left_cancel (heq.trans (add_zero _).symm)

/-- The weak differential pairing against every smooth spatial test implies the classical
conjugate heat equation at that time. Full support of native Riemannian volume turns the
fundamental lemma's almost-everywhere conclusion into a pointwise equation. -/
theorem conjugateHeat_of_forall_hasDerivAt_integral_mul
    (hweak : ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ →
      HasDerivAt (fun t ↦ ∫ x, φ x.ofWithMetric * u t x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t)))
        (-(∫ x, Manifold.laplaceBeltrami I (φ ∘ WithMetric.ofWithMetric) x *
          u t₀ x.ofWithMetric ∂riemannianVolume I (WithMetric (g t₀)))) t₀) :
    ∀ x : WithMetric (g t₀), deriv (fun t ↦ u t x.ofWithMetric) t₀ =
      -Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x +
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric := by
  let r (x : WithMetric (g t₀)) := deriv (fun t ↦ u t x.ofWithMetric) t₀ +
    Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x -
      (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric
  have hdt := continuous_deriv_slice_fst_of_contMDiffAt hu
  have hu' := hu₂.comp (WithMetric.contMDiff_ofWithMetric (g := g t₀))
  have hr : Continuous r := ((hdt.comp WithMetric.continuous_ofWithMetric).add
    (Manifold.continuous_laplaceBeltrami hu')).sub
      (((g t₀).continuous_scalarCurvature.comp WithMetric.continuous_ofWithMetric).mul
        hu'.continuous)
  have hae : r =ᵐ[riemannianVolume I (WithMetric (g t₀))] 0 := by
    apply ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hr.locallyIntegrable
    intro ψ hψ _
    have hψ' := hψ.comp (WithMetric.contMDiff_toWithMetric (g := g t₀))
    simpa only [smul_eq_mul, r, comp_apply, WithMetric.toWithMetric_ofWithMetric] using
      integral_mul_residual_eq_zero_of_weak hg hflow hu hu₂ hweak hψ'
  intro x
  have hz := congrFun (Measure.eq_of_ae_eq hae hr continuous_zero) x
  dsimp only [r, Pi.zero_apply] at hz
  linarith

/-- At a fixed time, the classical conjugate heat equation is equivalent to its weak
differential identity against all smooth spatial tests. No density sign is required. -/
theorem conjugateHeat_iff_forall_hasDerivAt_integral_mul :
    (∀ x : WithMetric (g t₀), deriv (fun t ↦ u t x.ofWithMetric) t₀ =
      -Manifold.laplaceBeltrami I (u t₀ ∘ WithMetric.ofWithMetric) x +
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric) ↔
    ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ →
      HasDerivAt (fun t ↦ ∫ x, φ x.ofWithMetric * u t x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t)))
        (-(∫ x, Manifold.laplaceBeltrami I (φ ∘ WithMetric.ofWithMetric) x *
          u t₀ x.ofWithMetric ∂riemannianVolume I (WithMetric (g t₀)))) t₀ := by
  exact ⟨fun h φ hφ ↦ hasDerivAt_integral_mul_of_conjugateHeat hg hflow hu hu₂
    (hφ.of_le (by norm_num)) h,
    conjugateHeat_of_forall_hasDerivAt_integral_mul hg hflow hu hu₂⟩

end Differential

section Spacetime

variable {v : ℝ → M → ℝ} {a b : ℝ}
  (hg : ∀ t ∈ Ioo a b, ∀ x : M,
    ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t, x))
  (hflow : ∀ t ∈ Ioo a b, ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
    (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g t).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t)
  (hu : ∀ t ∈ Ioo a b, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t, x))
  (hv : ∀ t ∈ Ioo a b, ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry v) (t, x))
  (hu₂ : ∀ t ∈ Ioo a b, ContMDiff I 𝓘(ℝ) 2 (u t))
  (hv₂ : ∀ t ∈ Ioo a b, ContMDiff I 𝓘(ℝ) 2 (v t))
  (hheat : ∀ t ∈ Ioo a b, ∀ x : WithMetric (g t), deriv (fun τ ↦ u τ x.ofWithMetric) t =
    -Manifold.laplaceBeltrami I (u t ∘ WithMetric.ofWithMetric) x +
      (g t).scalarCurvature x.ofWithMetric * u t x.ofWithMetric)

include hg hflow hu hv hu₂ hv₂ hheat

/-- **Spacetime adjoint identity with temporal boundary terms.** The spatial and temporal
integrals are actual Riemannian and interval integrals. Integrability is required only of the
resulting spatial pairing; no separate integrability assumptions on its summands are needed.
The pairing is continuous on the closed interval, while the differential hypotheses only hold
on the open interval. -/
theorem integral_integral_mul_riemannianVolume_eq_sub_of_conjugateHeat
    (hab : a ≤ b)
    (hcont : ContinuousOn (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) (Icc a b))
    (hi : IntervalIntegrable (fun t ↦ ∫ x, (deriv (fun τ ↦ v τ x.ofWithMetric) t -
      Manifold.laplaceBeltrami I (v t ∘ WithMetric.ofWithMetric) x) * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) volume a b) :
    (∫ t in a..b, ∫ x, (deriv (fun τ ↦ v τ x.ofWithMetric) t -
      Manifold.laplaceBeltrami I (v t ∘ WithMetric.ofWithMetric) x) * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) =
    (∫ x, v b x.ofWithMetric * u b x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g b))) -
    ∫ x, v a x.ofWithMetric * u a x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g a)) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun t ht ↦ hasDerivAt_integral_mul_riemannianVolume_of_conjugateHeat
      (hg t ht) (hflow t ht) (hu t ht) (hv t ht) (hu₂ t ht) (hv₂ t ht) (hheat t ht)) hi

/-- A classical conjugate-heat solution annihilates the adjoint operator on every test
vanishing at the two temporal endpoints. Compact temporal support in the open interval is a
sufficient special case; no temporal compact-support condition is needed in this statement. -/
theorem integral_integral_mul_riemannianVolume_eq_zero_of_conjugateHeat
    (hab : a ≤ b)
    (hcont : ContinuousOn (fun t ↦ ∫ x, v t x.ofWithMetric * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) (Icc a b))
    (hi : IntervalIntegrable (fun t ↦ ∫ x, (deriv (fun τ ↦ v τ x.ofWithMetric) t -
      Manifold.laplaceBeltrami I (v t ∘ WithMetric.ofWithMetric) x) * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) volume a b)
    (ha : ∀ x, v a x = 0) (hb : ∀ x, v b x = 0) :
    (∫ t in a..b, ∫ x, (deriv (fun τ ↦ v τ x.ofWithMetric) t -
      Manifold.laplaceBeltrami I (v t ∘ WithMetric.ofWithMetric) x) * u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) = 0 := by
  rw [integral_integral_mul_riemannianVolume_eq_sub_of_conjugateHeat
    hg hflow hu hv hu₂ hv₂ hheat hab hcont hi]
  simp only [ha, hb, zero_mul, integral_zero, sub_self]

end Spacetime

end TauCeti
