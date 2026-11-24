/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Variation
import TauCeti.Analysis.ODE.ScalarComparison

/-!
# Fixed-set volume comparison along Ricci flow

A lower scalar-curvature bound controls the growth of the native Riemannian volume
of any fixed measurable set. The metric family satisfies the Ricci equation using
its native Levi-Civita connections. Derivatives within the closed time interval
include its endpoints, and no completeness or finite-volume assumption is needed.

The argument first differentiates the relative volume density, compares it by an
integrating factor, and then uses the native change-of-metric measure identity.
This is the smooth-time volume-growth input to volume accounting for surgery.

## Main results

* `Bundle.ContMDiffRiemannianMetric.riemannianVolume_le_exp_neg_integral_of_scalarCurvature_ge`:
  a time-dependent scalar lower bound controls the volume of a fixed measurable set.
* `Bundle.ContMDiffRiemannianMetric.antitoneOn_riemannianVolume_of_scalarCurvature_nonneg`:
  nonnegative scalar curvature makes the volume of every fixed measurable set nonincreasing.
* `Bundle.ContMDiffRiemannianMetric.riemannianTotalVolume_le_exp_of_scalarCurvature_ge`:
  on a compact manifold, a constant scalar lower bound controls real total volume.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Chapter 13.
* P. Topping, *Lectures on the Ricci Flow* (2006), Section 2.3.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle Set MeasureTheory Riemannian.Tensor
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {n : ℕ∞ω}
  (g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- Along the native Ricci equation the relative volume density satisfies
`J' = -Scal(g) J`, for an arbitrary fixed reference metric. -/
theorem hasDerivWithinAt_relativeVolumeDensity_of_ricciFlow
    {s : Set ℝ} {t : ℝ} (x : M)
    (hg : ∀ v w, HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s t) :
    HasDerivWithinAt (fun τ ↦ relativeVolumeDensity g₀ (g τ) x)
      (-(g t).scalarCurvature x * relativeVolumeDensity g₀ (g t) x) s t := by
  let ρ (τ : ℝ) : ℝ :=
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g τ).toRiemannianMetric⟩
    TauCeti.chartVolumeDensity (I := I) x x
  let ρ₀ : ℝ := TauCeti.chartVolumeDensity (I := I)
    (TauCeti.WithMetric.toWithMetric g₀ x) (TauCeti.WithMetric.toWithMetric g₀ x)
  have heq (τ : ℝ) : relativeVolumeDensity g₀ (g τ) x = ρ τ / ρ₀ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g τ).toRiemannianMetric⟩
    rw [relativeVolumeDensity_eq_div_chartVolumeDensity g₀ (g τ) (mem_chart_source H x)]
    congr 1
    simp only [TauCeti.chartVolumeDensity_def, chartGramMatrix_toWithMetric, ρ]
    congr 2
    ext i j
    exact (chartGramMatrix_apply (I := I) (E := E) x x i j).symm
  have hd : HasDerivWithinAt ρ (-(g t).scalarCurvature x * ρ t) s t :=
    TauCeti.hasDerivWithinAt_chartVolumeDensity_of_ricciFlow x (mem_chart_source H x) hg
  simpa only [← heq, mul_div_assoc] using hd.div_const ρ₀

/-- A time-dependent scalar-curvature lower bound controls the relative volume
density across a closed interval. The bound is required only at interior times. -/
theorem relativeVolumeDensity_le_exp_neg_integral_of_scalarCurvature_ge
    {a b : ℝ} (hab : a ≤ b) (x : M)
    (hg : ∀ t ∈ Icc a b, ∀ v w,
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) (Icc a b) t)
    {q : ℝ → ℝ} (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hscalar : ∀ t ∈ Ioo a b, q t ≤ (g t).scalarCurvature x) :
    relativeVolumeDensity (g a) (g b) x ≤ Real.exp (-(∫ t in a..b, q t)) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :=
    hasDerivWithinAt_relativeVolumeDensity_of_ricciFlow (g a) x (hg t ht)
  have h := TauCeti.le_mul_exp_integral_of_deriv_le_mul hab
    (fun t ht ↦ (hd t ht).continuousWithinAt) hq.neg hqInt.neg
    (fun t ht ↦ (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht ↦ mul_le_mul_of_nonneg_right (neg_le_neg (hscalar t ht))
      (relativeVolumeDensity_nonneg (g a) (g t) x))
  simpa only [relativeVolumeDensity_self, one_mul, Pi.neg_apply,
    intervalIntegral.integral_neg] using h

section Measure

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

/-- A scalar-curvature lower bound controls the volume growth of every fixed
measurable set. The estimate holds for extended-real volumes and for included
flow endpoints, without compactness or completeness of the manifold. -/
theorem riemannianVolume_le_exp_neg_integral_of_scalarCurvature_ge
    {a b : ℝ} (hab : a ≤ b) {S : Set M} (hS : MeasurableSet S)
    (hg : ∀ t ∈ Icc a b, ∀ x ∈ S, ∀ v w,
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) (Icc a b) t)
    {q : ℝ → ℝ} (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hscalar : ∀ t ∈ Ioo a b, ∀ x ∈ S, q t ≤ (g t).scalarCurvature x) :
    TauCeti.riemannianVolume I (TauCeti.WithMetric (g b))
        (TauCeti.WithMetric.ofWithMetric ⁻¹' S) ≤
      ENNReal.ofReal (Real.exp (-(∫ t in a..b, q t))) *
        TauCeti.riemannianVolume I (TauCeti.WithMetric (g a))
          (TauCeti.WithMetric.ofWithMetric ⁻¹' S) := by
  have hSa := hS.preimage (TauCeti.WithMetric.measurableEmbedding_ofWithMetric (g a)).measurable
  have hSb := hS.preimage (TauCeti.WithMetric.measurableEmbedding_ofWithMetric (g b)).measurable
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity (g a) (g b),
    Measure.map_apply (TauCeti.WithMetric.measurableEmbedding_toWithMetric_ofWithMetric
      (g a) (g b)).measurable hSb]
  -- The change-of-metric map is toWithMetric (g b) ∘ ofWithMetric and preserves the
  -- underlying point, so its pullback of the fixed set is ofWithMetric ⁻¹' S.
  -- This definitional conversion exposes that set before applying withDensity_apply.
  change ((TauCeti.riemannianVolume I (TauCeti.WithMetric (g a))).withDensity
    (fun x ↦ ENNReal.ofReal (relativeVolumeDensity (g a) (g b) x.ofWithMetric)))
      (TauCeti.WithMetric.ofWithMetric ⁻¹' S) ≤ _
  rw [withDensity_apply _ hSa]
  calc
    _ ≤ ∫⁻ _ in TauCeti.WithMetric.ofWithMetric ⁻¹' S,
        ENNReal.ofReal (Real.exp (-(∫ t in a..b, q t)))
          ∂TauCeti.riemannianVolume I (TauCeti.WithMetric (g a)) := by
      apply setLIntegral_mono' hSa
      intro x hx
      exact ENNReal.ofReal_le_ofReal
        (relativeVolumeDensity_le_exp_neg_integral_of_scalarCurvature_ge hab x.ofWithMetric
          (fun t ht ↦ hg t ht _ hx) hq hqInt (fun t ht ↦ hscalar t ht _ hx))
    _ = _ := setLIntegral_const _ _

/-- A constant scalar-curvature lower bound gives an exponential fixed-set
volume-growth bound, with no sign restriction on the lower bound. -/
theorem riemannianVolume_le_exp_of_scalarCurvature_ge
    {a b L : ℝ} (hab : a ≤ b) {S : Set M} (hS : MeasurableSet S)
    (hg : ∀ t ∈ Icc a b, ∀ x ∈ S, ∀ v w,
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) (Icc a b) t)
    (hscalar : ∀ t ∈ Ioo a b, ∀ x ∈ S, L ≤ (g t).scalarCurvature x) :
    TauCeti.riemannianVolume I (TauCeti.WithMetric (g b))
        (TauCeti.WithMetric.ofWithMetric ⁻¹' S) ≤
      ENNReal.ofReal (Real.exp (-L * (b - a))) *
        TauCeti.riemannianVolume I (TauCeti.WithMetric (g a))
          (TauCeti.WithMetric.ofWithMetric ⁻¹' S) := by
  simpa only [intervalIntegral.integral_const, smul_eq_mul, neg_mul, mul_comm L] using
    riemannianVolume_le_exp_neg_integral_of_scalarCurvature_ge hab hS hg
      continuousOn_const intervalIntegrable_const hscalar

/-- Nonnegative scalar curvature makes native volume nonincreasing for every
fixed measurable set, including sets of infinite volume. -/
theorem antitoneOn_riemannianVolume_of_scalarCurvature_nonneg
    {a b : ℝ} {S : Set M} (hS : MeasurableSet S)
    (hg : ∀ t ∈ Icc a b, ∀ x ∈ S, ∀ v w,
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) (Icc a b) t)
    (hscalar : ∀ t ∈ Ioo a b, ∀ x ∈ S, 0 ≤ (g t).scalarCurvature x) :
    AntitoneOn (fun t ↦ TauCeti.riemannianVolume I (TauCeti.WithMetric (g t))
      (TauCeti.WithMetric.ofWithMetric ⁻¹' S)) (Icc a b) := by
  intro s hs t ht hst
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have h := riemannianVolume_le_exp_of_scalarCurvature_ge hst hS
    (fun τ hτ x hx v w ↦ (hg τ (hsub hτ) x hx v w).mono hsub)
    (fun τ hτ ↦ hscalar τ ⟨hs.1.trans_lt hτ.1, hτ.2.trans_le ht.2⟩)
  simpa only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul] using h

end Measure

/-- On a compact manifold, a scalar lower bound controls the real total volume
across a Ricci-flow interval. In particular `Scal ≥ -C` gives growth at most
`exp(C (b-a))`, the estimate used in smooth-time volume accounting. -/
theorem riemannianTotalVolume_le_exp_of_scalarCurvature_ge [CompactSpace M]
    {a b L : ℝ} (hab : a ≤ b)
    (hg : ∀ t ∈ Icc a b, ∀ x : M, ∀ v w,
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) (Icc a b) t)
    (hscalar : ∀ t ∈ Ioo a b, ∀ x : M, L ≤ (g t).scalarCurvature x) :
    TauCeti.riemannianTotalVolume I (TauCeti.WithMetric (g b)) ≤
      Real.exp (-L * (b - a)) *
        TauCeti.riemannianTotalVolume I (TauCeti.WithMetric (g a)) := by
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  have h := riemannianVolume_le_exp_of_scalarCurvature_ge hab MeasurableSet.univ
    (fun t ht x _ ↦ hg t ht x) (fun t ht x _ ↦ hscalar t ht x)
  simp only [preimage_univ] at h
  simpa only [TauCeti.riemannianTotalVolume_def, Measure.real, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using
    ENNReal.toReal_mono (by finiteness) h

end Bundle.ContMDiffRiemannianMetric
