/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.InteriorLp
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Quantitative Sobolev bounds for weakly harmonic remainders

A weakly harmonic real function has the native harmonic representative given by Weyl's lemma.
On a smaller ball its values and actual derivative are bounded by the outer `L¹` norm, and
its restriction is represented in the native `W1p` space with the corresponding norm bound.
This supplies the harmonic-remainder step of local divergence-form Laplace regularity.

The classical estimates allow Banach coefficients. For the weak representative and bundled `W1p`
statements here, the existing finite-dimensional Weyl theorem is specialized to real coefficients
to match the real-valued native Sobolev carrier.

## References

* L. C. Evans, *Partial Differential Equations*, Sections 2.2.3 and 5.2.
-/

public noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped Topology NNReal ENNReal Gradient ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- The native harmonic representative of a weakly harmonic real function has uniform value
and actual derivative bounds on an inner ball, controlled only by the outer `L¹` norm. -/
theorem WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_norm_and_norm_fderiv_le_integral_norm
    (c : E) {r R : ℝ} (hrR : r < R) (hRΩ : ball c R ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ}, WeaklyHarmonicOn μ Ω u → IntegrableOn u (ball c R) μ →
      ∃ v : E → ℝ, HarmonicOnNhd v Ω ∧ u =ᵐ[μ.restrict Ω] v ∧
        ∀ x ∈ closedBall c r,
          ‖v x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ ∧
            ‖fderiv ℝ v x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ := by
  obtain ⟨C, hC⟩ := exists_norm_and_norm_fderiv_le_integral_norm_of_harmonicOnNhd
    (F := ℝ) (μ := μ) c hrR
  refine ⟨C, fun {u} hu hi ↦ ?_⟩
  obtain ⟨v, hv, huv⟩ := hu.exists_harmonicOnNhd_ae_eq
  have hae := ae_restrict_of_ae_restrict_of_subset hRΩ huv
  have hiV : IntegrableOn v (ball c R) μ := hi.congr hae
  have hI : (∫ z in ball c R, ‖v z‖ ∂μ) = ∫ z in ball c R, ‖u z‖ ∂μ :=
    integral_congr_ae (hae.mono fun _ h ↦ congrArg norm h.symm)
  refine ⟨v, hv, huv, fun x hx ↦ ?_⟩
  simpa only [hI] using hC (hv.mono hRΩ) hiV x hx

/-- On each inner ball, a weakly harmonic real function has an actual native Sobolev
representative in every `W^{1,p}`, with norm controlled by its outer `L¹` norm. The recorded
gradient is the classical gradient of its harmonic representative. -/
theorem WeaklyHarmonicOn.exists_W1p_value_ae_eq_norm_le_integral_norm
    (c : E) {r R : ℝ} (hrR : r < R) (hRΩ : ball c R ⊆ Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ}, WeaklyHarmonicOn μ Ω u → IntegrableOn u (ball c R) μ →
      ∃ v : E → ℝ, ∃ w : W1p μ (⟨ball c r, isOpen_ball⟩ : Opens E) p,
        HarmonicOnNhd v Ω ∧ u =ᵐ[μ.restrict Ω] v ∧
        W1p.value w =ᵐ[μ.restrict (ball c r)] u ∧
        W1p.gradient w =ᵐ[μ.restrict (ball c r)] ∇ v ∧
        ‖w‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ := by
  obtain ⟨C, hC⟩ :=
    WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_norm_and_norm_fderiv_le_integral_norm
      (μ := μ) c hrR hRΩ
  let V : ℝ := (measureUnivNNReal (μ.restrict (ball c r)) : ℝ≥0) ^ p.toReal⁻¹
  have hV : 0 ≤ V := by positivity
  refine ⟨(2 * V * C).toNNReal, fun {u} hu hi ↦ ?_⟩
  have : IsFiniteMeasure (μ.restrict (⟨ball c r, isOpen_ball⟩ : Opens E)) := by
    rw [Opens.coe_mk]
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨v, hv, huv, hN⟩ := hC hu hi
  have hsub : closedBall c r ⊆ Ω := (closedBall_subset_ball hrR).trans hRΩ
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    Ω.isOpen (hv.contDiffOn.of_le (by simp)) (isCompact_closedBall c r)
    ball_subset_closedBall hsub (mu := μ) (p := p) (Omega := ⟨ball c r, isOpen_ball⟩)
  have hwu : W1p.value w =ᵐ[μ.restrict (ball c r)] u := hwv.trans
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hsub) huv.symm)
  have hI : 0 ≤ ∫ z in ball c R, ‖u z‖ ∂μ := integral_nonneg fun z ↦ norm_nonneg (u z)
  have hb : ∀ᵐ x ∂μ.restrict (ball c r), ‖W1p.value w x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ := by
    filter_upwards [hwv, ae_restrict_mem measurableSet_ball] with x hx hxr
    rw [hx]
    exact (hN x (ball_subset_closedBall hxr)).1
  have hg : ∀ᵐ x ∂μ.restrict (ball c r),
      ‖W1p.gradient w x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ := by
    filter_upwards [hwg, ae_restrict_mem measurableSet_ball] with x hx hxr
    rw [hx, norm_gradient_eq_norm_fderiv]
    exact (hN x (ball_subset_closedBall hxr)).2
  refine ⟨v, w, hv, huv, hwu, hwg, ?_⟩
  calc
    ‖w‖ ≤ ‖W1p.value w‖ + ‖W1p.gradient w‖ := W1p.norm_le_norm_value_add_norm_gradient w
    _ ≤ V * (C * ∫ z in ball c R, ‖u z‖ ∂μ) + V * (C * ∫ z in ball c R, ‖u z‖ ∂μ) :=
      add_le_add (Lp.norm_le_of_ae_bound (mul_nonneg C.coe_nonneg hI) hb)
        (Lp.norm_le_of_ae_bound (mul_nonneg C.coe_nonneg hI) hg)
    _ = _ := by rw [Real.coe_toNNReal _ (by positivity)]; ring

/-- A weakly harmonic `Lᵠ` function has a native `W^{1,p}` representative on every inner ball,
with norm bounded by the outer `Lᵠ` norm. This includes the `1 ≤ p ≤ q` exponents needed for
the harmonic remainder of the divergence-form Laplace equation. -/
theorem WeaklyHarmonicOn.exists_W1p_value_ae_eq_norm_le_eLpNorm
    (c : E) {r R : ℝ} (hrR : r < R) (hRΩ : ball c R ⊆ Ω)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ}, WeaklyHarmonicOn μ Ω u → MemLp u q (μ.restrict (ball c R)) →
      ∃ v : E → ℝ, ∃ w : W1p μ (⟨ball c r, isOpen_ball⟩ : Opens E) p,
        HarmonicOnNhd v Ω ∧ u =ᵐ[μ.restrict Ω] v ∧
        W1p.value w =ᵐ[μ.restrict (ball c r)] u ∧
        W1p.gradient w =ᵐ[μ.restrict (ball c r)] ∇ v ∧
        ‖w‖ ≤ C * (eLpNorm u q (μ.restrict (ball c R))).toReal := by
  obtain ⟨C, hC⟩ := WeaklyHarmonicOn.exists_W1p_value_ae_eq_norm_le_integral_norm
    (μ := μ) c hrR hRΩ p
  let V : ℝ := (μ (ball c R) ^ (1 - 1 / q.toReal)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have : IsFiniteMeasure (μ.restrict (ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine ⟨C * V.toNNReal, fun {u} hu hi ↦ ?_⟩
  obtain ⟨v, w, hv, huv, hwu, hwg, hnorm⟩ := hC hu (hi.integrable Fact.out)
  have hI : (∫ z in ball c R, ‖u z‖ ∂μ) ≤
      V * (eLpNorm u q (μ.restrict (ball c R))).toReal := by
    have h := Lp.integral_norm_le_mul_norm (hi.toLp u)
    rw [integral_congr_ae (hi.coeFn_toLp.mono fun _ hx ↦ congrArg norm hx)] at h
    simpa only [Measure.restrict_apply_univ, Lp.norm_toLp] using h
  refine ⟨v, w, hv, huv, hwu, hwg, hnorm.trans ?_⟩
  calc
    _ ≤ C * (V * (eLpNorm u q (μ.restrict (ball c R))).toReal) :=
      mul_le_mul_of_nonneg_left hI C.coe_nonneg
    _ = _ := by rw [NNReal.coe_mul, Real.coe_toNNReal _ hV]; ring

end TauCeti
