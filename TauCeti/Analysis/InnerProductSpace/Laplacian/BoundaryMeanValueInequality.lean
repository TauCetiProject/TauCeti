/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.EvenReflection
public import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The mean-value inequality on half-discs with a Neumann condition

Let `x₀` be a point of the real axis and let `w ≥ 0` be `C²` on the half-disc
`{0 ≤ im z} ∩ ball x₀ r`, up to its straight edge, with

`Δ w ≥ -A w²` above the axis and `∂ₜ w = 0` on the axis.

The **boundary mean-value inequality** says that if the integral of `w` over the half-disc is
small, `16 A ∫ w < π`, then

`π r² w x₀ ≤ 16 ∫_{{0 ≤ im z} ∩ ball x₀ r} w`.

The proof reflects `w` evenly across the real axis (`TauCeti.evenReflection`). The Neumann
condition makes the reflection `C²` on the whole disc (`TauCeti.contDiffOn_evenReflection`); its
Laplacian satisfies the same inequality, off the axis because conjugation is an isometry and on
the axis by continuity; and its integral over the disc is at most twice that of `w` over the
half-disc. The interior mean-value inequality
`TauCeti.mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian` then applies to the
reflection, centred at the boundary point `x₀`.

In Gromov compactness for holomorphic strips and discs with totally real boundary conditions,
`w` is the energy density `|∂ₛu|²` of a curve on a half-disc whose straight edge is mapped to the
totally real submanifold. For a metric adapted to the boundary condition this density satisfies
the hypotheses above, and the inequality gives the pointwise derivative bound at boundary points
for curves of small energy, the boundary counterpart of the interior estimate
`TauCeti.pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`. The geometric input,
the Neumann condition and differential inequality for the energy density, is not proved here.

## Main results

* `TauCeti.neg_mul_sq_le_laplacian_evenReflection`: the even reflection of `w` satisfies
  `Δ w ≥ -A w²` on the whole disc.
* `TauCeti.pi_mul_sq_mul_le_sixteen_mul_setIntegral_inter_ball_of_neg_mul_sq_le_laplacian`: **the
  boundary mean-value inequality**.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the mean-value inequality, and its version
  for half-discs proved by reflecting the energy density in the boundary).
-/

public section

namespace TauCeti

open Complex ComplexConjugate Filter InnerProductSpace Laplacian MeasureTheory Metric Real Set
  Topology

variable {w : ℂ → ℝ} {x₀ : ℂ} {r A : ℝ}

/-- If `w` is `C²` up to the real axis on a disc centred on the axis, satisfies the Neumann
condition on the axis and `Δ w ≥ -A w²` above it, then its even reflection satisfies
`Δ w ≥ -A w²` on the whole disc. -/
theorem neg_mul_sq_le_laplacian_evenReflection (hx₀ : x₀.im = 0)
    (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ ball x₀ r))
    (hN : ∀ x ∈ ball x₀ r, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ ball x₀ r) x I = 0)
    (hΔ : ∀ z ∈ ball x₀ r, 0 < z.im → -(A * w z ^ 2) ≤ Δ w z) {z : ℂ} (hz : z ∈ ball x₀ r) :
    -(A * evenReflection w z ^ 2) ≤ Δ (evenReflection w) z := by
  have hoff : ∀ y ∈ ball x₀ r, y.im ≠ 0 →
      -(A * evenReflection w y ^ 2) ≤ Δ (evenReflection w) y := by
    intro y hy hy0
    rcases hy0.lt_or_gt with hneg | hpos
    · rw [laplacian_evenReflection_of_neg hneg, evenReflection_of_nonpos hneg.le]
      exact hΔ _ (conj_mem_ball_of_im_eq_zero hx₀ hy) (by simpa using hneg)
    · rw [laplacian_evenReflection_of_pos hpos, evenReflection_of_nonneg hpos.le]
      exact hΔ y hy hpos
  rcases ne_or_eq z.im 0 with hz0 | hz0
  · exact hoff z hz hz0
  -- On the axis, pass to the limit along the points `z + t I`, `t > 0`, above it.
  have hreg : ContDiffOn ℝ 2 (evenReflection w) (ball x₀ r) :=
    contDiffOn_evenReflection isOpen_ball (fun y hy ↦ conj_mem_ball_of_im_eq_zero hx₀ hy) hw hN
  have hcont : ContinuousAt (fun y ↦ Δ (evenReflection w) y + A * evenReflection w y ^ 2) z :=
    ((hreg.continuousOn_laplacian isOpen_ball).add
      (continuousOn_const.mul (hreg.continuousOn.pow 2))).continuousAt (isOpen_ball.mem_nhds hz)
  have hlim : Tendsto (fun t : ℝ ↦ z + t * I) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous fun t : ℝ ↦ z + t * I := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : 0 ≤ Δ (evenReflection w) z + A * evenReflection w z ^ 2 := by
    refine ge_of_tendsto ((hcont.tendsto).comp hlim) ?_
    filter_upwards [self_mem_nhdsWithin, hlim (isOpen_ball.mem_nhds hz)] with t ht htz
    have := hoff _ htz (by simpa [hz0] using (ne_of_gt (show (0 : ℝ) < t from ht)))
    simp only [Function.comp_apply]
    linarith
  linarith

/-- The integral of the even reflection over a disc centred on the real axis is at most twice
the integral of `w ≥ 0` over the upper half-disc. -/
private theorem setIntegral_evenReflection_le (hx₀ : x₀.im = 0)
    (hwc : ContinuousOn w ({z | 0 ≤ z.im} ∩ closedBall x₀ r))
    (hw0 : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, 0 ≤ w z) :
    ∫ z in ball x₀ r, evenReflection w z ≤ 2 * ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z := by
  set P := {z : ℂ | 0 ≤ z.im}
  set N := {z : ℂ | z.im < 0}
  have hPm : MeasurableSet P := measurableSet_le measurable_const continuous_im.measurable
  have hNm : MeasurableSet N := measurableSet_lt continuous_im.measurable measurable_const
  have hint : IntegrableOn (evenReflection w) (ball x₀ r) :=
    ((continuousOn_evenReflection (fun y hy ↦ conj_mem_closedBall_of_im_eq_zero hx₀ hy)
      hwc).integrableOn_compact (isCompact_closedBall x₀ r)).mono_set ball_subset_closedBall
  have hwint : IntegrableOn w (P ∩ ball x₀ r) :=
    (hwc.integrableOn_compact ((isCompact_closedBall x₀ r).inter_left
      (isClosed_le continuous_const continuous_im))).mono_set
      (inter_subset_inter_right _ ball_subset_closedBall)
  have hsplit : ball x₀ r = (P ∩ ball x₀ r) ∪ (N ∩ ball x₀ r) := by
    rw [← union_inter_distrib_right, show P ∪ N = univ from
      eq_univ_of_forall fun z ↦ le_or_gt 0 z.im, univ_inter]
  have hdisj : Disjoint (P ∩ ball x₀ r) (N ∩ ball x₀ r) :=
    (disjoint_left.2 fun z (hP : 0 ≤ z.im) (hN : z.im < 0) ↦ hN.not_ge hP).mono
      inter_subset_left inter_subset_left
  have hunion : ∫ z in ball x₀ r, evenReflection w z = (∫ z in P ∩ ball x₀ r, evenReflection w z) +
      ∫ z in N ∩ ball x₀ r, evenReflection w z := by
    conv_lhs => rw [hsplit]
    exact setIntegral_union hdisj (hNm.inter measurableSet_ball)
      (hint.mono_set inter_subset_right) (hint.mono_set inter_subset_right)
  have hupper : ∫ z in P ∩ ball x₀ r, evenReflection w z = ∫ z in P ∩ ball x₀ r, w z :=
    setIntegral_congr_fun (hPm.inter measurableSet_ball) fun z hz ↦
      evenReflection_of_nonneg hz.1
  -- Below the axis, change variables by conjugation, which preserves the disc.
  have hpre : (conjLIE : ℂ → ℂ) ⁻¹' ({z : ℂ | 0 < z.im} ∩ ball x₀ r) = N ∩ ball x₀ r := by
    ext z
    refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨by simpa [N] using h₁, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨by simpa [N] using h₁, ?_⟩⟩
    · simpa using conj_mem_ball_of_im_eq_zero hx₀ h₂
    · simpa using conj_mem_ball_of_im_eq_zero hx₀ h₂
  have hlower : ∫ z in N ∩ ball x₀ r, evenReflection w z =
      ∫ z in {z : ℂ | 0 < z.im} ∩ ball x₀ r, w z := by
    rw [← hpre, ← conjLIE.measurePreserving.setIntegral_preimage_emb
      conjLIE.toHomeomorph.measurableEmbedding w]
    refine setIntegral_congr_fun
      (hpre ▸ hNm.inter measurableSet_ball) fun z hz ↦ evenReflection_of_nonpos ?_
    rw [hpre] at hz
    exact hz.1.le
  have hmono : ∫ z in {z : ℂ | 0 < z.im} ∩ ball x₀ r, w z ≤ ∫ z in P ∩ ball x₀ r, w z :=
    setIntegral_mono_set hwint
      ((ae_restrict_iff' (hPm.inter measurableSet_ball)).2 (Eventually.of_forall hw0))
      (Eventually.of_forall fun z hz ↦ ⟨by simpa [P] using le_of_lt hz.1, hz.2⟩)
  rw [hunion, hupper, hlower]
  linarith

/-- **The boundary mean-value inequality.** Let `x₀` lie on the real axis, and let `w ≥ 0` be
`C²` on the half-disc `{0 ≤ im z} ∩ ball x₀ r` up to its straight edge, continuous on its
closure, with `Δ w ≥ -A w²` above the axis and vanishing normal derivative `∂ₜ w = 0` on the
axis. If `16 A ∫ w < π` over the half-disc, then

`π r² w x₀ ≤ 16 ∫_{{0 ≤ im z} ∩ ball x₀ r} w`. -/
theorem pi_mul_sq_mul_le_sixteen_mul_setIntegral_inter_ball_of_neg_mul_sq_le_laplacian
    (hx₀ : x₀.im = 0) (hr : 0 ≤ r)
    (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ ball x₀ r))
    (hwc : ContinuousOn w ({z | 0 ≤ z.im} ∩ closedBall x₀ r))
    (hw0 : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, 0 ≤ w z)
    (hN : ∀ x ∈ ball x₀ r, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ ball x₀ r) x I = 0)
    (hΔ : ∀ z ∈ ball x₀ r, 0 < z.im → -(A * w z ^ 2) ≤ Δ w z)
    (hsmall : 16 * A * ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z < π) :
    π * r ^ 2 * w x₀ ≤ 16 * ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z := by
  have hsymm : ∀ y ∈ ball x₀ r, conj y ∈ ball x₀ r := fun y hy ↦
    conj_mem_ball_of_im_eq_zero hx₀ hy
  have hle := setIntegral_evenReflection_le hx₀ hwc hw0
  have hnonneg : 0 ≤ ∫ z in ball x₀ r, evenReflection w z := by
    refine setIntegral_nonneg measurableSet_ball fun z hz ↦ ?_
    rcases le_total 0 z.im with h | h
    · rw [evenReflection_of_nonneg h]
      exact hw0 z ⟨h, hz⟩
    · rw [evenReflection_of_nonpos h]
      exact hw0 _ ⟨by simpa using h, hsymm z hz⟩
  have hsmall' : 8 * A * ∫ z in ball x₀ r, evenReflection w z < π := by
    rcases le_total 0 A with hA | hA
    · nlinarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hA hnonneg, pi_pos]
  have h := mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian (μ := volume)
    (by simp) (w := evenReflection w) (x₀ := x₀) (r := r) (A := A)
    (contDiffOn_evenReflection isOpen_ball hsymm hw hN)
    (continuousOn_evenReflection (fun y hy ↦ conj_mem_closedBall_of_im_eq_zero hx₀ hy) hwc)
    (fun z hz ↦ by
      rcases le_total 0 z.im with h | h
      · rw [evenReflection_of_nonneg h]
        exact hw0 z ⟨h, hz⟩
      · rw [evenReflection_of_nonpos h]
        exact hw0 _ ⟨by simpa using h, hsymm z hz⟩)
    (fun z hz ↦ neg_mul_sq_le_laplacian_evenReflection hx₀ hw hN hΔ hz)
    (by simpa [measureReal_def, NNReal.coe_real_pi] using hsmall')
  rw [evenReflection_of_nonneg hx₀.ge] at h
  have h' : π * r ^ 2 * w x₀ ≤ 8 * ∫ z in ball x₀ r, evenReflection w z := by
    simpa [measureReal_def, hr, mul_comm, mul_left_comm, mul_assoc] using h
  linarith

end TauCeti
