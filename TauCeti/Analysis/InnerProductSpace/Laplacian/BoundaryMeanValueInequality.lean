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

Let `x₀` be a point of the closed upper half-plane and let `w ≥ 0` be `C²` on
`{0 ≤ im z} ∩ ball x₀ r`, up to the real axis, with

`Δ w ≥ -A w²` above the axis and `∂ₜ w = 0` on the axis.

The **boundary mean-value inequality** says that if the integral of `w` over
`{0 ≤ im z} ∩ ball x₀ r` is small, `16 A ∫ w < π`, then

`π r² w x₀ ≤ 16 ∫_{{0 ≤ im z} ∩ ball x₀ r} w`.

When the disc lies above the axis this is a weak form of the interior mean-value inequality; the
point is that the constants do not depend on the position of the disc relative to the axis, so
the estimate holds uniformly up to the boundary.

The proof reflects `w` evenly across the real axis (`TauCeti.evenReflection`). The disc
`ball x₀ r` and its mirror image `ball (conj x₀) r` meet the closed upper half-plane in the same
set `{0 ≤ im z} ∩ ball x₀ r`, since points of the closed upper half-plane are closer to `x₀` than
to `conj x₀` (`TauCeti.dist_le_dist_conj_of_im_nonneg`). The Neumann condition makes the reflection
`C²` on their union (`TauCeti.contDiffOn_evenReflection`); its Laplacian satisfies the same
inequality, off the axis because conjugation is an isometry and on the axis by continuity; and its
integral over `ball x₀ r` is at most twice that of `w` over `{0 ≤ im z} ∩ ball x₀ r`. The interior
mean-value inequality `TauCeti.mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian` then
applies to the reflection on `ball x₀ r`, or on any smaller disc `ball z ρ` inside it centred at
a point `z` of the closed upper half-plane, which bounds `π ρ² w z` in the same way. This is the
form needed near the edge, where points `z` close to the axis are not centres of half-discs but
lie in a small disc that may cross the axis.

In Gromov compactness for holomorphic strips and discs with totally real boundary conditions,
`w` is the energy density `|∂ₛu|²` of a curve on a half-disc whose straight edge is mapped to the
totally real submanifold. For a metric adapted to the boundary condition this density satisfies
the hypotheses above, and the inequality gives the pointwise derivative bound up to the boundary
for curves of small energy, the boundary counterpart of the interior estimate
`TauCeti.pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`. The geometric input,
the Neumann condition and differential inequality for the energy density, is not proved here.

## Main results

* `TauCeti.neg_mul_sq_le_laplacian_evenReflection`: on an open set invariant under conjugation,
  the even reflection of `w` satisfies `Δ w ≥ -A w²`.
* `TauCeti.pi_mul_sq_mul_le_sixteen_mul_setIntegral_inter_ball_of_neg_mul_sq_le_laplacian`: **the
  boundary mean-value inequality**, bounding `π ρ² w z` at any point `z` of the closed upper
  half-plane with `ball z ρ` inside the disc of the half-disc.

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

/-- Let `U` be an open set invariant under conjugation. If `w` is `C²` on `{0 ≤ im z} ∩ U`, up to
the real axis, satisfies the Neumann condition at the points of `U` on the axis and
`Δ w ≥ -A w²` above it, then its even reflection satisfies `Δ w ≥ -A w²` on `U`. -/
theorem neg_mul_sq_le_laplacian_evenReflection {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, conj z ∈ U) (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ U))
    (hN : ∀ x ∈ U, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U) x I = 0)
    (hΔ : ∀ z ∈ U, 0 < z.im → -(A * w z ^ 2) ≤ Δ w z) {z : ℂ} (hz : z ∈ U) :
    -(A * evenReflection w z ^ 2) ≤ Δ (evenReflection w) z := by
  have hoff : ∀ y ∈ U, y.im ≠ 0 →
      -(A * evenReflection w y ^ 2) ≤ Δ (evenReflection w) y := by
    intro y hy hy0
    rcases hy0.lt_or_gt with hneg | hpos
    · rw [laplacian_evenReflection_of_neg hneg, evenReflection_of_nonpos hneg.le]
      exact hΔ _ (hUc y hy) (by simpa using hneg)
    · rw [laplacian_evenReflection_of_pos hpos, evenReflection_of_nonneg hpos.le]
      exact hΔ y hy hpos
  rcases ne_or_eq z.im 0 with hz0 | hz0
  · exact hoff z hz hz0
  -- On the axis, pass to the limit along the points `z + t I`, `t > 0`, above it.
  have hreg : ContDiffOn ℝ 2 (evenReflection w) U := contDiffOn_evenReflection hU hUc hw hN
  have hcont : ContinuousAt (fun y ↦ Δ (evenReflection w) y + A * evenReflection w y ^ 2) z :=
    ((hreg.continuousOn_laplacian hU).add
      (continuousOn_const.mul (hreg.continuousOn.pow 2))).continuousAt (hU.mem_nhds hz)
  have hlim : Tendsto (fun t : ℝ ↦ z + t * I) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous fun t : ℝ ↦ z + t * I := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : 0 ≤ Δ (evenReflection w) z + A * evenReflection w z ^ 2 := by
    refine ge_of_tendsto ((hcont.tendsto).comp hlim) ?_
    filter_upwards [self_mem_nhdsWithin, hlim (hU.mem_nhds hz)] with t ht htz
    have := hoff _ htz (by simpa [hz0] using (ne_of_gt (show (0 : ℝ) < t from ht)))
    simp only [Function.comp_apply]
    linarith
  linarith

/-- For `x₀` in the closed upper half-plane, the even reflection of a function continuous on
`{0 ≤ im z} ∩ closedBall x₀ r` is continuous on `closedBall x₀ r`. -/
private theorem continuousOn_evenReflection_closedBall (hx₀ : 0 ≤ x₀.im)
    (hwc : ContinuousOn w ({z | 0 ≤ z.im} ∩ closedBall x₀ r)) :
    ContinuousOn (evenReflection w) (closedBall x₀ r) :=
  (continuousOn_evenReflection (s := closedBall x₀ r ∪ conj ⁻¹' closedBall x₀ r)
    (fun _ ↦ conj_mem_union_preimage_conj) (by
    rwa [setOfPred_le_im_inter_union_preimage_conj fun _ hz ↦
      mem_closedBall_of_conj_mem_closedBall_of_im_nonneg hx₀ hz])).mono subset_union_left

/-- For `x₀` in the closed upper half-plane, the integral of the even reflection over a disc about
`x₀` is at most twice the integral of `w ≥ 0` over the part of the disc in the closed upper
half-plane. -/
private theorem setIntegral_evenReflection_le (hx₀ : 0 ≤ x₀.im)
    (hwc : ContinuousOn w ({z | 0 ≤ z.im} ∩ closedBall x₀ r))
    (hw0 : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, 0 ≤ w z) :
    ∫ z in ball x₀ r, evenReflection w z ≤ 2 * ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z := by
  set P := {z : ℂ | 0 ≤ z.im}
  set N := {z : ℂ | z.im < 0}
  have hPm : MeasurableSet P := measurableSet_le measurable_const continuous_im.measurable
  have hNm : MeasurableSet N := measurableSet_lt continuous_im.measurable measurable_const
  have hint : IntegrableOn (evenReflection w) (ball x₀ r) :=
    ((continuousOn_evenReflection_closedBall hx₀ hwc).integrableOn_compact
      (isCompact_closedBall x₀ r)).mono_set ball_subset_closedBall
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
  -- Below the axis, change variables by conjugation, which maps the disc to its mirror image,
  -- whose part above the axis lies in the disc.
  set M := {z : ℂ | 0 < z.im} ∩ conj ⁻¹' ball x₀ r
  have hpre : (conjLIE : ℂ → ℂ) ⁻¹' M = N ∩ ball x₀ r := by
    ext z
    simp [M, N]
  have hlower : ∫ z in N ∩ ball x₀ r, evenReflection w z = ∫ z in M, w z := by
    rw [← hpre, ← conjLIE.measurePreserving.setIntegral_preimage_emb
      conjLIE.toHomeomorph.measurableEmbedding w]
    refine setIntegral_congr_fun
      (hpre ▸ hNm.inter measurableSet_ball) fun z hz ↦ evenReflection_of_nonpos ?_
    rw [hpre] at hz
    exact hz.1.le
  have hmono : ∫ z in M, w z ≤ ∫ z in P ∩ ball x₀ r, w z :=
    setIntegral_mono_set hwint
      ((ae_restrict_iff' (hPm.inter measurableSet_ball)).2 (Eventually.of_forall hw0))
      (Eventually.of_forall fun z hz ↦ ⟨mem_ofPred.2 (mem_ofPred.1 hz.1).le,
        mem_ball_of_conj_mem_ball_of_im_nonneg hx₀ (mem_ofPred.1 hz.1).le hz.2⟩)
  rw [hunion, hupper, hlower]
  linarith

/-- **The boundary mean-value inequality.** Let `x₀` lie in the closed upper half-plane, and let
`w ≥ 0` be `C²` on `{0 ≤ im y} ∩ ball x₀ r` up to the real axis, continuous on
`{0 ≤ im y} ∩ closedBall x₀ r`, with `Δ w ≥ -A w²` above the axis and vanishing normal derivative
`∂ₜ w = 0` on the axis. If `16 A ∫ w < π` over `{0 ≤ im y} ∩ ball x₀ r`, then every point `z` of
the closed upper half-plane and every disc `ball z ρ` contained in `ball x₀ r`, which may cross
the real axis, satisfy

`π ρ² w z ≤ 16 ∫_{{0 ≤ im y} ∩ ball x₀ r} w`.

In particular `π r² w x₀ ≤ 16 ∫_{{0 ≤ im y} ∩ ball x₀ r} w` at the centre. -/
theorem pi_mul_sq_mul_le_sixteen_mul_setIntegral_inter_ball_of_neg_mul_sq_le_laplacian
    (hx₀ : 0 ≤ x₀.im)
    (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ ball x₀ r))
    (hwc : ContinuousOn w ({z | 0 ≤ z.im} ∩ closedBall x₀ r))
    (hw0 : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, 0 ≤ w z)
    (hN : ∀ x ∈ ball x₀ r, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ ball x₀ r) x I = 0)
    (hΔ : ∀ z ∈ ball x₀ r, 0 < z.im → -(A * w z ^ 2) ≤ Δ w z)
    (hsmall : 16 * A * ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z < π)
    {z : ℂ} {ρ : ℝ} (hz : 0 ≤ z.im) (hρ : 0 ≤ ρ) (hzρ : ball z ρ ⊆ ball x₀ r) :
    π * ρ ^ 2 * w z ≤ 16 * ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z := by
  have hHm : MeasurableSet ({z : ℂ | 0 ≤ z.im} ∩ ball x₀ r) :=
    (measurableSet_le measurable_const continuous_im.measurable).inter measurableSet_ball
  have hI : 0 ≤ ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, w z := setIntegral_nonneg hHm hw0
  rcases hρ.eq_or_lt with rfl | hρ
  · simpa using hI
  -- Reflect `w` on the union `U` of the disc and its mirror image, which is invariant under
  -- conjugation and meets the closed upper half-plane in the half-disc.
  set U := ball x₀ r ∪ conj ⁻¹' ball x₀ r
  have hU : IsOpen U := isOpen_ball.union (isOpen_ball.preimage continuous_conj)
  have hUc : ∀ y ∈ U, conj y ∈ U := fun _ ↦ conj_mem_union_preimage_conj
  have hHU : {z : ℂ | 0 ≤ z.im} ∩ U = {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r :=
    setOfPred_le_im_inter_union_preimage_conj fun _ hz ↦
      mem_ball_of_conj_mem_ball_of_im_nonneg hx₀ hz
  have hUball : ∀ y ∈ U, 0 ≤ y.im → y ∈ ball x₀ r := fun y hy hy0 ↦
    (hHU.subset ⟨hy0, hy⟩).2
  have hwU : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ U) := by rwa [hHU]
  have hNU : ∀ x ∈ U, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U) x I = 0 :=
    fun x hx hx0 ↦ by rw [hHU]; exact hN x (hUball x hx hx0.ge) hx0
  have hcl : closedBall z ρ ⊆ closedBall x₀ r := by
    rw [← closure_ball z hρ.ne']
    exact (closure_mono hzρ).trans closure_ball_subset_closedBall
  have hrefl0 : ∀ y ∈ ball x₀ r, 0 ≤ evenReflection w y := fun y hy ↦ by
    rcases le_total 0 y.im with h | h
    · rw [evenReflection_of_nonneg h]
      exact hw0 y ⟨h, hy⟩
    · rw [evenReflection_of_nonpos h]
      have h' : 0 ≤ (conj y).im := by simpa using h
      exact hw0 _ ⟨h', hUball _ (hUc y (Or.inl hy)) h'⟩
  have hreflc : ContinuousOn (evenReflection w) (closedBall x₀ r) :=
    continuousOn_evenReflection_closedBall hx₀ hwc
  -- The integral of the reflection over the small disc is at most twice that of `w`.
  have hmono : ∫ y in ball z ρ, evenReflection w y ≤ ∫ y in ball x₀ r, evenReflection w y :=
    setIntegral_mono_set ((hreflc.integrableOn_compact (isCompact_closedBall x₀ r)).mono_set
      ball_subset_closedBall)
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall hrefl0))
      (Eventually.of_forall hzρ)
  have hle := hmono.trans (setIntegral_evenReflection_le hx₀ hwc hw0)
  have hnonneg : 0 ≤ ∫ y in ball z ρ, evenReflection w y :=
    setIntegral_nonneg measurableSet_ball fun y hy ↦ hrefl0 y (hzρ hy)
  have hsmall' : 8 * A * ∫ y in ball z ρ, evenReflection w y < π := by
    rcases le_total 0 A with hA | hA
    · nlinarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hA hnonneg, pi_pos]
  have h := mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian (μ := volume)
    (by simp) (w := evenReflection w) (x₀ := z) (r := ρ) (A := A)
    ((contDiffOn_evenReflection hU hUc hwU hNU).mono (hzρ.trans subset_union_left))
    (hreflc.mono hcl) (fun y hy ↦ hrefl0 y (hzρ hy))
    (fun y hy ↦ neg_mul_sq_le_laplacian_evenReflection hU hUc hwU hNU
      (fun y hy hy0 ↦ hΔ y (hUball y hy hy0.le) hy0) (Or.inl (hzρ hy)))
    (by simpa [measureReal_def, NNReal.coe_real_pi] using hsmall')
  rw [evenReflection_of_nonneg hz] at h
  have h' : π * ρ ^ 2 * w z ≤ 8 * ∫ y in ball z ρ, evenReflection w y := by
    simpa [measureReal_def, hρ.le, mul_comm, mul_left_comm, mul_assoc] using h
  linarith


end TauCeti
