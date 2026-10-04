/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Logarithmic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Ray
import TauCeti.Algebra.BigOperators.Finset.Fiber
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Parallel ends of Schwarz--Christoffel boundaries

When the total turning exponent is `-1`, the Schwarz--Christoffel primitive has logarithmic
growth. Its two outer boundary edges are consequently parallel rays. This file identifies their
two affine lines from the logarithmic constant at infinity: the right ray lies on the horizontal
line through that constant, and the left ray lies on its translate by `pi * I`.

The separation by exactly `pi` is for the normalized primitive, whose integrand has leading
coefficient one at infinity. An affine postcomposition rotates and rescales both the direction
and the separation. These are the asymptotic data needed for Schwarz--Christoffel maps onto
polygonal domains with a parallel-sided end, such as a half-strip.

## Main results

* `TauCeti.tendsto_schwarzChristoffelBoundary_sub_log_atTop_of_sum_eq_neg_one` gives the
  logarithmic asymptotic on the right outer ray.
* `TauCeti.tendsto_schwarzChristoffelBoundary_sub_log_neg_atBot_of_sum_eq_neg_one` gives the
  logarithmic asymptotic on the left outer ray, including its `pi * I` displacement.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Far from the prevertices, a boundary value differs little from the value one unit directly
above it. This estimate is used to transfer the logarithmic asymptotic in the open half-plane to
the two outer boundary rays. -/
private theorem norm_schwarzChristoffelBoundary_sub_primitive_add_I_le
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) {C R : ℝ} (hC : 0 < C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ →
      ‖schwarzChristoffelIntegrand a e z‖ ≤ C * ‖z‖ ^ (-1 : ℝ))
    {x : ℝ} (hx : max R 1 ≤ |x|) :
    ‖schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I)‖ ≤ C / |x| := by
  have hxpos : 0 < |x| := zero_lt_one.trans_le ((le_max_right R 1).trans hx)
  have hxR : R ≤ |x| := (le_max_left R 1).trans hx
  let ε : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := by positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    simp only [ε]
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact (inv_le_one₀ hn).mpr (by norm_num)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpath : Tendsto (fun n => (x : ℂ) + (ε n : ℂ) * Complex.I) atTop
      (𝓝[upperHalfPlaneSet] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    convert (tendsto_const_nhds (x := (x : ℂ))).add
      (((Complex.continuous_ofReal.tendsto 0).comp hε).mul
        (tendsto_const_nhds (x := Complex.I))) using 1 <;> simp
    exact Eventually.of_forall fun n => by simpa [upperHalfPlaneSet] using hεpos n
  have hboundary := (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x
    (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite x)).comp hpath
  have hlimit := ((tendsto_const_nhds
    (x := schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I))).sub hboundary).norm
  have hle :
      ‖schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I) -
        schwarzChristoffelBoundary a e z₀ x‖ ≤ C / |x| :=
    le_of_tendsto hlimit (Eventually.of_forall fun n => by
      have hmem : ∀ s ∈ Icc (ε n) 1,
          (x : ℂ) + (s : ℂ) * Complex.I ∈ upperHalfPlaneSet := by
        intro s hs
        simpa [upperHalfPlaneSet] using lt_of_lt_of_le (hεpos n) hs.1
      have hnorm (s : ℝ) : |x| ≤ ‖(x : ℂ) + (s : ℂ) * Complex.I‖ := by
        simpa using abs_re_le_norm ((x : ℂ) + (s : ℂ) * Complex.I)
      have hB : ∀ s ∈ Icc (ε n) 1,
          ‖Complex.I‖ * ‖schwarzChristoffelIntegrand a e
            ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ C / |x| := by
        intro s _
        rw [norm_I, one_mul]
        calc
          ‖schwarzChristoffelIntegrand a e ((x : ℂ) + (s : ℂ) * Complex.I)‖
              ≤ C * ‖(x : ℂ) + (s : ℂ) * Complex.I‖ ^ (-1 : ℝ) :=
            hbound _ (hxR.trans (hnorm s))
          _ ≤ C * |x| ^ (-1 : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hxpos (hnorm s) (by norm_num)) hC.le
          _ = C / |x| := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      have hmove := norm_schwarzChristoffelPrimitive_sub_le_integral a e z₀ (hεle n) hmem hB
        intervalIntegrable_const
      simp only [ofReal_one, one_mul] at hmove
      have hmove' :
          ‖schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I) -
            schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + (ε n : ℂ) * Complex.I)‖
            ≤ C / |x| := by
        refine hmove.trans ?_
        rw [intervalIntegral.integral_const, smul_eq_mul]
        apply mul_le_of_le_one_left (div_nonneg hC.le hxpos.le)
        linarith [hεpos n]
      exact hmove')
  simpa only [norm_sub_rev] using hle

/-- On the right outer edge, the normalized Schwarz--Christoffel boundary has the asymptotic
`log x + c`, where `c` is its logarithmic constant at infinity. -/
theorem tendsto_schwarzChristoffelBoundary_sub_log_atTop_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = -1) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x - (Real.log x : ℂ))
      atTop (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀)) := by
  obtain ⟨C, hC, R, _, hbound⟩ := exists_norm_schwarzChristoffelIntegrand_le_of_le_norm a e
  have herror : Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (by
        filter_upwards [eventually_ge_atTop (max R 1)] with x hx
        have hx0 : 0 ≤ x := by linarith [le_max_right R 1]
        exact norm_schwarzChristoffelBoundary_sub_primitive_add_I_le a e z₀ hfinite hC
          (by simpa only [hsum] using hbound) (by simpa [abs_of_nonneg hx0] using hx))
    refine (tendsto_id.const_div_atTop C).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [id_eq, abs_of_nonneg hx]
  have hpath : Tendsto (fun x : ℝ => (x : ℂ) + Complex.I) atTop
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
    apply tendsto_inf.mpr
    refine ⟨(tendsto_add_const_cobounded Complex.I).comp
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ), Filter.tendsto_principal.mpr ?_⟩
    exact Eventually.of_forall fun x => by simp [upperHalfPlaneSet]
  have hremainder :=
    (tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e z₀ hsum).comp hpath
  have hsmall : Tendsto (fun x : ℝ => (1 : ℂ) + Complex.I / (x : ℂ)) atTop (𝓝 1) := by
    have h := (tendsto_inv_atTop_zero.ofReal.const_mul Complex.I).const_add (1 : ℂ)
    simpa [div_eq_mul_inv, Complex.ofReal_inv] using h
  have hlogSmall : Tendsto (fun x : ℝ => log ((1 : ℂ) + Complex.I / (x : ℂ)))
      atTop (𝓝 0) := by
    change Tendsto (log ∘ fun x : ℝ => (1 : ℂ) + Complex.I / (x : ℂ)) atTop (𝓝 0)
    simpa only [Complex.log_one] using
      (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp hsmall
  have hlog : Tendsto (fun x : ℝ => log ((x : ℂ) + Complex.I) - (Real.log x : ℂ))
      atTop (𝓝 0) := by
    refine hlogSmall.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hq : (1 : ℂ) + Complex.I / (x : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp [div_im, hx.ne'] at this
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show (x : ℂ) + Complex.I = (x : ℂ) * (1 + Complex.I / (x : ℂ)) by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hx0], log_ofReal_mul hx hq]
    ring
  have hinterior : Tendsto (fun x : ℝ => schwarzChristoffelPrimitive a e z₀
      ((x : ℂ) + Complex.I) - (Real.log x : ℂ)) atTop
      (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀)) := by
    simpa only [Function.comp_apply, sub_add_sub_cancel, add_zero] using hremainder.add hlog
  simpa only [sub_add_sub_cancel, zero_add] using herror.add hinterior

/-- On the left outer edge, the normalized Schwarz--Christoffel boundary has the asymptotic
`log (-x) + c + pi * I`. The extra term is the upper-half-plane boundary value of the principal
logarithm along the negative real axis. -/
theorem tendsto_schwarzChristoffelBoundary_sub_log_neg_atBot_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = -1) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x - (Real.log (-x) : ℂ))
      atBot (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀ + Real.pi * Complex.I)) := by
  obtain ⟨C, hC, R, _, hbound⟩ := exists_norm_schwarzChristoffelIntegrand_le_of_le_norm a e
  have herror : Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I)) atBot (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (by
        filter_upwards [eventually_le_atBot (-max R 1)] with x hx
        have hx0 : x ≤ 0 := by linarith [le_max_right R 1]
        exact norm_schwarzChristoffelBoundary_sub_primitive_add_I_le a e z₀ hfinite hC
          (by simpa only [hsum] using hbound)
          (by rw [abs_of_nonpos hx0]; linarith))
    have hzero := (tendsto_id.const_div_atTop C).comp Filter.tendsto_neg_atBot_atTop
    refine hzero.congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    simp only [Function.comp_apply, id_eq, abs_of_nonpos hx]
  have hpath : Tendsto (fun x : ℝ => (x : ℂ) + Complex.I) atBot
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
    apply tendsto_inf.mpr
    refine ⟨(tendsto_add_const_cobounded Complex.I).comp
      (RCLike.tendsto_ofReal_atBot_cobounded ℂ), Filter.tendsto_principal.mpr ?_⟩
    exact Eventually.of_forall fun x => by simp [upperHalfPlaneSet]
  have hremainder :=
    (tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e z₀ hsum).comp hpath
  let q : ℝ → ℂ := fun x => -1 + Complex.I / ((-x : ℝ) : ℂ)
  have hq : Tendsto q atBot (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hinv := (tendsto_inv_atTop_zero.comp Filter.tendsto_neg_atBot_atTop).ofReal
      have h := (hinv.const_mul Complex.I).const_add (-1 : ℂ)
      simpa [q, div_eq_mul_inv, Complex.ofReal_inv] using h
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
      rw [show (q x).im = -x / (x * x) by simp [q, Complex.div_im]]
      exact div_nonneg (neg_nonneg.mpr hx.le) (mul_self_nonneg x)
  have hlogSmall : Tendsto (fun x => log (q x)) atBot (𝓝 (Real.pi * Complex.I)) := by
    change Tendsto (log ∘ q) atBot (𝓝 (Real.pi * Complex.I))
    simpa only [norm_neg, norm_one, Real.log_one, ofReal_zero, zero_add] using
      (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp hq
  have hlog : Tendsto (fun x : ℝ => log ((x : ℂ) + Complex.I) -
      (Real.log (-x) : ℂ)) atBot (𝓝 (Real.pi * Complex.I)) := by
    refine hlogSmall.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    have hq0 : q x ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp [q, div_im, hx.ne] at this
    have hx0 : (((-x : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hx.ne)
    rw [show (x : ℂ) + Complex.I = ((-x : ℝ) : ℂ) * q x by
      dsimp only [q]
      rw [mul_add, mul_neg, mul_one, mul_div_cancel₀ _ hx0]
      simp, log_ofReal_mul (neg_pos.mpr hx) hq0]
    ring
  have hinterior : Tendsto (fun x : ℝ => schwarzChristoffelPrimitive a e z₀
      ((x : ℂ) + Complex.I) - (Real.log (-x) : ℂ)) atBot
      (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀ + Real.pi * Complex.I)) := by
    simpa only [Function.comp_apply, sub_add_sub_cancel] using hremainder.add hlog
  simpa only [sub_add_sub_cancel, zero_add] using herror.add hinterior

end TauCeti
