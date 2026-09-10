/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Edge
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The Schwarz--Christoffel vertex at infinity

The real axis is only part of the boundary of the upper half-plane: the prevertices divide it into
finitely many bounded intervals and two unbounded ones, and the two unbounded ones are a single
boundary arc through the point at infinity.  The polygon a Schwarz--Christoffel map is meant to
parametrize can therefore close up only if the map has a limit at infinity, and this file proves
that it does, under the hypothesis that the total turning exponent `∑ i, e i` is less than `-1`.
That hypothesis is the classical closing condition: for a bounded polygon with interior angles
`α i` and no prevertex at infinity, `e i = α i / π - 1` and the angle sum forces `∑ i, e i = -2`.

Far from all the prevertices, `dist z (a i)` is caught between `‖z‖ / 2` and `2 ‖z‖`, so the
integrand `∏ i, (z - a i) ^ (e i)` is dominated by `C * ‖z‖ ^ ∑ i, e i`
(`TauCeti.exists_norm_schwarzChristoffelIntegrand_le_of_le_norm`).  With `∑ i, e i < -1` that
dominating function is integrable along a vertical ray, and the map is estimated between any two
far-away points of the half-plane by running up a vertical ray from the first, across a horizontal
segment at the common height `‖z‖ + ‖w‖`, and back down to the second: all three pieces stay far
from the prevertices, and all three contributions are `O(R ^ (∑ i, e i + 1))` when both points have
norm at least `R`.  That is the Cauchy criterion along `cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet`, and
completeness of `ℂ` turns it into the limit `TauCeti.schwarzChristoffelVertexAtInfinity`.

The boundary consequence is `TauCeti.tendsto_nhds_schwarzChristoffelVertexAtInfinity`: any
family of boundary values of the map along the real axis converges to that same point as the
real parameter leaves every bounded set.  Applied to the two unbounded boundary intervals it says
that the two unbounded image edges run to one and the same point, which is what closes the
boundary path up into a polygon; identifying the closed path with a prescribed polygon, and the
image of the half-plane with its interior, is left to later work.

## Main definitions

* `TauCeti.schwarzChristoffelVertexAtInfinity` -- the boundary value of the Schwarz--Christoffel
  primitive at the point at infinity.

## Main results

* `TauCeti.exists_norm_schwarzChristoffelIntegrand_le_of_le_norm` -- far from every prevertex the
  integrand is dominated by a constant multiple of `‖z‖ ^ ∑ i, e i`.
* `TauCeti.tendsto_schwarzChristoffelPrimitive_atInfinity` -- the map converges to
  `schwarzChristoffelVertexAtInfinity` along the upper half-plane at infinity.
* `TauCeti.schwarzChristoffelVertexAtInfinity_change_base` -- changing the base point translates
  that boundary value by the same constant as every other one.
* `TauCeti.tendsto_nhds_schwarzChristoffelVertexAtInfinity` -- boundary values along the real axis
  converge to it, and hence
  `TauCeti.tendsto_limUnder_schwarzChristoffelPrimitive_atTop` and
  `TauCeti.tendsto_limUnder_schwarzChristoffelPrimitive_atBot`: the two unbounded image edges close
  up at one point.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

-- `open` before `namespace TauCeti`: inside it, `UpperHalfPlane` would resolve to the imported
-- `TauCeti.UpperHalfPlane` namespace instead of the root one.
open Bornology Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### The decay of the integrand at infinity -/

/-- **The Schwarz--Christoffel integrand decays like `‖z‖ ^ ∑ i, e i` at infinity.**  Once `‖z‖`
is large compared with the prevertices, every distance `dist z (a i)` lies between `‖z‖ / 2` and
`2 ‖z‖`, so each factor `dist z (a i) ^ e i` differs from `‖z‖ ^ e i` by at most the fixed factor
`2 ^ |e i|`. -/
theorem exists_norm_schwarzChristoffelIntegrand_le_of_le_norm (a e : ι → ℝ) :
    ∃ C > 0, ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖schwarzChristoffelIntegrand a e z‖ ≤ C * ‖z‖ ^ ∑ i, e i := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  set A : ℝ := ∑ i, |a i| with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨2 ^ ∑ i, |e i|, Real.rpow_pos_of_pos h2 _, 2 * A + 2, by linarith, fun z hz => ?_⟩
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have key : ∀ i, dist z (a i : ℂ) ^ e i ≤ 2 ^ |e i| * ‖z‖ ^ e i := by
    intro i
    have hai : |a i| ≤ A := by
      rw [hAdef]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    have hnorm : ‖((a i : ℝ) : ℂ)‖ = |a i| := by simp
    have hlow : ‖z‖ / 2 ≤ dist z (a i : ℂ) := by
      have h := norm_sub_norm_le z ((a i : ℝ) : ℂ)
      rw [hnorm] at h
      rw [dist_eq_norm]
      linarith
    have hhigh : dist z (a i : ℂ) ≤ 2 * ‖z‖ := by
      have h := norm_sub_le z ((a i : ℝ) : ℂ)
      rw [hnorm] at h
      rw [dist_eq_norm]
      linarith
    rcases le_or_gt 0 (e i) with he | he
    · calc dist z (a i : ℂ) ^ e i ≤ (2 * ‖z‖) ^ e i := Real.rpow_le_rpow dist_nonneg hhigh he
        _ = 2 ^ |e i| * ‖z‖ ^ e i := by rw [Real.mul_rpow h2.le hz0.le, abs_of_nonneg he]
    · calc dist z (a i : ℂ) ^ e i ≤ (‖z‖ / 2) ^ e i :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hlow he.le
        _ = 2 ^ |e i| * ‖z‖ ^ e i := by
            rw [Real.div_rpow hz0.le h2.le, abs_of_neg he, Real.rpow_neg h2.le]
            field_simp
  calc ‖schwarzChristoffelIntegrand a e z‖ = ∏ i, dist z (a i : ℂ) ^ e i :=
        norm_schwarzChristoffelIntegrand a e z
    _ ≤ ∏ i, (2 ^ |e i| * ‖z‖ ^ e i) :=
        Finset.prod_le_prod (fun i _ => Real.rpow_nonneg dist_nonneg _) fun i _ => key i
    _ = (2 ^ ∑ i, |e i|) * ‖z‖ ^ ∑ i, e i := by
        rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h2, ← Real.rpow_sum_of_pos hz0]

/-! ### Displacement along segments of the half-plane -/

/-- Displacement of the Schwarz--Christoffel primitive along a segment of the upper half-plane is
at most the integral of any integrable bound on the speed. -/
private theorem norm_schwarzChristoffelPrimitive_sub_le (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {α β : ℝ} (hab : α ≤ β) {c v : ℂ} {B : ℝ → ℝ}
    (hmem : ∀ s ∈ Icc α β, c + (s : ℂ) * v ∈ upperHalfPlaneSet)
    (hB : ∀ s ∈ Icc α β,
      ‖v‖ * ‖schwarzChristoffelIntegrand a e (c + (s : ℂ) * v)‖ ≤ B s)
    (hBi : IntervalIntegrable B volume α β) :
    ‖schwarzChristoffelPrimitive a e z₀ (c + (β : ℂ) * v) -
        schwarzChristoffelPrimitive a e z₀ (c + (α : ℂ) * v)‖ ≤ ∫ s in α..β, B s := by
  have hderiv : ∀ s ∈ Icc α β,
      HasDerivAt (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (c + (s : ℂ) * v))
        (v * schwarzChristoffelIntegrand a e (c + (s : ℂ) * v)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => c + (s : ℂ) * v) v s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const v).const_add c
    have h2 := hasDerivAt_schwarzChristoffelPrimitive a e z₀ (hmem s hs)
    simpa [Function.comp_def, smul_eq_mul] using h2.scomp s h1
  have hfc : ContinuousOn
      (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (c + (s : ℂ) * v)) (Icc α β) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ
      (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (c + (s : ℂ) * v)) (Ioo α β) :=
    fun s hs => (hderiv s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
  have hfB : ∀ᵐ t : ℝ, t ∈ Ioo α β →
      ‖deriv (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (c + (s : ℂ) * v)) t‖ ≤ B t :=
    .of_forall fun t ht => by
      rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv, norm_mul]
      exact hB t (Ioo_subset_Icc_self ht)
  exact norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd hfB hBi

/-- Running up the vertical ray from a far-away point `z` of the upper half-plane to the height
`T` moves the Schwarz--Christoffel primitive by `O (‖z‖ ^ (∑ i, e i + 1))`, uniformly in `T`.  The
ray stays at distance at least `(‖z‖ + s) / 2` from the origin, so the integrand is dominated
there by an integrable function of the height. -/
private theorem norm_schwarzChristoffelPrimitive_sub_le_vertical (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {C R : ℝ} (hC : 0 < C)
    (hbd : ∀ w : ℂ, R ≤ ‖w‖ → ‖schwarzChristoffelIntegrand a e w‖ ≤ C * ‖w‖ ^ ∑ i, e i)
    (hS : ∑ i, e i < -1) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hzR : R ≤ ‖z‖)
    {T : ℝ} (hT : z.im ≤ T) :
    ‖schwarzChristoffelPrimitive a e z₀ ((z.re : ℂ) + (T : ℂ) * Complex.I) -
        schwarzChristoffelPrimitive a e z₀ z‖
      ≤ C * 2 ^ (-∑ i, e i) / (-(∑ i, e i + 1)) * ‖z‖ ^ (∑ i, e i + 1) := by
  set S : ℝ := ∑ i, e i with hSdef
  have hS1 : S + 1 < 0 := by linarith
  have hzim : 0 < z.im := hz
  have hz0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hzim (le_trans (le_abs_self _) (abs_im_le_norm z))
  set β : ℝ := T - z.im with hβdef
  have hβ0 : 0 ≤ β := sub_nonneg.mpr hT
  set K : ℝ := C * 2 ^ (-S) with hKdef
  have hK : 0 < K := by positivity
  -- every point of the ray is far from the origin
  have him : ∀ s : ℝ, (z + (s : ℂ) * Complex.I).im = z.im + s := by
    intro s
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖z‖ ≤ ‖z + (s : ℂ) * Complex.I‖ := by
    intro s hs
    have hsq : ‖z‖ ^ 2 ≤ ‖z + (s : ℂ) * Complex.I‖ ^ 2 := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      nlinarith [hzim.le]
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  have hray : ∀ s ∈ Icc (0 : ℝ) β, (‖z‖ + s) / 2 ≤ ‖z + (s : ℂ) * Complex.I‖ := by
    intro s hs
    have h1 := hnorm s hs.1
    have h2 : s ≤ ‖z + (s : ℂ) * Complex.I‖ := by
      refine le_trans ?_ (le_trans (le_abs_self _) (abs_im_le_norm (z + (s : ℂ) * Complex.I)))
      rw [him s]
      linarith [hs.1, hzim.le]
    linarith
  have hmem : ∀ s ∈ Icc (0 : ℝ) β, z + (s : ℂ) * Complex.I ∈ upperHalfPlaneSet := by
    intro s hs
    simp only [upperHalfPlaneSet, Set.mem_ofPred_eq]
    rw [him s]
    linarith [hs.1]
  have hB : ∀ s ∈ Icc (0 : ℝ) β, ‖Complex.I‖ *
      ‖schwarzChristoffelIntegrand a e (z + (s : ℂ) * Complex.I)‖ ≤ K * (‖z‖ + s) ^ S := by
    intro s hs
    have hpos : (0 : ℝ) < (‖z‖ + s) / 2 := by linarith [hs.1]
    have hfar := hray s hs
    have h1 : ‖schwarzChristoffelIntegrand a e (z + (s : ℂ) * Complex.I)‖
        ≤ C * ‖z + (s : ℂ) * Complex.I‖ ^ S := hbd _ (hzR.trans (hnorm s hs.1))
    have h2 : ‖z + (s : ℂ) * Complex.I‖ ^ S ≤ ((‖z‖ + s) / 2) ^ S :=
      Real.rpow_le_rpow_of_nonpos hpos hfar (by linarith)
    have h3 : ((‖z‖ + s) / 2) ^ S = 2 ^ (-S) * (‖z‖ + s) ^ S := by
      rw [Real.div_rpow (by linarith [hs.1]) (by norm_num), Real.rpow_neg (by norm_num)]
      field_simp
    rw [Complex.norm_I, one_mul, hKdef]
    calc ‖schwarzChristoffelIntegrand a e (z + (s : ℂ) * Complex.I)‖
        ≤ C * ‖z + (s : ℂ) * Complex.I‖ ^ S := h1
      _ ≤ C * ((‖z‖ + s) / 2) ^ S := mul_le_mul_of_nonneg_left h2 hC.le
      _ = C * 2 ^ (-S) * (‖z‖ + s) ^ S := by rw [h3]; ring
  have hBi : IntervalIntegrable (fun s : ℝ => K * (‖z‖ + s) ^ S) volume 0 β := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hβ0]
    refine continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop) fun s hs => Or.inl ?_)
    have := hs.1
    linarith
  have hend : z + ((β : ℝ) : ℂ) * Complex.I = (z.re : ℂ) + (T : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, hβdef] <;> ring
  have hstart : z + ((0 : ℝ) : ℂ) * Complex.I = z := by simp
  have hmain := norm_schwarzChristoffelPrimitive_sub_le a e z₀ hβ0 hmem hB hBi
  rw [hend, hstart] at hmain
  refine hmain.trans ?_
  -- evaluate the dominating integral
  have hnotmem : (0 : ℝ) ∉ Set.uIcc (‖z‖ + 0) (‖z‖ + β) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact fun hmem => absurd hmem.1 (not_le.mpr (by linarith))
  have hint : (∫ s in (0 : ℝ)..β, K * (‖z‖ + s) ^ S)
      = K * (((‖z‖ + β) ^ (S + 1) - (‖z‖ + 0) ^ (S + 1)) / (S + 1)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ S) ‖z‖,
      integral_rpow (Or.inr ⟨by linarith, hnotmem⟩)]
  rw [hint]
  have hp : 0 ≤ (‖z‖ + β) ^ (S + 1) := Real.rpow_nonneg (by linarith) _
  have hdiv : (‖z‖ + β) ^ (S + 1) / (S + 1) ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨hp, hS1.le⟩)
  have hstep : ((‖z‖ + β) ^ (S + 1) - (‖z‖ + 0) ^ (S + 1)) / (S + 1)
      ≤ ‖z‖ ^ (S + 1) / (-(S + 1)) := by
    rw [sub_div, div_neg, add_zero]
    linarith
  calc K * (((‖z‖ + β) ^ (S + 1) - (‖z‖ + 0) ^ (S + 1)) / (S + 1))
      ≤ K * (‖z‖ ^ (S + 1) / (-(S + 1))) := mul_le_mul_of_nonneg_left hstep hK.le
    _ = C * 2 ^ (-S) / (-(S + 1)) * ‖z‖ ^ (S + 1) := by rw [hKdef]; ring

/-- Crossing the upper half-plane along a horizontal segment at height `T` moves the
Schwarz--Christoffel primitive by at most `C * T ^ (∑ i, e i)` times the length of the segment:
every point of the segment has norm at least `T`. -/
private theorem norm_schwarzChristoffelPrimitive_sub_le_horizontal (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {C R : ℝ} (hC : 0 < C)
    (hbd : ∀ w : ℂ, R ≤ ‖w‖ → ‖schwarzChristoffelIntegrand a e w‖ ≤ C * ‖w‖ ^ ∑ i, e i)
    (hS : ∑ i, e i < -1) {T : ℝ} (hT : 0 < T) (hTR : R ≤ T) (x y : ℝ) :
    ‖schwarzChristoffelPrimitive a e z₀ ((y : ℂ) + (T : ℂ) * Complex.I) -
        schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ C * T ^ (∑ i, e i) * |y - x| := by
  set S : ℝ := ∑ i, e i with hSdef
  set c : ℂ := (x : ℂ) + (T : ℂ) * Complex.I with hcdef
  set v : ℂ := ((y - x : ℝ) : ℂ) with hvdef
  have him : ∀ s : ℝ, (c + (s : ℂ) * v).im = T := by
    intro s
    simp [hcdef, hvdef]
  have hfar : ∀ s : ℝ, T ≤ ‖c + (s : ℂ) * v‖ := fun s =>
    (him s).ge.trans ((le_abs_self _).trans (abs_im_le_norm (c + (s : ℂ) * v)))
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, c + (s : ℂ) * v ∈ upperHalfPlaneSet := by
    intro s _
    simp only [upperHalfPlaneSet, Set.mem_ofPred_eq]
    rw [him s]
    exact hT
  have hB : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖v‖ * ‖schwarzChristoffelIntegrand a e (c + (s : ℂ) * v)‖ ≤ |y - x| * (C * T ^ S) := by
    intro s _
    have hnv : ‖v‖ = |y - x| := by rw [hvdef, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖schwarzChristoffelIntegrand a e (c + (s : ℂ) * v)‖
        ≤ C * ‖c + (s : ℂ) * v‖ ^ S := hbd _ (hTR.trans (hfar s))
    have h2 : ‖c + (s : ℂ) * v‖ ^ S ≤ T ^ S :=
      Real.rpow_le_rpow_of_nonpos hT (hfar s) (by linarith)
    rw [hnv]
    exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hC.le))
      (abs_nonneg _)
  have hBi : IntervalIntegrable (fun _ : ℝ => |y - x| * (C * T ^ S)) volume 0 1 :=
    intervalIntegrable_const
  have hend : c + ((1 : ℝ) : ℂ) * v = (y : ℂ) + (T : ℂ) * Complex.I := by
    rw [hcdef, hvdef]
    push_cast
    ring
  have hstart : c + ((0 : ℝ) : ℂ) * v = c := by simp
  have hmain := norm_schwarzChristoffelPrimitive_sub_le a e z₀ zero_le_one hmem hB hBi
  rw [hend, hstart] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### The limit at infinity -/

/-- **The Schwarz--Christoffel primitive converges at infinity** when the total turning exponent
is less than `-1`.  The estimate runs from `z` up a vertical ray, across at the height
`‖z‖ + ‖w‖`, and down to `w`. -/
private theorem exists_tendsto_schwarzChristoffelPrimitive_atInfinity (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hS : ∑ i, e i < -1) :
    ∃ v : ℂ, Tendsto (schwarzChristoffelPrimitive a e z₀)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 v) := by
  obtain ⟨C, hC, R, hR, hbd⟩ := exists_norm_schwarzChristoffelIntegrand_le_of_le_norm a e
  set S : ℝ := ∑ i, e i with hSdef
  have hS1 : S + 1 < 0 := by linarith
  set D : ℝ := C * 2 ^ (-S) / (-(S + 1)) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact div_pos (by positivity) (by linarith)
  set M : ℝ := 2 * D + C with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  refine CompleteSpace.complete (f := map (schwarzChristoffelPrimitive a e z₀)
    (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)) ?_
  rw [Metric.cauchy_iff]
  refine ⟨map_neBot, fun ε hε => ?_⟩
  obtain ⟨R', hR'pos, hR'R, hR'ε⟩ : ∃ R', 0 < R' ∧ R ≤ R' ∧ M * R' ^ (S + 1) < ε := by
    set τ : ℝ := (ε / (2 * M)) ^ (S + 1)⁻¹ with hτdef
    have hτ : 0 < τ := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨max R τ, lt_of_lt_of_le hR (le_max_left _ _), le_max_left _ _, ?_⟩
    have h1 : (max R τ) ^ (S + 1) ≤ τ ^ (S + 1) :=
      Real.rpow_le_rpow_of_nonpos hτ (le_max_right _ _) hS1.le
    have h2 : τ ^ (S + 1) = ε / (2 * M) := by
      rw [hτdef, Real.rpow_inv_rpow (by positivity) hS1.ne]
    calc M * (max R τ) ^ (S + 1) ≤ M * (ε / (2 * M)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hM.le
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  refine ⟨schwarzChristoffelPrimitive a e z₀ '' ({z : ℂ | R' ≤ ‖z‖} ∩ upperHalfPlaneSet), ?_, ?_⟩
  · refine mem_map.mpr (mem_of_superset ?_ (subset_preimage_image _ _))
    exact inter_mem (mem_inf_of_left (eventually_cobounded_le_norm R'))
      (mem_inf_of_right (mem_principal_self _))
  rintro - ⟨z, hz, rfl⟩ - ⟨w, hw, rfl⟩
  set T : ℝ := ‖z‖ + ‖w‖ with hTdef
  have hzR' : R' ≤ ‖z‖ := hz.1
  have hwR' : R' ≤ ‖w‖ := hw.1
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hTR' : R' ≤ T := by rw [hTdef]; linarith
  have hzT : z.im ≤ T := by
    have := (le_abs_self z.im).trans (abs_im_le_norm z)
    rw [hTdef]; linarith
  have hwT : w.im ≤ T := by
    have := (le_abs_self w.im).trans (abs_im_le_norm w)
    rw [hTdef]; linarith
  -- the three legs of the path
  have hleg1 := norm_schwarzChristoffelPrimitive_sub_le_vertical a e z₀ hC hbd hS hz.2
    (hR'R.trans hzR') hzT
  have hleg3 := norm_schwarzChristoffelPrimitive_sub_le_vertical a e z₀ hC hbd hS hw.2
    (hR'R.trans hwR') hwT
  have hleg2 := norm_schwarzChristoffelPrimitive_sub_le_horizontal a e z₀ hC hbd hS hT0
    (hR'R.trans hTR') z.re w.re
  -- each leg is `O (R' ^ (S + 1))`
  have hdecay : ∀ r : ℝ, R' ≤ r → r ^ (S + 1) ≤ R' ^ (S + 1) :=
    fun r hr => Real.rpow_le_rpow_of_nonpos hR'pos hr hS1.le
  have hb1 : ‖schwarzChristoffelPrimitive a e z₀ ((z.re : ℂ) + (T : ℂ) * Complex.I) -
      schwarzChristoffelPrimitive a e z₀ z‖ ≤ D * R' ^ (S + 1) :=
    hleg1.trans (mul_le_mul_of_nonneg_left (hdecay _ hzR') hD.le)
  have hb3 : ‖schwarzChristoffelPrimitive a e z₀ ((w.re : ℂ) + (T : ℂ) * Complex.I) -
      schwarzChristoffelPrimitive a e z₀ w‖ ≤ D * R' ^ (S + 1) :=
    hleg3.trans (mul_le_mul_of_nonneg_left (hdecay _ hwR') hD.le)
  have hb2 : ‖schwarzChristoffelPrimitive a e z₀ ((w.re : ℂ) + (T : ℂ) * Complex.I) -
      schwarzChristoffelPrimitive a e z₀ ((z.re : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ C * R' ^ (S + 1) := by
    refine hleg2.trans ?_
    have hlen : |w.re - z.re| ≤ T := by
      have h1 := abs_le.mp (abs_re_le_norm z)
      have h2 := abs_le.mp (abs_re_le_norm w)
      rw [hTdef, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hTS : C * T ^ S * |w.re - z.re| ≤ C * T ^ S * T :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    have hTeq : T ^ S * T = T ^ (S + 1) := by
      rw [Real.rpow_add_one hT0.ne' S]
    calc C * T ^ S * |w.re - z.re| ≤ C * T ^ S * T := hTS
      _ = C * T ^ (S + 1) := by rw [mul_assoc, hTeq]
      _ ≤ C * R' ^ (S + 1) := mul_le_mul_of_nonneg_left (hdecay _ hTR') hC.le
  calc dist (schwarzChristoffelPrimitive a e z₀ z) (schwarzChristoffelPrimitive a e z₀ w)
      ≤ dist (schwarzChristoffelPrimitive a e z₀ z)
          (schwarzChristoffelPrimitive a e z₀ ((z.re : ℂ) + (T : ℂ) * Complex.I)) +
        dist (schwarzChristoffelPrimitive a e z₀ ((z.re : ℂ) + (T : ℂ) * Complex.I))
          (schwarzChristoffelPrimitive a e z₀ ((w.re : ℂ) + (T : ℂ) * Complex.I)) +
        dist (schwarzChristoffelPrimitive a e z₀ ((w.re : ℂ) + (T : ℂ) * Complex.I))
          (schwarzChristoffelPrimitive a e z₀ w) := dist_triangle4 _ _ _ _
    _ ≤ D * R' ^ (S + 1) + C * R' ^ (S + 1) + D * R' ^ (S + 1) := by
        rw [dist_eq_norm', dist_eq_norm', dist_eq_norm]
        exact add_le_add (add_le_add hb1 hb2) hb3
    _ = M * R' ^ (S + 1) := by rw [hMdef]; ring
    _ < ε := hR'ε

/-- The **Schwarz--Christoffel vertex at infinity**: the boundary value at the point at infinity
of the primitive normalized at `z₀`.  It is a genuine limit when the total turning exponent
`∑ i, e i` is less than `-1`, which is the classical condition for the image polygon to close
up. -/
def schwarzChristoffelVertexAtInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane) : ℂ :=
  limUnder (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (schwarzChristoffelPrimitive a e z₀)

/-- The Schwarz--Christoffel primitive converges to `schwarzChristoffelVertexAtInfinity` along the
upper half-plane at infinity. -/
theorem tendsto_schwarzChristoffelPrimitive_atInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hS : ∑ i, e i < -1) :
    Tendsto (schwarzChristoffelPrimitive a e z₀) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 (schwarzChristoffelVertexAtInfinity a e z₀)) := by
  obtain ⟨v, hv⟩ := exists_tendsto_schwarzChristoffelPrimitive_atInfinity a e z₀ hS
  rwa [schwarzChristoffelVertexAtInfinity, hv.limUnder_eq]

/-- Changing the base point translates the Schwarz--Christoffel vertex at infinity by the same
constant as every finite boundary value. -/
theorem schwarzChristoffelVertexAtInfinity_change_base (a e : ι → ℝ) (b c : UpperHalfPlane)
    (hS : ∑ i, e i < -1) :
    schwarzChristoffelVertexAtInfinity a e b
      = schwarzChristoffelVertexAtInfinity a e c - schwarzChristoffelPrimitive a e c b := by
  refine tendsto_nhds_unique (tendsto_schwarzChristoffelPrimitive_atInfinity a e b hS) ?_
  refine Tendsto.congr' ?_
    ((tendsto_schwarzChristoffelPrimitive_atInfinity a e c hS).sub tendsto_const_nhds)
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  exact (schwarzChristoffelPrimitive_change_base a e b c hz).symm

/-! ### Closing the boundary path up -/

/-- **Boundary values of the Schwarz--Christoffel map converge to its vertex at infinity.**  If
`L x` is the boundary value at the real point `x` — the limit of the map along the upper
half-plane at `x` — for all `x` in a filter along which `|x|` tends to infinity, then `L` tends to
`schwarzChristoffelVertexAtInfinity` along that filter. -/
theorem tendsto_nhds_schwarzChristoffelVertexAtInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hS : ∑ i, e i < -1) {l : Filter ℝ} {L : ℝ → ℂ}
    (hl : Tendsto (fun x : ℝ => |x|) l atTop)
    (hL : ∀ᶠ x in l, Tendsto (schwarzChristoffelPrimitive a e z₀)
      (𝓝[upperHalfPlaneSet] (((x : ℝ) : ℂ))) (𝓝 (L x))) :
    Tendsto L l (𝓝 (schwarzChristoffelVertexAtInfinity a e z₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hmem : schwarzChristoffelPrimitive a e z₀ ⁻¹'
      (Metric.closedBall (schwarzChristoffelVertexAtInfinity a e z₀) (ε / 2))
      ∈ cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet :=
    tendsto_schwarzChristoffelPrimitive_atInfinity a e z₀ hS
      (Metric.closedBall_mem_nhds _ (by positivity))
  obtain ⟨t₁, ht₁, t₂, ht₂, heq⟩ := Filter.mem_inf_iff.mp hmem
  obtain ⟨R, -, hRt₁⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp ht₁
  have hkey : ∀ z : ℂ, R ≤ ‖z‖ → z ∈ upperHalfPlaneSet →
      dist (schwarzChristoffelPrimitive a e z₀ z)
        (schwarzChristoffelVertexAtInfinity a e z₀) ≤ ε / 2 := by
    intro z hzR hzU
    have : z ∈ t₁ ∩ t₂ := ⟨hRt₁ hzR, ht₂ hzU⟩
    rw [← heq] at this
    exact this
  filter_upwards [hL, hl.eventually_ge_atTop (R + 1)] with x hx hxbig
  have hnb := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  have hnorm : ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((x : ℂ)), R ≤ ‖z‖ := by
    have hopen : {z : ℂ | R < ‖z‖} ∈ 𝓝 ((x : ℂ)) := by
      refine (isOpen_lt continuous_const continuous_norm).mem_nhds ?_
      have hnx : ‖((x : ℝ) : ℂ)‖ = |x| := by simp
      simp only [Set.mem_ofPred_eq, hnx]
      linarith
    filter_upwards [nhdsWithin_le_nhds hopen] with z hz using hz.le
  have hle : dist (L x) (schwarzChristoffelVertexAtInfinity a e z₀) ≤ ε / 2 := by
    refine le_of_tendsto (hx.dist tendsto_const_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, hnorm] with z hzU hzR
    exact hkey z hzR hzU
  linarith

/-- **The right-hand unbounded image edge of the Schwarz--Christoffel map runs to its vertex at
infinity.**  Beyond every prevertex the map has a boundary value at each real point, by the
straight-edge continuation, and those values converge to the vertex at infinity. -/
theorem tendsto_limUnder_schwarzChristoffelPrimitive_atTop (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hS : ∑ i, e i < -1) :
    Tendsto (fun x : ℝ => limUnder (𝓝[upperHalfPlaneSet] ((x : ℂ)))
        (schwarzChristoffelPrimitive a e z₀)) atTop
      (𝓝 (schwarzChristoffelVertexAtInfinity a e z₀)) := by
  refine tendsto_nhds_schwarzChristoffelVertexAtInfinity a e z₀ hS tendsto_abs_atTop_atTop ?_
  filter_upwards [eventually_gt_atTop (∑ i, |a i|)] with x hx
  have hle : ∀ i, a i ≤ ∑ j, |a j| := fun i => (le_abs_self (a i)).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i))
  obtain ⟨L, hL, -, -⟩ := exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀
    (p := ∑ i, |a i|) (q := x + 1) fun i _ hi => absurd hi.1 (not_lt.mpr (hle i))
  have hnb := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  have h := hL x ⟨hx, by linarith⟩
  rwa [h.limUnder_eq]

/-- **The left-hand unbounded image edge of the Schwarz--Christoffel map runs to its vertex at
infinity.**  Together with `tendsto_limUnder_schwarzChristoffelPrimitive_atTop` this closes the
boundary path up: the two unbounded image edges have one and the same endpoint. -/
theorem tendsto_limUnder_schwarzChristoffelPrimitive_atBot (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hS : ∑ i, e i < -1) :
    Tendsto (fun x : ℝ => limUnder (𝓝[upperHalfPlaneSet] ((x : ℂ)))
        (schwarzChristoffelPrimitive a e z₀)) atBot
      (𝓝 (schwarzChristoffelVertexAtInfinity a e z₀)) := by
  refine tendsto_nhds_schwarzChristoffelVertexAtInfinity a e z₀ hS tendsto_abs_atBot_atTop ?_
  filter_upwards [eventually_lt_atBot (-∑ i, |a i|)] with x hx
  have hle : ∀ i, -∑ j, |a j| ≤ a i := fun i => neg_le_of_neg_le
    ((neg_le_abs (a i)).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)))
  obtain ⟨L, hL, -, -⟩ := exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀
    (p := x - 1) (q := -∑ i, |a i|) fun i _ hi => absurd hi.2 (not_lt.mpr (hle i))
  have hnb := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  have h := hL x ⟨by linarith, hx⟩
  rwa [h.limUnder_eq]

end TauCeti
