/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Trace
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Algebra.Group.Order
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Hopf's boundary-point lemma for weak supersolutions on an interval

Let `a < b`. This file proves Hopf's boundary-point lemma at the endpoint `a` for weak
supersolutions of the one-dimensional divergence-form equation

`(A u' + B u)' + C u' + D u ≤ 0` in `(a, b)`,

in the sign convention of Gilbarg–Trudinger, Chapter 8: `u ∈ H¹(a, b)` and

`∫ (A u' + B u) v' - (C u' + D u) v ≥ 0` for every nonnegative `v ∈ H¹₀(a, b)`.

The coefficient `A` is measurable with `λ ≤ A ≤ Λ` for some `λ > 0`, `B` is measurable and
bounded, `C ∈ L²(a, b)` and `D ∈ L¹(a, b)`; square integrability of `C` is what makes `C u' v`
integrable for `u ∈ H¹`. If the continuous representative `ū` of `u` vanishes at `a` and is
positive in `(a, b)`, then it leaves `a` at a positive linear rate: `ε t ≤ ū (a + t)` for some
`ε > 0` and all small `t > 0`, so that `liminf_{t ↓ 0} ū (a + t) / t > 0`.

No continuity of the coefficients and no sign condition on `B` or `D` is needed. In dimension
`n ≥ 2` the divergence-form lemma fails for bounded measurable coefficients, and Rosales proves it
for Hölder continuous principal coefficients; in one dimension the flux can be integrated
directly. Since `ū a = 0`, the sign of the zeroth-order terms plays no role, as for the classical
lemma `TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`. The flux
`A u' + B u` of a supersolution need not be continuous: `u = 1 - |x|` on `(-1, 1)` has `u'' ≤ 0`
and a jump in `u'`. The argument therefore works with a weighted flux that is antitone almost
everywhere.

## The argument

The drift `C u'` is absorbed by the integrating factor `E = exp (∫ₐ C / A)`, which is absolutely
continuous with `E' = (C / A) E`. Testing the inequality with `v = E ψ`, for a nonnegative
trapezoid `ψ` rising with slope `1 / ε` on `[x - ε, x]` and falling with slope `-1 / ε` on
`[y, y + ε]`, and integrating the zeroth-order term by parts shows that the weighted flux

`Ψ = E (A u' + B ū) - ∫ₐ E ū ((C / A) B - D)`

has average over `[x - ε, x]` at least its average over `[y, y + ε]` whenever `x ≤ y`. By
Lebesgue's differentiation theorem `Ψ` is antitone on a set of full measure. If `Ψ` stays above
some `m > 0` near `a`, then `u'` is bounded below by a positive constant near `a`, because the
integral term and `B ū` vanish at `a`, and integrating `u'` gives the conclusion. Otherwise
`Ψ ≤ 0` almost everywhere, so that `u' ≤ θ U` on `(a, a + r)`, where `U` is the maximum of `ū` on
`[a, a + r]` and `θ` depends only on the coefficients. Integrating up to a maximum point gives
`U ≤ r θ U`, which contradicts `U > 0` once `r θ < 1`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg`: **Hopf's lemma**
  for weak supersolutions on an interval, as a linear lower bound near the endpoint.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_integral_nonneg`: the derivative form, the right
  derivative of `ū` at `a` is positive where it exists.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical lemma) and Section 8.1 (weak supersolutions).
* C. Rosales, *Generalizing Hopf's boundary point lemma*, arXiv:1806.07003, Theorem 4.1 (the
  divergence-form lemma in dimension `n ≥ 2`).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.2 (one-dimensional Sobolev spaces).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open TauCeti.W1p

namespace TauCeti.PDE

variable {a b : ℝ}

/-! ### Trapezoidal test functions -/

/-- The trapezoid rising with slope `1 / ε` on `[x - ε, x]`, equal to `1` on `[x, y]` and
falling with slope `-1 / ε` on `[y, y + ε]` vanishes at `a` and `b`, and its derivative is
`ε⁻¹ (1_{(x - ε, x]} - 1_{(y, y + ε]})` almost everywhere. -/
private theorem exists_trapezoid {x y ε : ℝ} (hε : 0 < ε) (hax : a ≤ x - ε) (hxy : x ≤ y)
    (hyb : y + ε ≤ b) :
    ∃ ψ : ℝ → ℝ, AbsolutelyContinuousOnInterval ψ a b ∧ ψ a = 0 ∧ ψ b = 0 ∧ (∀ t, 0 ≤ ψ t) ∧
      ∀ᵐ t, HasDerivAt ψ (ε⁻¹ * ((Ioc (x - ε) x).indicator 1 t -
        (Ioc y (y + ε)).indicator 1 t)) t := by
  -- The ramp `max 0 (min (t - s) ε)` has derivative `1_{(s, s + ε]}` off `{s, s + ε}`.
  have hramp : ∀ s t, t ≠ s → t ≠ s + ε →
      HasDerivAt (fun r ↦ max 0 (min (r - s) ε)) ((Ioc s (s + ε)).indicator 1 t) t := by
    intro s t hts htsε
    rcases hts.lt_or_gt with h | h
    · have hev : (fun r ↦ max 0 (min (r - s) ε)) =ᶠ[𝓝 t] fun _ ↦ 0 := by
        filter_upwards [Iio_mem_nhds h] with r hr
        exact max_eq_left (min_le_of_left_le (by linarith [mem_Iio.1 hr]))
      rw [indicator_of_notMem fun hm : t ∈ Ioc s (s + ε) ↦ (hm.1.trans h).false]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
    rcases htsε.lt_or_gt with h' | h'
    · have hev : (fun r ↦ max 0 (min (r - s) ε)) =ᶠ[𝓝 t] fun r ↦ r - s := by
        filter_upwards [Ioo_mem_nhds h h'] with r hr
        rw [min_eq_left (by linarith [hr.2]), max_eq_right (by linarith [hr.1])]
      rw [indicator_of_mem (show t ∈ Ioc s (s + ε) from ⟨h, h'.le⟩), Pi.one_apply]
      exact ((hasDerivAt_id t).sub_const s).congr_of_eventuallyEq hev
    · have hev : (fun r ↦ max 0 (min (r - s) ε)) =ᶠ[𝓝 t] fun _ ↦ max 0 ε := by
        filter_upwards [Ioi_mem_nhds h'] with r hr
        rw [min_eq_right (by linarith [mem_Ioi.1 hr])]
      rw [indicator_of_notMem fun hm : t ∈ Ioc s (s + ε) ↦ (h'.trans_le hm.2).false]
      exact (hasDerivAt_const t _).congr_of_eventuallyEq hev
  have hd : ∀ t ∉ ({x - ε, x, y, y + ε} : Set ℝ),
      HasDerivAt (fun t ↦ ε⁻¹ * (max 0 (min (t - (x - ε)) ε) - max 0 (min (t - y) ε)))
        (ε⁻¹ * ((Ioc (x - ε) x).indicator 1 t - (Ioc y (y + ε)).indicator 1 t)) t := by
    intro t ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
    have h1 := hramp (x - ε) t ht.1 (by rw [sub_add_cancel]; exact ht.2.1)
    rw [sub_add_cancel] at h1
    exact (h1.sub (hramp y t ht.2.2.1 ht.2.2.2)).const_mul ε⁻¹
  have hcount : ({x - ε, x, y, y + ε} : Set ℝ).Countable := by simp
  have hind : ∀ s s' : ℝ, IntervalIntegrable ((Ioc s s').indicator (1 : ℝ → ℝ)) volume a b :=
    fun s s' ↦ (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
      (measurable_one.indicator measurableSet_Ioc).aestronglyMeasurable
      (ae_of_all _ fun t ↦ norm_indicator_le_norm_self _ _)
  refine ⟨_, ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
    (Continuous.continuousOn (by fun_prop)) hcount (fun t ht ↦ hd t ht.2)
    (((hind _ _).sub (hind _ _)).const_mul ε⁻¹), ?_, ?_, ?_, ?_⟩
  · rw [max_eq_left (min_le_of_left_le (by linarith)),
      max_eq_left (min_le_of_left_le (by linarith))]
    simp
  · rw [min_eq_right (by linarith), min_eq_right (by linarith)]
    simp
  · intro t
    exact mul_nonneg (inv_nonneg.2 hε.le)
      (sub_nonneg.2 (max_le_max le_rfl (min_le_min (by linarith) le_rfl)))
  · filter_upwards [compl_mem_ae_iff.2 (hcount.measure_zero volume)] with t ht
    exact hd t ht

/-- Pairing with the derivative of the trapezoid of `exists_trapezoid` takes the difference of
the integrals over the two ramps. -/
private theorem integral_trapezoid_mul {x y ε : ℝ} (hax : a ≤ x - ε) (hxy : x ≤ y)
    (hyb : y + ε ≤ b) (hε : 0 < ε) {Ψ : ℝ → ℝ} (hΨ : IntervalIntegrable Ψ volume a b) :
    ∫ t in a..b, ε⁻¹ * ((Ioc (x - ε) x).indicator 1 t - (Ioc y (y + ε)).indicator 1 t) * Ψ t =
      ε⁻¹ * ((∫ t in x - ε..x, Ψ t) - ∫ t in y..y + ε, Ψ t) := by
  have hab : a ≤ b := by linarith
  have h : ∀ t, ε⁻¹ * ((Ioc (x - ε) x).indicator 1 t - (Ioc y (y + ε)).indicator 1 t) * Ψ t =
      ε⁻¹ * ((Ioc (x - ε) x).indicator Ψ t - (Ioc y (y + ε)).indicator Ψ t) := fun t ↦ by
    simp only [indicator_apply]
    split_ifs <;> simp
  have hI : ∀ s s', a ≤ s → s ≤ s' → s' ≤ b →
      ∫ t in Ioc a b, (Ioc s s').indicator Ψ t = ∫ t in s..s', Ψ t := fun s s' h1 h2 h3 ↦ by
    rw [setIntegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le h2,
      inter_eq_right.2 (Ioc_subset_Ioc h1 h3)]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab,
    integral_sub (hΨ.1.indicator measurableSet_Ioc) (hΨ.1.indicator measurableSet_Ioc),
    hI _ _ hax (by linarith) (by linarith), hI _ _ (by linarith) (by linarith) hyb]

/-- If the integral of `Ψ` over `[x - ε, x]` dominates its integral over `[y, y + ε]` whenever
`a ≤ x - ε`, `x ≤ y` and `y + ε ≤ b`, then `Ψ` is antitone on a subset of `(a, b)` of full
measure, namely at its Lebesgue points. -/
private theorem exists_antitoneOn_of_integral_le {Ψ : ℝ → ℝ}
    (hΨ : IntervalIntegrable Ψ volume a b)
    (h : ∀ x y ε, 0 < ε → a ≤ x - ε → x ≤ y → y + ε ≤ b →
      ∫ t in y..y + ε, Ψ t ≤ ∫ t in x - ε..x, Ψ t) :
    ∃ S ⊆ Ioo a b, (∀ᵐ t ∂volume.restrict (Ioo a b), t ∈ S) ∧ AntitoneOn Ψ S := by
  set K : ℝ → ℝ := fun s ↦ ∫ r in a..s, Ψ r
  refine ⟨{t ∈ Ioo a b | HasDerivAt K (Ψ t) t}, fun t ht ↦ ht.1, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hΨ.ae_hasDerivAt_integral] with t ht hd
    exact ⟨ht, hd (uIcc_of_le (ht.1.le.trans ht.2.le) ▸ Ioo_subset_Icc_self ht) a left_mem_uIcc⟩
  · rintro x ⟨⟨hax, hxb⟩, hxd⟩ y ⟨⟨-, hyb⟩, hyd⟩ hxy
    -- Compare the left difference quotient of `K` at `x` with the right one at `y`.
    have hl := hxd.tendsto_slope_zero_left.comp
      (by simpa using (tendsto_neg_nhdsGT (a := (0 : ℝ))))
    refine le_of_tendsto_of_tendsto hyd.tendsto_slope_zero_right hl ?_
    have hint : ∀ c d, a ≤ c → c ≤ b → a ≤ d → d ≤ b → IntervalIntegrable Ψ volume c d :=
      fun c d hc hc' hd hd' ↦ hΨ.mono_set (uIcc_subset_uIcc
        (by rw [uIcc_of_le (hc.trans hc')]; exact ⟨hc, hc'⟩)
        (by rw [uIcc_of_le (hd.trans hd')]; exact ⟨hd, hd'⟩))
    filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.2 hax) (sub_pos.2 hyb))] with e he
    have he1 : e < x - a := he.2.trans_le (min_le_left _ _)
    have he2 : e < b - y := he.2.trans_le (min_le_right _ _)
    have hab : a ≤ b := hax.le.trans hxb.le
    have he0 : 0 < e := he.1
    simp only [Function.comp_apply, smul_eq_mul, K]
    have hI : ∀ c, a ≤ c → c ≤ b → IntervalIntegrable Ψ volume a c :=
      fun c hc hc' ↦ hint a c le_rfl hab hc hc'
    rw [intervalIntegral.integral_interval_sub_left (hI _ (by linarith) (by linarith))
        (hI _ (by linarith) (by linarith)),
      intervalIntegral.integral_interval_sub_left (hI _ (by linarith) (by linarith))
        (hI _ (by linarith) (by linarith)), ← sub_eq_add_neg, inv_neg,
      intervalIntegral.integral_symm (b := x), mul_neg, neg_mul, neg_neg]
    exact mul_le_mul_of_nonneg_left (h x y e he0 (by linarith) hxy (by linarith))
      (inv_nonneg.2 he0.le)

/-! ### The integrating factor and the weighted flux -/

/-- The integrating factor `E t = exp (∫ s in a..t, k s)` of an integrable `k` is absolutely
continuous with `E' = E k` almost everywhere, and lies between `exp (-∫ |k|)` and `exp (∫ |k|)`
on `[a, b]`. -/
private theorem exp_integral_properties (hab : a ≤ b) {k : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ Real.exp (∫ s in a..t, k s)) a b ∧
    (∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t ↦ Real.exp (∫ s in a..t, k s))
      (Real.exp (∫ s in a..t, k s) * k t) t) ∧
    ∀ t ∈ Icc a b, Real.exp (-∫ s in a..b, |k s|) ≤ Real.exp (∫ s in a..t, k s) ∧
      Real.exp (∫ s in a..t, k s) ≤ Real.exp (∫ s in a..b, |k s|) := by
  have hmem : a ∈ uIcc a b := left_mem_uIcc
  refine ⟨(hk.absolutelyContinuousOnInterval_intervalIntegral hmem).comp_of_contDiffAt
      (φ := Real.exp) fun _ _ ↦ Real.contDiff_exp.contDiffAt, ?_, fun t ht ↦ ?_⟩
  · filter_upwards [hk.ae_hasDerivAt_integral] with t ht htI
    exact (ht (uIcc_of_le hab ▸ htI) a hmem).exp
  · have hle : |∫ s in a..t, k s| ≤ ∫ s in a..b, |k s| :=
      (intervalIntegral.abs_integral_le_integral_abs ht.1).trans
        (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ fun _ ↦ abs_nonneg _) (hk.abs))
    exact ⟨Real.exp_le_exp.2 (neg_le_of_abs_le hle), Real.exp_le_exp.2 (le_of_abs_le hle)⟩

/-- Under the hypotheses of Hopf's lemma, `C / A ∈ L²(a, b)`, and the weighted flux
`E (A u' + B ū)` and the zeroth-order density `E ū ((C / A) B - D)` are integrable on `(a, b)`,
where `E = exp (∫ₐ C / A)`. -/
private theorem integrable_flux (hab : a < b) {A B C D : ℝ → ℝ} {lam Λ β : ℝ}
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hlam : 0 < lam) (hAlam : ∀ x ∈ Ioo a b, lam ≤ A x) (hAΛ : ∀ x ∈ Ioo a b, A x ≤ Λ)
    (hB : AEStronglyMeasurable B (volume.restrict (Ioo a b))) (hBβ : ∀ x ∈ Ioo a b, |B x| ≤ β)
    (hC : MemLp C 2 (volume.restrict (Ioo a b))) (hD : IntegrableOn D (Ioo a b))
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    MemLp (fun t ↦ C t / A t) 2 (volume.restrict (Ioo a b)) ∧
    Integrable (fun t ↦ Real.exp (∫ s in a..t, C s / A s) *
      (A t * gradient u t + B t * intervalRepresentativeL hab u (projIcc a b hab.le t)))
      (volume.restrict (Ioo a b)) ∧
    Integrable (fun t ↦ Real.exp (∫ s in a..t, C s / A s) *
      intervalRepresentativeL hab u (projIcc a b hab.le t) * (C t / A t * B t - D t))
      (volume.restrict (Ioo a b)) := by
  have hIoo : MeasurableSet (Ioo a b) := measurableSet_Ioo
  have hfin : IsFiniteMeasure (volume.restrict (Ioo a b)) := Real.isFiniteMeasure_restrict_Ioo a b
  set ub : ℝ → ℝ := fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)
  set k : ℝ → ℝ := fun t ↦ C t / A t with hk_def
  set E : ℝ → ℝ := fun t ↦ Real.exp (∫ s in a..t, k s)
  have hApos : ∀ x ∈ Ioo a b, 0 < A x := fun x hx ↦ hlam.trans_le (hAlam x hx)
  have hkm : AEStronglyMeasurable k (volume.restrict (Ioo a b)) :=
    (hC.aestronglyMeasurable.aemeasurable.div hA.aemeasurable).aestronglyMeasurable
  have hk2 : MemLp k 2 (volume.restrict (Ioo a b)) := by
    refine hC.of_le_mul (c := lam⁻¹) hkm ?_
    filter_upwards [ae_restrict_mem hIoo] with t ht
    rw [hk_def, norm_div, Real.norm_of_nonneg (hApos t ht).le, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hlam (hAlam t ht)) (norm_nonneg _)
  have hk1 : Integrable k (volume.restrict (Ioo a b)) := hk2.integrable one_le_two
  obtain ⟨hEac, -, hEbd⟩ := exp_integral_properties hab.le
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hk1)
  set K := ∫ s in a..b, |k s|
  have hEm : AEStronglyMeasurable E (volume.restrict (Ioo a b)) :=
    ((uIcc_of_le hab.le ▸ hEac.continuousOn).mono Ioo_subset_Icc_self).aestronglyMeasurable hIoo
  have hEb : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖E t‖ ≤ Real.exp K := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (hEbd t (Ioo_subset_Icc_self ht)).2
  have hubm : AEStronglyMeasurable ub (volume.restrict (Ioo a b)) :=
    ((intervalRepresentativeL hab u).continuous.comp continuous_projIcc).aestronglyMeasurable
  have hubb : ∀ t, ‖ub t‖ ≤ ‖intervalRepresentativeL hab u‖ := fun t ↦
    (intervalRepresentativeL hab u).norm_coe_le_norm _
  set Mu := ‖intervalRepresentativeL hab u‖
  have hAb : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    rw [Real.norm_of_nonneg (hApos t ht).le]
    exact hAΛ t ht
  have hBb : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖B t‖ ≤ β := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    exact hBβ t ht
  refine ⟨hk2, ?_, ?_⟩
  · -- `E A u'` is integrable since `u' ∈ L²`, and `E B ub` is bounded.
    have h1 := ((Lp.memLp (gradient u)).integrable one_le_two).bdd_mul (c := Real.exp K * Λ)
      (hEm.mul hA) (by
        filter_upwards [hEb, hAb] with t h1 h2
        calc ‖E t * A t‖ = ‖E t‖ * ‖A t‖ := norm_mul _ _
          _ ≤ Real.exp K * Λ := mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le)
    have h2 : Integrable (fun t ↦ E t * B t * ub t) (volume.restrict (Ioo a b)) := by
      refine (MemLp.of_bound ((hEm.mul hB).mul hubm) (Real.exp K * β * Mu) ?_).integrable le_rfl
      filter_upwards [hEb, hBb] with t h1 h2
      calc ‖E t * B t * ub t‖ = ‖E t‖ * ‖B t‖ * ‖ub t‖ := by rw [norm_mul, norm_mul]
        _ ≤ Real.exp K * β * Mu :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le) (hubb t)
            (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans h2))
    refine (h1.add h2).congr (ae_of_all _ fun t ↦ ?_)
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · -- `E ub B k` and `E ub D` are integrable since `k` and `D` are, and `E ub B` is bounded.
    have h1 := hk1.bdd_mul (c := Real.exp K * Mu * β) ((hEm.mul hubm).mul hB) (by
      filter_upwards [hEb, hBb] with t h1 h2
      calc ‖E t * ub t * B t‖ = ‖E t‖ * ‖ub t‖ * ‖B t‖ := by rw [norm_mul, norm_mul]
        _ ≤ Real.exp K * Mu * β :=
          mul_le_mul (mul_le_mul h1 (hubb t) (norm_nonneg _) (Real.exp_pos _).le) h2
            (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
    have h2 := hD.bdd_mul (c := Real.exp K * Mu) (hEm.mul hubm) (by
      filter_upwards [hEb] with t h1
      calc ‖E t * ub t‖ = ‖E t‖ * ‖ub t‖ := norm_mul _ _
        _ ≤ Real.exp K * Mu := mul_le_mul h1 (hubb t) (norm_nonneg _) (Real.exp_pos _).le)
    refine (h1.sub h2).congr (ae_of_all _ fun t ↦ ?_)
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring

/-- For `k ∈ L²(a, b)` and an absolutely continuous `ψ` vanishing at `a` and `b` with a bounded
measurable derivative `w`, the product `E ψ` with the integrating factor `E = exp (∫ₐ k)` is an
element of `H¹₀(a, b)` with derivative `E k ψ + E w`. -/
private theorem exists_w1p0_exp_integral_mul (hab : a < b) {k ψ w : ℝ → ℝ} {M : ℝ}
    (hk : MemLp k 2 (volume.restrict (Ioo a b))) (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψa : ψ a = 0) (hψb : ψ b = 0) (hψw : ∀ᵐ t, HasDerivAt ψ (w t) t)
    (hw : AEStronglyMeasurable w (volume.restrict (Ioo a b))) (hwM : ∀ t, |w t| ≤ M) :
    ∃ V : W1p0 volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      value (V : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) =ᵐ[volume.restrict (Ioo a b)]
        (fun t ↦ Real.exp (∫ s in a..t, k s) * ψ t) ∧
      gradient (V : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ Real.exp (∫ s in a..t, k s) * k t * ψ t + Real.exp (∫ s in a..t, k s) * w t := by
  have hIoo : MeasurableSet (Ioo a b) := measurableSet_Ioo
  have hfin : IsFiniteMeasure (volume.restrict (Ioo a b)) := Real.isFiniteMeasure_restrict_Ioo a b
  set E : ℝ → ℝ := fun t ↦ Real.exp (∫ s in a..t, k s)
  obtain ⟨hEac, hEder, hEbd⟩ := exp_integral_properties hab.le
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hk.integrable one_le_two))
  set K := ∫ s in a..b, |k s|
  have hEm : AEStronglyMeasurable E (volume.restrict (Ioo a b)) :=
    ((uIcc_of_le hab.le ▸ hEac.continuousOn).mono Ioo_subset_Icc_self).aestronglyMeasurable hIoo
  have hEb : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖E t‖ ≤ Real.exp K := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (hEbd t (Ioo_subset_Icc_self ht)).2
  obtain ⟨Mψ, hMψ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (uIcc_of_le hab.le ▸ hψ.continuousOn)
  have hψm : AEStronglyMeasurable ψ (volume.restrict (Ioo a b)) :=
    ((uIcc_of_le hab.le ▸ hψ.continuousOn).mono Ioo_subset_Icc_self).aestronglyMeasurable hIoo
  have hψbd : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖ψ t‖ ≤ Mψ := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    exact hMψ t (Ioo_subset_Icc_self ht)
  have hv : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt (fun t ↦ E t * ψ t) (E t * k t * ψ t + E t * w t) t := by
    filter_upwards [hEder, hψw] with t h1 h2 ht
    exact (h1 (Ioo_subset_Icc_self ht)).mul h2
  have hderiv : deriv (fun t ↦ E t * ψ t) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ E t * k t * ψ t + E t * w t := by
    filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem hIoo] with t ht hmem
    exact (ht hmem).deriv
  have hv2 : MemLp (fun t ↦ E t * k t * ψ t + E t * w t) 2 (volume.restrict (Ioo a b)) := by
    refine MemLp.add
      (hk.of_le_mul (c := Real.exp K * Mψ) ((hEm.mul hk.aestronglyMeasurable).mul hψm) ?_)
      (MemLp.of_bound (hEm.mul hw) (Real.exp K * M) ?_)
    · filter_upwards [hEb, hψbd] with t h1 h2
      calc ‖E t * k t * ψ t‖ = ‖E t‖ * ‖ψ t‖ * ‖k t‖ := by rw [norm_mul, norm_mul]; ring
        _ ≤ Real.exp K * Mψ * ‖k t‖ := by gcongr
    · filter_upwards [hEb] with t h1
      calc ‖E t * w t‖ = ‖E t‖ * |w t| := by rw [norm_mul, Real.norm_eq_abs (w t)]
        _ ≤ Real.exp K * M := mul_le_mul h1 (hwM t) (abs_nonneg _) (Real.exp_pos _).le
  obtain ⟨V, hV, hVg⟩ := AbsolutelyContinuousOnInterval.exists_w1p0_value_gradient_ae_eq
    (p := 2) (by norm_num) hab (f := fun t ↦ E t * ψ t) (hEac.mul hψ)
    (hv2.ae_eq hderiv.symm) (by simp [hψa]) (by simp [hψb])
  exact ⟨V, hV, hVg.trans hderiv⟩

/-- **The test inequality.** Testing the weak supersolution inequality with `E ψ`, where
`E = exp (∫ₐ C / A)` and `ψ ≥ 0` vanishes at `a` and `b`, and integrating the zeroth-order term
by parts gives `0 ≤ ∫ ψ' Ψ` for the weighted flux
`Ψ = E (A u' + B ū) - ∫ₐ E ū ((C / A) B - D)`. -/
private theorem integral_mul_weightedFlux_nonneg (hab : a < b) {A B C D : ℝ → ℝ}
    {lam Λ β : ℝ} {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2}
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hlam : 0 < lam) (hAlam : ∀ x ∈ Ioo a b, lam ≤ A x) (hAΛ : ∀ x ∈ Ioo a b, A x ≤ Λ)
    (hB : AEStronglyMeasurable B (volume.restrict (Ioo a b))) (hBβ : ∀ x ∈ Ioo a b, |B x| ≤ β)
    (hC : MemLp C 2 (volume.restrict (Ioo a b))) (hD : IntegrableOn D (Ioo a b))
    (hu : ∀ v : W1p0 volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      (∀ᵐ x ∂volume.restrict (Ioo a b),
        0 ≤ value (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x) →
      0 ≤ ∫ x in Ioo a b, ((A x * gradient u x + B x * value u x) *
          gradient (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x -
        (C x * gradient u x + D x * value u x) *
          value (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x))
    {ψ w : ℝ → ℝ} {M : ℝ} (hψ : AbsolutelyContinuousOnInterval ψ a b) (hψa : ψ a = 0)
    (hψb : ψ b = 0) (hψ0 : ∀ t, 0 ≤ ψ t) (hψw : ∀ᵐ t, HasDerivAt ψ (w t) t)
    (hw : AEStronglyMeasurable w (volume.restrict (Ioo a b))) (hwM : ∀ t, |w t| ≤ M) :
    0 ≤ ∫ t in a..b, w t *
      (Real.exp (∫ s in a..t, C s / A s) *
          (A t * gradient u t + B t * intervalRepresentativeL hab u (projIcc a b hab.le t)) -
        ∫ s in a..t, Real.exp (∫ r in a..s, C r / A r) *
          intervalRepresentativeL hab u (projIcc a b hab.le s) * (C s / A s * B s - D s)) := by
  have hIoo : MeasurableSet (Ioo a b) := measurableSet_Ioo
  have hfin : IsFiniteMeasure (volume.restrict (Ioo a b)) := Real.isFiniteMeasure_restrict_Ioo a b
  set ub : ℝ → ℝ := fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)
  set k : ℝ → ℝ := fun t ↦ C t / A t with hk_def
  set E : ℝ → ℝ := fun t ↦ Real.exp (∫ s in a..t, k s)
  set g : ℝ → ℝ := fun t ↦ E t * ub t * (k t * B t - D t) with hg_def
  obtain ⟨hk2, hΦ, hgi⟩ := integrable_flux hab hA hlam hAlam hAΛ hB hBβ hC hD u
  -- Test with `v = E ψ`; since `E' = k E` and `k A = C`, the drift cancels.
  obtain ⟨V, hV, hVg⟩ := exists_w1p0_exp_integral_mul hab hk2 hψ hψa hψb hψw hw hwM
  have h0 := hu V (by
    filter_upwards [hV] with t ht
    rw [ht]
    exact mul_nonneg (Real.exp_pos _).le (hψ0 t))
  have hval : value u =ᵐ[volume.restrict (Ioo a b)] ub := value_ae_eq_intervalRepresentativeL hab u
  rw [integral_congr_ae (g := fun t ↦ w t * (E t * (A t * gradient u t + B t * ub t)) +
    ψ t * g t) (by
      filter_upwards [hV, hVg, hval, ae_restrict_mem hIoo] with t h1 h2 h3 ht
      rw [h1, h2, h3]
      have := (hlam.trans_le (hAlam t ht)).ne'
      simp only [hg_def, hk_def]
      field_simp
      ring)] at h0
  have hwb : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖w t‖ ≤ M :=
    ae_of_all _ fun t ↦ (Real.norm_eq_abs (w t)).trans_le (hwM t)
  have hwΦ := hΦ.bdd_mul hw hwb
  obtain ⟨Mψ, hMψ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (uIcc_of_le hab.le ▸ hψ.continuousOn)
  rw [integral_add hwΦ (hgi.bdd_mul
    (((uIcc_of_le hab.le ▸ hψ.continuousOn).mono Ioo_subset_Icc_self).aestronglyMeasurable hIoo)
    ((ae_restrict_iff' hIoo).2 (ae_of_all _ fun t ht ↦ hMψ t (Ioo_subset_Icc_self ht))))] at h0
  -- Integrate `ψ g` by parts against the primitive `G` of `g`.
  have hIoc : ∀ f : ℝ → ℝ, ∫ t in a..b, f t = ∫ t in Ioo a b, f t := fun f ↦ by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hgi
  have hwI : IntervalIntegrable w volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
      ((MemLp.of_bound hw M hwb).integrable le_rfl)
  have hGac := hgI.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hibp := hGac.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hψ
    (by
      filter_upwards [hgI.ae_hasDerivAt_integral] with t ht hmem
      exact ht (uIoc_subset_uIcc hmem) a left_mem_uIcc)
    (hψw.mono fun t ht _ ↦ ht)
  rw [hψa, hψb, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  have hsplit : ∀ t, w t * (E t * (A t * gradient u t + B t * ub t) - ∫ s in a..t, g s) =
      w t * (E t * (A t * gradient u t + B t * ub t)) - (∫ s in a..t, g s) * w t :=
    fun t ↦ by ring
  -- The goal is this inequality with the abbreviations `E`, `k`, `ub` and `g` unfolded.
  suffices h : 0 ≤ ∫ t in a..b, w t *
      (E t * (A t * gradient u t + B t * ub t) - ∫ s in a..t, g s) from h
  simp only [hsplit]
  rw [intervalIntegral.integral_sub ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hwΦ)
    (hwI.continuousOn_mul hGac.continuousOn), hibp, sub_neg_eq_add, hIoc, hIoc]
  simpa only [mul_comm (g _)] using h0

/-! ### The two cases of the argument -/

/-- If the weighted flux `E (A u' + B ū) - G` is at least `m > 0` on `S` near `a`, where `G` is
continuous at `a` with `G a = 0` and `S` has full measure, then `ū` grows at least linearly
from `ū a = 0`. -/
private theorem exists_pos_mul_le_of_le_weightedFlux (hab : a < b) {A B E G ub u' : ℝ → ℝ}
    {S : Set ℝ} {Λ β K m δ₁ : ℝ} (hApos : ∀ x ∈ Ioo a b, 0 < A x)
    (hAΛ : ∀ x ∈ Ioo a b, A x ≤ Λ) (hBβ : ∀ x ∈ Ioo a b, |B x| ≤ β) (hEpos : ∀ t, 0 < E t)
    (hEK : ∀ t ∈ Icc a b, E t ≤ Real.exp K) (hubc : Continuous ub) (hua : ub a = 0)
    (hGc : ContinuousWithinAt G (Icc a b) a) (hG0 : G a = 0)
    (hu'I : IntervalIntegrable u' volume a b) (hftc : ∀ t ∈ Icc a b, ∫ s in a..t, u' s = ub t)
    (hS : ∀ᵐ s, s ∈ Ioo a b → s ∈ S) (hm : 0 < m) (hδ₁ : 0 < δ₁)
    (hΨ : ∀ t ∈ S, t < a + δ₁ → m ≤ E t * (A t * u' t + B t * ub t) - G t) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ ub (a + t) := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hΛ : 0 < Λ := (hApos _ hmid).trans_le (hAΛ _ hmid)
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hBβ _ hmid)
  set m₁ := m / 2 / Real.exp K
  have hm₁ : 0 < m₁ := by positivity
  obtain ⟨δ₂, hδ₂, hG⟩ := Metric.continuousWithinAt_iff.1 hGc (m / 2) (by positivity)
  obtain ⟨δ₃, hδ₃, hU⟩ := Metric.continuous_iff.1 hubc a (m₁ / 2 / (β + 1)) (by positivity)
  refine ⟨m₁ / 2 / Λ, by positivity, min (min δ₁ δ₂) (min δ₃ (b - a)),
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ (sub_pos.2 hab)), fun h hh ↦ ?_⟩
  have hhδ := hh.2
  simp only [lt_min_iff] at hhδ
  have hmem : a + h ∈ Icc a b := ⟨by linarith [hh.1], by linarith⟩
  refine le_of_le_of_eq ?_ (hftc _ hmem)
  calc m₁ / 2 / Λ * h = ∫ _ in a..a + h, m₁ / 2 / Λ := by simp; ring
    _ ≤ ∫ s in a..a + h, u' s := by
      refine intervalIntegral.integral_mono_ae_restrict (by linarith [hh.1])
        intervalIntegrable_const (hu'I.mono_set ?_) ?_
      · rw [uIcc_of_le (by linarith [hh.1]), uIcc_of_le hab.le]
        exact Icc_subset_Icc le_rfl hmem.2
      refine (ae_restrict_iff' measurableSet_Icc).2 ?_
      have hne : ∀ᵐ s : ℝ, s ≠ a := by simp [ae_iff, measure_singleton]
      filter_upwards [hS, hne] with s hsS hsa hs
      have hsI : s ∈ Ioo a b := ⟨lt_of_le_of_ne hs.1 hsa.symm, by linarith [hs.2]⟩
      have hdist : dist s a < min δ₂ δ₃ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        exact lt_min (by linarith [hs.2]) (by linarith [hs.2])
      have h2 := hG (Ioo_subset_Icc_self hsI) (hdist.trans_le (min_le_left _ _))
      rw [Real.dist_eq, hG0, sub_zero] at h2
      have h3 := hU s (hdist.trans_le (min_le_right _ _))
      rw [Real.dist_eq, hua, sub_zero] at h3
      -- `Φ ≥ m / 2`, so `Φ / E ≥ m₁`, while `|B ub| < m₁ / 2`; hence `A u' ≥ m₁ / 2`.
      have hΦE : m₁ ≤ (A s * u' s + B s * ub s) := by
        rw [← mul_le_mul_iff_of_pos_left (hEpos s)]
        calc E s * m₁ ≤ Real.exp K * m₁ :=
              mul_le_mul_of_nonneg_right (hEK s (Ioo_subset_Icc_self hsI)) hm₁.le
          _ = m / 2 := by simp only [m₁]; field_simp
          _ ≤ E s * (A s * u' s + B s * ub s) := by
            linarith [hΨ s (hsS hsI) (by linarith [hs.2]), neg_abs_le (G s)]
      have hBu : |B s * ub s| < m₁ / 2 := by
        rw [abs_mul]
        calc |B s| * |ub s| ≤ (β + 1) * |ub s| :=
              mul_le_mul_of_nonneg_right (by linarith [hBβ s hsI]) (abs_nonneg _)
          _ < (β + 1) * (m₁ / 2 / (β + 1)) := by gcongr
          _ = m₁ / 2 := by field_simp
      have hAu : m₁ / 2 ≤ A s * u' s := by linarith [le_abs_self (B s * ub s)]
      have hu'0 : 0 ≤ u' s := by
        by_contra hneg
        linarith [mul_nonpos_of_nonneg_of_nonpos (hApos s hsI).le (not_le.1 hneg).le]
      rw [div_le_iff₀ hΛ]
      nlinarith [hAΛ s hsI]

/-- If the weighted flux `E (A u' + B ū) - ∫ₐ g` is nonpositive on a set `S` of full measure,
where `|g| ≤ E |ū| q` with `q` integrable, then `ū` cannot be positive in `(a, b)` while
vanishing at `a`: the bound `u' ≤ θ max ū` near `a` contradicts this by a Grönwall argument. -/
private theorem false_of_weightedFlux_nonpos (hab : a < b) {A B E g q ub u' : ℝ → ℝ}
    {S : Set ℝ} {lam β K : ℝ} (hlam : 0 < lam) (hAlam : ∀ x ∈ Ioo a b, lam ≤ A x)
    (hBβ : ∀ x ∈ Ioo a b, |B x| ≤ β) (hEpos : ∀ t, 0 < E t)
    (hEbd : ∀ t ∈ Icc a b, Real.exp (-K) ≤ E t ∧ E t ≤ Real.exp K)
    (hubc : Continuous ub) (hua : ub a = 0) (hpos : ∀ t ∈ Ioo a b, 0 < ub t)
    (hgI : IntervalIntegrable g volume a b) (hqI : IntervalIntegrable q volume a b)
    (hq : ∀ s, 0 ≤ q s) (hgq : ∀ s ∈ Icc a b, |g s| ≤ E s * |ub s| * q s)
    (hu'I : IntervalIntegrable u' volume a b) (hftc : ∀ t ∈ Icc a b, ∫ s in a..t, u' s = ub t)
    (hS : ∀ᵐ s, s ∈ Ioo a b → s ∈ S)
    (hΨ : ∀ t ∈ S, E t * (A t * u' t + B t * ub t) - ∫ s in a..t, g s ≤ 0) : False := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hBβ _ hmid)
  set Q := ∫ t in a..b, q t
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hab.le fun _ _ ↦ hq _
  set θ := (Real.exp K * Real.exp K * Q + β) / lam
  have hθ : 0 ≤ θ := by positivity
  set r := min ((b - a) / 2) (1 / (2 * (θ + 1)))
  have hr : 0 < r := lt_min (by linarith) (by positivity)
  have hy : a + r ∈ Ioo a b :=
    ⟨by linarith, by linarith [min_le_left ((b - a) / 2) (1 / (2 * (θ + 1)))]⟩
  have hrθ : r * θ < 1 := by
    calc r * θ ≤ 1 / (2 * (θ + 1)) * θ := mul_le_mul_of_nonneg_right (min_le_right _ _) hθ
      _ < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  -- `U`, the maximum of `ub` on `[a, a + r]`, is positive.
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hy.1.le)
    hubc.continuousOn
  set U := ub z
  have hU : 0 < U := (hpos _ hy).trans_le (hzmax ⟨hy.1.le, le_rfl⟩)
  have hub0 : ∀ s ∈ Icc a (a + r), 0 ≤ ub s := fun s hs ↦ by
    rcases hs.1.eq_or_lt with rfl | hs1
    · exact hua.ge
    · exact (hpos s ⟨hs1, hs.2.trans_lt hy.2⟩).le
  have hsub : ∀ s ∈ Icc a (a + r), s ∈ Icc a b := fun s hs ↦ ⟨hs.1, hs.2.trans hy.2.le⟩
  -- The primitive of `g` is at most `exp K U Q` on `[a, a + r]`.
  have hGb : ∀ t ∈ Icc a (a + r), ∫ s in a..t, g s ≤ Real.exp K * U * Q := fun t ht ↦ by
    have hsubI : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl (hsub t ht).2
    calc ∫ s in a..t, g s ≤ |∫ s in a..t, g s| := le_abs_self _
      _ ≤ ∫ s in a..t, |g s| := intervalIntegral.abs_integral_le_integral_abs ht.1
      _ ≤ ∫ s in a..t, Real.exp K * U * q s := by
        refine intervalIntegral.integral_mono_on ht.1 (hgI.mono_set hsubI).abs
          ((hqI.mono_set hsubI).const_mul _) fun s hs ↦ ?_
        have hs' : s ∈ Icc a (a + r) := ⟨hs.1, hs.2.trans ht.2⟩
        refine (hgq s (hsub s hs')).trans ?_
        rw [abs_of_nonneg (hub0 s hs')]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hEbd s (hsub s hs')).2 (hzmax hs')
          (hub0 s hs') (Real.exp_pos _).le) (hq s)
      _ ≤ ∫ s in a..b, Real.exp K * U * q s :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 (hsub t ht).2
          (ae_of_all _ fun s ↦ mul_nonneg (by positivity) (hq s)) (hqI.const_mul _)
      _ = Real.exp K * U * Q := intervalIntegral.integral_const_mul _ _
  -- On `S ∩ (a, a + r]` the bound `Ψ ≤ 0` gives `u' ≤ θ U`.
  have hu'b : ∀ s ∈ S, s ∈ Ioo a b → s ≤ a + r → u' s ≤ θ * U := fun s hs hsI hsr ↦ by
    have hmem : s ∈ Icc a (a + r) := ⟨hsI.1.le, hsr⟩
    have hΦE : A s * u' s + B s * ub s ≤ Real.exp K * Real.exp K * U * Q := by
      rw [← mul_le_mul_iff_of_pos_left (hEpos s)]
      have h1 : 1 ≤ Real.exp K * E s := by
        calc (1 : ℝ) = Real.exp K * Real.exp (-K) := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
          _ ≤ Real.exp K * E s :=
            mul_le_mul_of_nonneg_left (hEbd s (hsub s hmem)).1 (Real.exp_pos _).le
      have h2 : 0 ≤ Real.exp K * U * Q := by positivity
      nlinarith [hΨ s hs, hGb s hmem]
    have hBu : -(β * U) ≤ B s * ub s := (abs_le.1 ((abs_mul _ _).le.trans (mul_le_mul
      (hBβ s hsI) (abs_le.2 ⟨by linarith [hub0 s hmem], hzmax hmem⟩) (abs_nonneg _) hβ))).1
    have hAu : A s * u' s ≤ lam * (θ * U) := by
      simp only [θ]
      rw [div_mul_eq_mul_div, mul_div_cancel₀ _ hlam.ne']
      nlinarith
    by_contra hlt
    have hu'0 : 0 ≤ u' s := (mul_nonneg hθ hU.le).trans (not_le.1 hlt).le
    nlinarith [mul_lt_mul_of_pos_left (not_le.1 hlt) hlam,
      mul_le_mul_of_nonneg_right (hAlam s hsI) hu'0]
  -- Integrating `u' ≤ θ U` from `a` to the maximum point `z` gives `U ≤ r θ U < U`.
  have hz' : z ∈ Icc a b := hsub z hz
  have hint : U ≤ (z - a) * (θ * U) := by
    refine le_of_eq_of_le (hftc z hz').symm ?_
    calc ∫ s in a..z, u' s ≤ ∫ _ in a..z, θ * U := by
          refine intervalIntegral.integral_mono_ae_restrict hz.1
            (hu'I.mono_set ?_) intervalIntegrable_const ?_
          · rw [uIcc_of_le hz.1, uIcc_of_le hab.le]
            exact Icc_subset_Icc le_rfl hz'.2
          refine (ae_restrict_iff' measurableSet_Icc).2 ?_
          have hne : ∀ᵐ s : ℝ, s ≠ a := by simp [ae_iff, measure_singleton]
          filter_upwards [hS, hne] with s hsS hsa hs
          have hsI : s ∈ Ioo a b :=
            ⟨lt_of_le_of_ne hs.1 hsa.symm, hs.2.trans_lt (hz.2.trans_lt hy.2)⟩
          exact hu'b s (hsS hsI) hsI (hs.2.trans hz.2)
      _ = (z - a) * (θ * U) := by simp; ring
  nlinarith [hz.2, mul_nonneg hθ hU.le]

/-! ### Hopf's lemma -/

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval.** Let `a < b` and let
`u ∈ H¹(a, b)` be a weak supersolution of `(A u' + B u)' + C u' + D u ≤ 0`, that is,
`∫ (A u' + B u) v' - (C u' + D u) v ≥ 0` for every nonnegative `v ∈ H¹₀(a, b)`, where `A` is
measurable with `λ ≤ A ≤ Λ` and `λ > 0`, `B` is measurable with `|B| ≤ β`, `C ∈ L²(a, b)` and
`D ∈ L¹(a, b)`. If the continuous representative `ū` of `u` vanishes at `a` and is positive in
`(a, b)`, then `ε t ≤ ū (a + t)` for some `ε > 0` and all small `t > 0`.

The coefficients need no continuity, and `B` and `D` need no sign condition. -/
theorem exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg (hab : a < b)
    {A B C D : ℝ → ℝ} {lam Λ β : ℝ} {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2}
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hlam : 0 < lam) (hAlam : ∀ x ∈ Ioo a b, lam ≤ A x) (hAΛ : ∀ x ∈ Ioo a b, A x ≤ Λ)
    (hB : AEStronglyMeasurable B (volume.restrict (Ioo a b))) (hBβ : ∀ x ∈ Ioo a b, |B x| ≤ β)
    (hC : MemLp C 2 (volume.restrict (Ioo a b))) (hD : IntegrableOn D (Ioo a b))
    (hu : ∀ v : W1p0 volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      (∀ᵐ x ∂volume.restrict (Ioo a b),
        0 ≤ value (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x) →
      0 ≤ ∫ x in Ioo a b, ((A x * gradient u x + B x * value u x) *
          gradient (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x -
        (C x * gradient u x + D x * value u x) *
          value (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x))
    (hua : (intervalTraceL hab u).1 = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < intervalRepresentativeL hab u (projIcc a b hab.le t)) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ,
      ε * t ≤ intervalRepresentativeL hab u (projIcc a b hab.le (a + t)) := by
  set ub : ℝ → ℝ := fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t) with hub_def
  set k : ℝ → ℝ := fun t ↦ C t / A t with hk_def
  set E : ℝ → ℝ := fun t ↦ Real.exp (∫ s in a..t, k s) with hE_def
  set g : ℝ → ℝ := fun t ↦ E t * ub t * (k t * B t - D t) with hg_def
  set Φ : ℝ → ℝ := fun t ↦ E t * (A t * gradient u t + B t * ub t) with hΦ_def
  set G : ℝ → ℝ := fun t ↦ ∫ s in a..t, g s with hG_def
  obtain ⟨hk2, hΦi, hgi⟩ := integrable_flux hab hA hlam hAlam hAΛ hB hBβ hC hD u
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hgi
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    hgI.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  -- The weighted flux `Ψ = Φ - G` is antitone on a set `S` of full measure.
  have hΨI : IntervalIntegrable (fun t ↦ Φ t - G t) volume a b :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hΦi).sub
      hGac.continuousOn.intervalIntegrable
  obtain ⟨S, hSI, hSae, hSanti⟩ := exists_antitoneOn_of_integral_le hΨI
    fun x y ε hε hax hxy hyb ↦ by
      obtain ⟨ψ, hψ, hψa, hψb, hψ0, hψw⟩ := exists_trapezoid hε hax hxy hyb
      have h := integral_mul_weightedFlux_nonneg hab hA hlam hAlam hAΛ hB hBβ hC hD hu hψ hψa
        hψb hψ0 hψw (M := ε⁻¹ * 2)
        (((measurable_one.indicator measurableSet_Ioc).sub
          (measurable_one.indicator measurableSet_Ioc)).const_mul ε⁻¹).aestronglyMeasurable
        (fun t ↦ by
          rw [abs_mul, abs_of_pos (inv_pos.2 hε)]
          gcongr
          simp only [indicator_apply]
          split_ifs <;> norm_num)
      rw [integral_trapezoid_mul hax hxy hyb hε hΨI] at h
      exact sub_nonneg.1 (nonneg_of_mul_nonneg_right h (inv_pos.2 hε))
  -- The facts about `E`, `ub` and `u'` that both cases use.
  obtain ⟨-, -, hEbd⟩ := exp_integral_properties hab.le
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hk2.integrable one_le_two))
  have hubc : Continuous ub := (intervalRepresentativeL hab u).continuous.comp continuous_projIcc
  have ha0 : intervalRepresentativeL hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 := by
    rw [intervalTraceL_apply] at hua
    exact hua
  have hua' : ub a = 0 := by simpa only [hub_def, projIcc_left] using ha0
  have hftc : ∀ t ∈ Icc a b, ∫ s in a..t, gradient u s = ub t := fun t ht ↦ by
    have h := integral_gradient_eq_intervalRepresentativeL_sub hab u ⟨a, left_mem_Icc.2 hab.le⟩
      ⟨t, ht⟩
    simp only at h
    rw [h, ha0, sub_zero, hub_def]
    simp only [projIcc_of_mem hab.le ht]
  have hu'I : IntervalIntegrable (gradient u) volume a b := by
    have : IsFiniteMeasure (volume.restrict
        ((⟨Ioo a b, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) : Set ℝ)) :=
      Real.isFiniteMeasure_restrict_Ioo a b
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
      ((Lp.memLp (gradient u)).integrable one_le_two)
  have hSae' : ∀ᵐ s, s ∈ Ioo a b → s ∈ S := (ae_restrict_iff' measurableSet_Ioo).1 hSae
  by_cases hcase : ∃ m > 0, ∃ δ > 0, ∀ t ∈ S, t < a + δ → m ≤ Φ t - G t
  · -- Near `a` the weighted flux stays above some `m > 0`.
    obtain ⟨m, hm, δ₁, hδ₁, hΨm⟩ := hcase
    exact exists_pos_mul_le_of_le_weightedFlux hab (fun x hx ↦ hlam.trans_le (hAlam x hx)) hAΛ
      hBβ (fun t ↦ Real.exp_pos _) (fun t ht ↦ (hEbd t ht).2) hubc hua'
      ((uIcc_of_le hab.le ▸ hGac.continuousOn) a (left_mem_Icc.2 hab.le))
      intervalIntegral.integral_same hu'I hftc hSae' hm hδ₁ hΨm
  · -- Otherwise `Ψ ≤ 0` on `S`, since `Ψ` is antitone there.
    push Not at hcase
    have hΨ0 : ∀ t ∈ S, Φ t - G t ≤ 0 := by
      intro t ht
      by_contra hlt
      obtain ⟨s, hs, hst, hlt'⟩ := hcase _ (not_le.1 hlt) (t - a) (sub_pos.2 (hSI ht).1)
      linarith [hSanti hs ht (by linarith)]
    have hBbd : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖B t‖ ≤ β :=
      (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht ↦ hBβ t ht)
    have hqI : IntervalIntegrable (fun t ↦ |k t * B t - D t|) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
        (((hk2.integrable one_le_two).mul_bdd hB hBbd).sub hD).abs
    refine (false_of_weightedFlux_nonpos (E := E) (g := g) (ub := ub) hab hlam hAlam hBβ
      (fun t ↦ Real.exp_pos _) hEbd hubc hua' hpos hgI hqI (fun _ ↦ abs_nonneg _)
      (fun s _ ↦ le_of_eq ?_) hu'I hftc hSae' hΨ0).elim
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval, derivative form.**
Under the hypotheses of `exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg`, if the
continuous representative `ū` of `u` has a right derivative `d` at `a`, then `d > 0`. -/
theorem pos_of_hasDerivWithinAt_of_integral_nonneg (hab : a < b)
    {A B C D : ℝ → ℝ} {lam Λ β : ℝ} {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2}
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hlam : 0 < lam) (hAlam : ∀ x ∈ Ioo a b, lam ≤ A x) (hAΛ : ∀ x ∈ Ioo a b, A x ≤ Λ)
    (hB : AEStronglyMeasurable B (volume.restrict (Ioo a b))) (hBβ : ∀ x ∈ Ioo a b, |B x| ≤ β)
    (hC : MemLp C 2 (volume.restrict (Ioo a b))) (hD : IntegrableOn D (Ioo a b))
    (hu : ∀ v : W1p0 volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      (∀ᵐ x ∂volume.restrict (Ioo a b),
        0 ≤ value (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x) →
      0 ≤ ∫ x in Ioo a b, ((A x * gradient u x + B x * value u x) *
          gradient (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x -
        (C x * gradient u x + D x * value u x) *
          value (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) x))
    (hua : (intervalTraceL hab u).1 = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < intervalRepresentativeL hab u (projIcc a b hab.le t)) {d : ℝ}
    (hd : HasDerivWithinAt (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) d
      (Ici a) a) :
    0 < d := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg hab
    hA hlam hAlam hAΛ hB hBβ hC hD hu hua hpos
  have ha0 : intervalRepresentativeL hab u (projIcc a b hab.le a) = 0 := by
    rw [intervalTraceL_apply] at hua
    simpa only [projIcc_left] using hua
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Ici_sdiff_left] at hslope
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  -- For `a < t < a + δ` the slope at `a` is the difference quotient at `t - a`.
  filter_upwards [Ioo_mem_nhdsGT (show a < a + δ by linarith)] with t ht
  have h' := h (t - a) ⟨sub_pos.2 ht.1, by linarith [ht.2]⟩
  rw [add_sub_cancel] at h'
  rw [slope_def_field, ha0, sub_zero, le_div_iff₀ (sub_pos.2 ht.1)]
  exact h'

end TauCeti.PDE
