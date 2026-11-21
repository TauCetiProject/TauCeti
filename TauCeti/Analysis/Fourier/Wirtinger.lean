/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import TauCeti.Analysis.Fourier.AbsolutelyContinuous
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Fourier.SpectralGap
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Wirtinger's inequality for periodic functions and for arcs

Let `f : ℝ → V` be an absolutely continuous function on `[a, b]` with `f a = f b`, valued in a
finite-dimensional real inner product space, whose almost-everywhere derivative `f'` is square
integrable. **Wirtinger's inequality** bounds the `L²` distance of `f` from its mean by its
derivative, with the sharp constant:

`∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤ ((b - a) / (2π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2`
(`TauCeti.integral_norm_sub_average_sq_le`).

Equality holds exactly when `f` is its mean plus a first harmonic, that is, when there are
`u v : V` with `f t = ⨍ y in a..b, f y + cos (2π t / (b - a)) • u + sin (2π t / (b - a)) • v`
for every `t ∈ [a, b]` (`TauCeti.integral_norm_sub_average_sq_eq_iff`). Taking `V = ℂ` gives
the complex-valued statements.

The proof is Fourier-analytic: for an absolutely continuous closed curve the `n`-th Fourier
coefficient of `f'` on `[a, b]` is that of `f` multiplied by `2πin / (b - a)`
(`TauCeti.hasSum_sq_frequency_mul_sq_fourierCoeffOn`), the zeroth coefficient of `f` minus its
mean vanishes, and Parseval's identity (`hasSum_sq_fourierCoeffOn`) turns the coefficientwise
comparison into the inequality. Equality forces every coefficient of frequency `|n| ≥ 2` to
vanish, and a continuous closed curve with finitely many nonzero coefficients is the sum of its
Fourier series at every point. Vector values reduce to complex scalars coordinatewise in an
orthonormal basis. No smoothness beyond absolute continuity is assumed.

Together with the Cauchy--Schwarz inequality it bounds the integral of any continuous bilinear
form along a loop: since `∫ B(m, f') = B(m, f b - f a) = 0` for the mean `m`,

`‖∫ x in a..b, B (f x) (f' x)‖ ≤ ‖B‖ * ((b - a) / (2π)) * ∫ x in a..b, ‖f' x‖ ^ 2`
(`ContinuousLinearMap.norm_integral_apply_apply_le`).

For `B` a symplectic form this is the isoperimetric inequality for the symplectic area of a loop,
the estimate behind removal of singularities and energy quantization for holomorphic curves.

An arc `f` on `[a, b]` whose endpoints lie in a subspace `K` satisfies the same inequality with
the doubled constant `(b - a) / π`, measured from a suitable point of `K`
(`TauCeti.exists_mem_integral_norm_sub_sq_le`): doubling `f` across `a`, the copy reflected in
`K`, gives a loop on `[2a - b, b]` whose mean lies in `K`. For `K = ⊥` this is the Dirichlet and
for `K = ⊤` the Neumann Poincaré inequality on an interval. If `B` vanishes on `K`, the integral of
`B (f x) (f' x)` along such an arc is bounded as for loops, with `(b - a) / π` in place of
`(b - a) / (2π)` (`ContinuousLinearMap.norm_integral_apply_apply_le_of_mem`). This is the
isoperimetric inequality for arcs with boundary on an isotropic subspace, used at boundary
punctures of holomorphic curves with totally real boundary conditions.

## Main results

* `TauCeti.integral_norm_sub_average_sq_le`: Wirtinger's inequality.
* `TauCeti.integral_norm_sub_average_sq_eq_iff`: its equality case.
* `TauCeti.integral_norm_sq_le_of_integral_eq_zero`: Wirtinger's inequality for mean-zero `C¹`
  loops.
* `TauCeti.integral_norm_sq_eq_sum_integral_inner_sq`: the interval integral of `‖F‖ ^ 2` is the
  sum of those of the squared coordinates of `F` in an orthonormal basis.
* `TauCeti.exists_mem_integral_norm_sub_sq_le`: Wirtinger's inequality for arcs with endpoints in
  a subspace.
* `ContinuousLinearMap.norm_integral_apply_apply_le`: the bound on the integral of a bilinear form
  along a loop.
* `ContinuousLinearMap.norm_integral_apply_apply_le_of_mem`: the same along an arc with endpoints
  in a subspace on which the form vanishes.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Cambridge University Press, 1934,
  Theorem 258 (Wirtinger's inequality).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.4 (the isoperimetric inequality, proved by the
  same Fourier argument).
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval RealInnerProductSpace

namespace TauCeti

variable {a b : ℝ}

section Complex

/-- The coefficientwise comparison behind Wirtinger's inequality, for a complex closed curve whose
zeroth Fourier coefficient vanishes: the inequality holds, with equality exactly when every
coefficient of frequency `|n| ≥ 2` vanishes. -/
private theorem integral_norm_sq_le_and_eq_iff_of_fourierCoeffOn_zero (hab : a < b)
    {g g' : ℝ → ℂ} (hg : AbsolutelyContinuousOnInterval g a b)
    (hgg' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt g (g' t) t) (hgab : g a = g b)
    (hg' : MemLp g' 2 (volume.restrict (Ioc a b))) (h0 : fourierCoeffOn hab g 0 = 0) :
    (∫ x in a..b, ‖g x‖ ^ 2 ≤ ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖g' x‖ ^ 2) ∧
    (∫ x in a..b, ‖g x‖ ^ 2 = ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖g' x‖ ^ 2 ↔
      ∀ n : ℤ, n ≠ 1 → n ≠ -1 → fourierCoeffOn hab g n = 0) := by
  set c := fourierCoeffOn hab g
  set K := ((b - a) / (2 * π)) ^ 2
  have hinv : 0 < (b - a)⁻¹ := inv_pos.2 (sub_pos.2 hab)
  have hgc : ContinuousOn g (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hg.continuousOn
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) :=
    hgc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self 2
  -- Parseval for `g` and for `g'`, both normalized by `(b - a)⁻¹`.
  have hP : HasSum (fun n : ℤ => ‖c n‖ ^ 2) ((b - a)⁻¹ * ∫ x in a..b, ‖g x‖ ^ 2) := by
    simpa only [smul_eq_mul] using hasSum_sq_fourierCoeffOn hab hgL2
  have hE : HasSum (fun n : ℤ => K * ((2 * π * (n : ℝ) / (b - a)) ^ 2 * ‖c n‖ ^ 2))
      ((b - a)⁻¹ * (K * ∫ x in a..b, ‖g' x‖ ^ 2)) := by
    convert (hasSum_sq_frequency_mul_sq_fourierCoeffOn hab hg hgg' hgab hg').mul_left K using 1
    ring
  -- Coefficientwise, `K * (2πn / (b - a)) ^ 2 = n ^ 2`, and the `n = 0` coefficient vanishes.
  have hK (n : ℤ) : K * (2 * π * (n : ℝ) / (b - a)) ^ 2 = (n : ℝ) ^ 2 := by
    simp only [K]
    field_simp
  let _ : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  obtain ⟨G, hGc⟩ := exists_Lp_fourierCoeff_eq_fourierCoeffOn hab hgL2
  have hGnorm : (∫ t, ‖G t‖ ^ 2 ∂AddCircle.haarAddCircle) = (b - a)⁻¹ * ∫ x in a..b, ‖g x‖ ^ 2 :=
    calc (∫ t, ‖G t‖ ^ 2 ∂AddCircle.haarAddCircle) = ∑' n : ℤ, ‖fourierCoeff G n‖ ^ 2 :=
          (tsum_sq_fourierCoeff G).symm
      _ = ∑' n : ℤ, ‖c n‖ ^ 2 := tsum_congr fun n => by rw [hGc]
      _ = (b - a)⁻¹ * ∫ x in a..b, ‖g x‖ ^ 2 := hP.tsum_eq
  have hGenergy : HasSum (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeff G n‖ ^ 2)
      ((b - a)⁻¹ * (K * ∫ x in a..b, ‖g' x‖ ^ 2)) := by
    convert hE using 1
    funext n
    rw [hGc, ← mul_assoc, hK]
  have hGzero : fourierCoeff G 0 = 0 := by rw [hGc]; exact h0
  have hle' : (b - a)⁻¹ * ∫ x in a..b, ‖g x‖ ^ 2 ≤
      (b - a)⁻¹ * (K * ∫ x in a..b, ‖g' x‖ ^ 2) := by
    rw [← hGnorm, ← hGenergy.tsum_eq]
    exact integral_norm_sq_le_tsum_frequency_sq_fourierCoeff G hGzero hGenergy.summable
  refine ⟨le_of_mul_le_mul_left hle' hinv, ?_⟩
  constructor
  · intro heq
    have heq' := congrArg (fun x : ℝ => (b - a)⁻¹ * x) heq
    rw [← hGnorm, ← hGenergy.tsum_eq] at heq'
    intro n hn₁ hn₂
    exact (hGc n).symm.trans
      (Lp.fourierCoeff_eq_zero_of_integral_norm_sq_eq_tsum_frequency_sq G hGzero hGenergy.summable
        heq' hn₁ hn₂)
  · -- Otherwise the two series agree term by term.
    intro hc
    apply mul_left_cancel₀ hinv.ne'
    refine hP.unique ?_
    convert hE using 1
    funext n
    rw [← mul_assoc, hK]
    by_cases hn : n = 1 ∨ n = -1
    · rcases hn with rfl | rfl <;> simp
    · rw [not_or] at hn
      simp [hc n hn.1 hn.2]

/-- Wirtinger's inequality and its equality case for complex-valued functions; the vector-valued
statements reduce to it coordinatewise. -/
private theorem integral_norm_sub_average_sq_le_and_eq_iff_complex (hab : a < b) {f f' : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2) ∧
    (∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 =
        ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 ↔
      ∃ u v : ℂ, ∀ t ∈ Icc a b, f t - ⨍ y in a..b, f y =
        Real.cos (2 * π * t / (b - a)) • u + Real.sin (2 * π * t / (b - a)) • v) := by
  set m := ⨍ y in a..b, f y
  set g : ℝ → ℂ := fun x => f x - m
  have hg : AbsolutelyContinuousOnInterval g a b :=
    hf.sub (LipschitzWith.const m).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgg' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt g (f' t) t := by
    filter_upwards [hff'] with t ht hmem
    exact (ht hmem).sub_const m
  have hgab : g a = g b := by simp only [g, hfab]
  -- The zeroth coefficient of `g` is its mean, which vanishes.
  have h0 : fourierCoeffOn hab g 0 = 0 := by
    have hfi : IntervalIntegrable f volume a b := hf.continuousOn.intervalIntegrable
    have hba' : (b : ℂ) - a ≠ 0 := by exact_mod_cast (sub_pos.2 hab).ne'
    simp [fourierCoeffOn_eq_integral, g, m, interval_average_eq,
      intervalIntegral.integral_sub hfi intervalIntegrable_const, hba']
  obtain ⟨hle, heq⟩ :=
    integral_norm_sq_le_and_eq_iff_of_fourierCoeffOn_zero hab hg hgg' hgab hf' h0
  refine ⟨hle, heq.trans ⟨exists_cos_smul_add_sin_smul hab
    (by simpa only [uIcc_of_le hab.le] using hg.continuousOn) hgab, ?_⟩⟩
  -- A first harmonic has no coefficients outside the frequencies `±1`.
  rintro ⟨u, v, huv⟩ n hn₁ hn₂
  have h : g =ᵐ[volume.restrict (Ioc a b)] fun t => Real.cos (2 * π * t / (b - a)) • u +
      Real.sin (2 * π * t / (b - a)) • v :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => huv t (Ioc_subset_Icc_self ht)
  rw [congrFun (fourierCoeffOn_congr_ae hab h) n]
  exact fourierCoeffOn_cos_smul_add_sin_smul hab u v hn₁ hn₂

end Complex

section Vector

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {f f' : ℝ → V}

/-- Wirtinger's inequality and its equality case for a single coordinate `⟪w, f⟫`. -/
private theorem integral_inner_sub_average_sq_le_and_eq_iff (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) (w : V) :
    (∫ x in a..b, ⟪w, f x - ⨍ y in a..b, f y⟫ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪w, f' x⟫ ^ 2) ∧
    (∫ x in a..b, ⟪w, f x - ⨍ y in a..b, f y⟫ ^ 2 =
        ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪w, f' x⟫ ^ 2 ↔
      ∃ u v : ℝ, ∀ t ∈ Icc a b, ⟪w, f t - ⨍ y in a..b, f y⟫ =
        Real.cos (2 * π * t / (b - a)) * u + Real.sin (2 * π * t / (b - a)) * v) := by
  -- The coordinate `⟪w, ·⟫`, read as a complex number.
  let L : V →L[ℝ] ℂ := ofRealCLM.comp (innerSL ℝ w)
  have hL (v : V) : L v = (⟪w, v⟫ : ℂ) := rfl
  have hm : ⨍ y in a..b, L (f y) = L (⨍ y in a..b, f y) := by
    rw [interval_average_eq, interval_average_eq, L.map_smul,
      L.intervalIntegral_comp_comm hf.continuousOn.intervalIntegrable]
  have h := integral_norm_sub_average_sq_le_and_eq_iff_complex hab
    (f := fun x => L (f x)) (f' := fun x => L (f' x))
    (L.lipschitzWith.comp_absolutelyContinuousOnInterval hf)
    (by filter_upwards [hff'] with t ht hmem using L.hasFDerivAt.comp_hasDerivAt t (ht hmem))
    (by rw [hfab]) (L.comp_memLp' hf')
  simp_rw [hm, ← L.map_sub, hL, norm_real, Real.norm_eq_abs, sq_abs] at h
  refine ⟨h.1, h.2.trans ⟨fun ⟨u, v, huv⟩ => ⟨u.re, v.re, fun t ht => ?_⟩,
    fun ⟨u, v, huv⟩ => ⟨u, v, fun t ht => ?_⟩⟩⟩
  · simpa only [add_re, real_smul, re_ofReal_mul, ofReal_re] using congrArg re (huv t ht)
  · rw [huv t ht]
    simp only [ofReal_add, ofReal_mul, real_smul]

/-- **Splitting an `L²` norm into coordinates.** For `F` square integrable on `(a, b]` and valued
in a finite-dimensional real inner product space, the interval integral of `‖F‖ ^ 2` is the sum of
those of the squares of its coordinates in the standard orthonormal basis. -/
theorem integral_norm_sq_eq_sum_integral_inner_sq {F : ℝ → V} (hab : a ≤ b)
    (hF : MemLp F 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖F x‖ ^ 2 = ∑ i, ∫ x in a..b, ⟪stdOrthonormalBasis ℝ V i, F x⟫ ^ 2 := by
  simp_rw [← (stdOrthonormalBasis ℝ V).sum_sq_inner_right]
  exact intervalIntegral.integral_finsetSum fun i _ =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((innerSL ℝ (stdOrthonormalBasis ℝ V i)).comp_memLp' hF).integrable_sq

/-- The squared distance from the mean and the squared derivative split into the squares of their
coordinates in an orthonormal basis. -/
private theorem integral_norm_sq_eq_sum (hab : a < b) (hfc : ContinuousOn f [[a, b]])
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2) =
        ∑ i, ∫ x in a..b, ⟪stdOrthonormalBasis ℝ V i, f x - ⨍ y in a..b, f y⟫ ^ 2 ∧
      ∫ x in a..b, ‖f' x‖ ^ 2 = ∑ i, ∫ x in a..b, ⟪stdOrthonormalBasis ℝ V i, f' x⟫ ^ 2 := by
  have hc : ContinuousOn (fun x => f x - ⨍ y in a..b, f y) (Icc a b) := by
    rw [← uIcc_of_le hab.le]
    exact hfc.sub continuousOn_const
  exact ⟨integral_norm_sq_eq_sum_integral_inner_sq hab.le
      (hc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self 2),
    integral_norm_sq_eq_sum_integral_inner_sq hab.le hf'⟩

/-- **Wirtinger's inequality.** An absolutely continuous function on `[a, b]` with `f a = f b`,
valued in a finite-dimensional real inner product space and with square-integrable
almost-everywhere derivative, deviates from its mean in `L²` by at most `(b - a) / (2π)` times
the `L²` norm of its derivative. -/
theorem integral_norm_sub_average_sq_le (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  obtain ⟨h₁, h₂⟩ := integral_norm_sq_eq_sum hab hf.continuousOn hf'
  rw [h₁, h₂, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    (integral_inner_sub_average_sq_le_and_eq_iff hab hf hff' hfab hf' _).1

/-- **Wirtinger's inequality for mean-zero `C¹` loops.** If `f` has a continuous derivative `f'`,
`f a = f b` and `f` has mean zero on `[a, b]`, then
`∫ₐᵇ ‖f‖² ≤ ((b - a) / (2π))² ∫ₐᵇ ‖f'‖²`. -/
theorem integral_norm_sq_le_of_integral_eq_zero (hab : a < b)
    (hff' : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (hfab : f a = f b)
    (hmean : ∫ x in a..b, f x = 0) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  have hderiv : deriv f = f' := funext fun t ↦ (hff' t).deriv
  have hf : ContDiff ℝ 1 f :=
    contDiff_one_iff_deriv.2 ⟨fun t ↦ (hff' t).differentiableAt, hderiv ▸ hf'⟩
  have h := integral_norm_sub_average_sq_le hab hf.contDiffOn.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall fun t _ ↦ hff' t) hfab
    (hf'.continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      Ioc_subset_Icc_self 2)
  simpa [interval_average_eq, hmean] using h

/-- **Equality in Wirtinger's inequality.** Equality holds exactly when, on `[a, b]`, the function
is its mean plus a first harmonic `cos (2π t / (b - a)) • u + sin (2π t / (b - a)) • v`. -/
theorem integral_norm_sub_average_sq_eq_iff (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 =
        ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 ↔
      ∃ u v : V, ∀ t ∈ Icc a b, f t - ⨍ y in a..b, f y =
        Real.cos (2 * π * t / (b - a)) • u + Real.sin (2 * π * t / (b - a)) • v := by
  set e := stdOrthonormalBasis ℝ V
  have hc := integral_inner_sub_average_sq_le_and_eq_iff hab hf hff' hfab hf'
  obtain ⟨h₁, h₂⟩ := integral_norm_sq_eq_sum hab hf.continuousOn hf'
  rw [h₁, h₂, Finset.mul_sum, Finset.sum_eq_sum_iff_of_le fun i _ => (hc (e i)).1]
  simp_rw [(hc _).2, Finset.mem_univ, true_imp_iff]
  constructor
  · intro h
    choose u v huv using h
    refine ⟨∑ i, u i • e i, ∑ i, v i • e i, fun t ht => ?_⟩
    rw [← e.sum_repr' (f t - _), Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [huv i t ht, add_smul, smul_smul, smul_smul]
  · rintro ⟨u, v, huv⟩ i
    refine ⟨⟪e i, u⟫, ⟪e i, v⟫, fun t ht => ?_⟩
    rw [huv t ht, inner_add_right, real_inner_smul_right, real_inner_smul_right]

/-- The double of an arc `f` across `a`: `f` from `a` on, and before `a` the reflection in `K` of
`t ↦ f (2a - t)`. For `f` on `[a, b]` with endpoints in `K` it is a loop on `[2a - b, b]`. -/
private noncomputable def arcDouble (K : Submodule ℝ V) (a : ℝ) (f : ℝ → V) (t : ℝ) : V :=
  if a ≤ t then f t else K.reflection (f (2 * a - t))

/-- The derivative of `arcDouble K a f`, away from `a`, for `f` with derivative `f'`. -/
private noncomputable def arcDoubleDeriv (K : Submodule ℝ V) (a : ℝ) (f' : ℝ → V) : ℝ → V :=
  (Ioi a).piecewise f' fun t ↦ -K.reflection (f' (2 * a - t))

private theorem arcDouble_of_le (K : Submodule ℝ V) {f : ℝ → V} {t : ℝ} (ht : a ≤ t) :
    arcDouble K a f t = f t := by
  simp [arcDouble, ht]

private theorem arcDouble_of_ge (K : Submodule ℝ V) {f : ℝ → V} (ha : f a ∈ K) {t : ℝ}
    (ht : t ≤ a) : arcDouble K a f t = K.reflection (f (2 * a - t)) := by
  rcases ht.eq_or_lt with rfl | h
  · simp [arcDouble, show 2 * t - t = t by ring, K.reflection_mem_subspace_eq_self ha]
  · simp [arcDouble, not_le.2 h]

private theorem arcDoubleDeriv_of_ge (K : Submodule ℝ V) {f' : ℝ → V} {t : ℝ} (ht : t ≤ a) :
    arcDoubleDeriv K a f' t = -K.reflection (f' (2 * a - t)) :=
  piecewise_eq_of_notMem _ _ _ (notMem_Ioi.2 ht)

private theorem continuousOn_arcDouble (K : Submodule ℝ V) (hab : a ≤ b) {f : ℝ → V}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ∈ K) :
    ContinuousOn (arcDouble K a f) (Icc (2 * a - b) b) := by
  rw [← Icc_union_Icc_eq_Icc (by linarith) hab]
  refine ContinuousOn.union_of_isClosed ?_ (hf.congr fun t ht ↦ arcDouble_of_le K ht.1)
    isClosed_Icc isClosed_Icc
  exact (K.reflection.continuous.comp_continuousOn (hf.comp (by fun_prop)
    fun t ht ↦ ⟨by linarith [ht.2], by linarith [ht.1]⟩)).congr
      fun t ht ↦ arcDouble_of_ge K ha ht.2

private theorem hasDerivAt_arcDouble (K : Submodule ℝ V) {f f' : ℝ → V}
    (hff' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) {t : ℝ} (ht : t ∈ Ioo (2 * a - b) b \ {a}) :
    HasDerivAt (arcDouble K a f) (arcDoubleDeriv K a f' t) t := by
  obtain ⟨ht, hta⟩ := ht
  rcases lt_or_gt_of_ne hta with h | h
  · have hd := K.reflection.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t
      ((hff' (2 * a - t) ⟨by linarith, by linarith [ht.1]⟩).scomp t
        ((hasDerivAt_id t).const_sub (2 * a)))
    refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Iio_mem_nhds h] with s hs
      simp [arcDouble, not_le.2 (mem_Iio.1 hs)]
    · simp [arcDoubleDeriv_of_ge K h.le]
  · refine ((hff' t ⟨h, ht.2⟩).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds h] with s hs
      exact arcDouble_of_le K (mem_Ioi.1 hs).le
    · exact (piecewise_eq_of_mem _ _ _ (mem_Ioi.2 h)).symm

private theorem memLp_arcDoubleDeriv (K : Submodule ℝ V) {f' : ℝ → V}
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    MemLp (arcDoubleDeriv K a f') 2 (volume.restrict (Ioc (2 * a - b) b)) := by
  have hmp : MeasurePreserving (fun t ↦ 2 * a - t) (volume.restrict (Ioc (2 * a - b) a))
      (volume.restrict (Ico a b)) := by
    have h := (Measure.measurePreserving_sub_left volume (2 * a)).restrict_preimage
      measurableSet_Ico (s := Ico a b)
    have hpre : (fun t ↦ 2 * a - t) ⁻¹' Ico a b = Ioc (2 * a - b) a := by
      ext t
      simp only [mem_preimage, mem_Ico, mem_Ioc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rwa [hpre] at h
  have hr : Ioi a ∩ Ioc (2 * a - b) b = Ioc a b := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, by linarith [h.1], h.2⟩⟩
  have hl : (Ioi a)ᶜ ∩ Ioc (2 * a - b) b = Ioc (2 * a - b) a := by
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_Ioi, not_lt, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, by linarith [h.2]⟩⟩
  refine MemLp.piecewise measurableSet_Ioi.nullMeasurableSet ?_ ?_
  · rwa [Measure.restrict_restrict measurableSet_Ioi, hr]
  · have hf'Ico : MemLp f' 2 (volume.restrict (Ico a b)) := by
      rwa [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    rw [Measure.restrict_restrict measurableSet_Ioi.compl, hl]
    exact (K.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
      (hf'Ico.comp_measurePreserving hmp)).neg

/-- An integral over the doubled half `[2a - b, a]` is the integral over `[a, b]` of the
reflected arc. -/
private theorem integral_arcDouble_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Submodule ℝ V) (hab : a ≤ b) {f : ℝ → V} (ha : f a ∈ K) (F : V → E) :
    ∫ x in (2 * a - b)..a, F (arcDouble K a f x) = ∫ x in a..b, F (K.reflection (f x)) := by
  rw [intervalIntegral.integral_congr (g := fun x ↦ F (K.reflection (f (2 * a - x)))) fun x hx ↦ by
      rw [arcDouble_of_ge K ha ((uIcc_of_le (by linarith : 2 * a - b ≤ a)).subset hx).2],
    intervalIntegral.integral_comp_sub_left (fun x ↦ F (K.reflection (f x))),
    show 2 * a - a = a by ring, show 2 * a - (2 * a - b) = b by ring]

/-- An integral over `[a, b]` of the doubled arc is the integral of the arc. -/
private theorem integral_arcDouble_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Submodule ℝ V) (hab : a ≤ b) {f : ℝ → V} (F : V → E) :
    ∫ x in a..b, F (arcDouble K a f x) = ∫ x in a..b, F (f x) :=
  intervalIntegral.integral_congr fun x hx ↦ by
    simp only [arcDouble_of_le K ((uIcc_of_le hab).subset hx).1]

/-- An integral over `[2a - b, b]` splits at `a`. -/
private theorem integral_add_adjacent_two_mul_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hab : a ≤ b) {g : ℝ → E} (hg : IntervalIntegrable g volume (2 * a - b) b) :
    ∫ x in (2 * a - b)..b, g x = (∫ x in (2 * a - b)..a, g x) + ∫ x in a..b, g x := by
  have hcb : 2 * a - b ≤ b := by linarith
  have hamem : a ∈ Icc (2 * a - b) b := ⟨by linarith, hab⟩
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hg.mono_set (uIcc_of_le hcb ▸ uIcc_subset_Icc ⟨le_rfl, hcb⟩ hamem))
    (hg.mono_set (uIcc_of_le hcb ▸ uIcc_subset_Icc hamem ⟨hcb, le_rfl⟩))).symm

/-- An integral over `[2a - b, b]` of the doubled arc is the sum of the integrals over `[a, b]`
of the reflected arc and of the arc. -/
private theorem integral_arcDouble {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Submodule ℝ V) (hab : a ≤ b) {f : ℝ → V} (ha : f a ∈ K) {F : V → E}
    (hF : IntervalIntegrable (fun x ↦ F (arcDouble K a f x)) volume (2 * a - b) b) :
    ∫ x in (2 * a - b)..b, F (arcDouble K a f x) =
      (∫ x in a..b, F (K.reflection (f x))) + ∫ x in a..b, F (f x) := by
  rw [integral_add_adjacent_two_mul_sub hab hF, integral_arcDouble_left K hab ha F,
    integral_arcDouble_right K hab F]

/-- The mean of the doubled arc over `[2a - b, b]` is fixed by the reflection in `K`, so it lies
in `K`. -/
private theorem average_arcDouble_mem (K : Submodule ℝ V) (hab : a ≤ b) {f : ℝ → V}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ∈ K) :
    ⨍ y in (2 * a - b)..b, arcDouble K a f y ∈ K := by
  have hint : ∫ x in (2 * a - b)..b, arcDouble K a f x =
      K.reflection (∫ x in a..b, f x) + ∫ x in a..b, f x := by
    rw [integral_arcDouble K hab ha (F := fun v ↦ v)
      ((continuousOn_arcDouble K hab hf ha).intervalIntegrable_of_Icc (by linarith))]
    exact congrArg (· + _) (K.reflection.toLinearIsometry.intervalIntegral_comp_comm f)
  rw [← K.reflection_eq_self_iff, interval_average_eq, hint, map_smul, map_add,
    K.reflection_reflection, add_comm]

/-- The energy of the doubled arc over `[2a - b, b]` is twice the energy of the arc. -/
private theorem integral_norm_arcDoubleDeriv_sq (K : Submodule ℝ V) (hab : a ≤ b) {f' : ℝ → V}
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in (2 * a - b)..b, ‖arcDoubleDeriv K a f' x‖ ^ 2 = 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  have hg'2 := memLp_arcDoubleDeriv K hf'
  have hF : IntervalIntegrable (fun x ↦ ‖arcDoubleDeriv K a f' x‖ ^ 2) volume (2 * a - b) b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      ((memLp_two_iff_integrable_sq_norm hg'2.aestronglyMeasurable).1 hg'2)
  have hl : ∫ x in (2 * a - b)..a, ‖arcDoubleDeriv K a f' x‖ ^ 2 =
      ∫ x in (2 * a - b)..a, ‖f' (2 * a - x)‖ ^ 2 :=
    intervalIntegral.integral_congr fun x hx ↦ by
      simp only [arcDoubleDeriv_of_ge K ((uIcc_of_le (by linarith : 2 * a - b ≤ a)).subset hx).2,
        norm_neg, LinearIsometryEquiv.norm_map]
  have hr : ∫ x in a..b, ‖arcDoubleDeriv K a f' x‖ ^ 2 = ∫ x in a..b, ‖f' x‖ ^ 2 := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx ↦ ?_)
    rw [uIoc_of_le hab] at hx
    simp only [arcDoubleDeriv, piecewise_eq_of_mem _ _ _ (mem_Ioi.2 hx.1)]
  rw [integral_add_adjacent_two_mul_sub hab hF, hl, hr,
    intervalIntegral.integral_comp_sub_left (fun x ↦ ‖f' x‖ ^ 2),
    show 2 * a - a = a by ring, show 2 * a - (2 * a - b) = b by ring]
  ring

/-- **Wirtinger's inequality for arcs with endpoints on a subspace.** If `f` is continuous on
`[a, b]`, differentiable on `(a, b)` with square-integrable derivative, and both endpoints lie in
a subspace `K`, then some point `m` of `K` satisfies
`∫ₐᵇ ‖f - m‖² ≤ ((b - a) / π)² ∫ₐᵇ ‖f'‖²`. For `K = ⊥` this is the sharp Poincaré inequality for
functions vanishing at both ends, with `m = 0`; for `K = ⊤`, which imposes no condition at the
ends, it is the Neumann Poincaré inequality. -/
theorem exists_mem_integral_norm_sub_sq_le (K : Submodule ℝ V) (hab : a < b) {f f' : ℝ → V}
    (hf : ContinuousOn f (Icc a b)) (hff' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) (ha : f a ∈ K) (hb : f b ∈ K) :
    ∃ m ∈ K, ∫ x in a..b, ‖f x - m‖ ^ 2 ≤ ((b - a) / π) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  -- Wirtinger's inequality for the doubled loop on `[c, b]`.
  set c := 2 * a - b
  have hcb : c ≤ b := by linarith
  have hgc := continuousOn_arcDouble K hab.le hf ha
  have hg'2 := memLp_arcDoubleDeriv K hf'
  have hW := integral_norm_sub_average_sq_le (by linarith : c < b)
    ((uIcc_of_le hcb ▸ hgc).absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
      (countable_singleton a)
        (fun t ht ↦ hasDerivAt_arcDouble K hff' (by rwa [min_eq_left hcb, max_eq_right hcb] at ht))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hcb).2 (hg'2.integrable one_le_two)))
    (by
      filter_upwards [(Set.toFinite {a, b}).countable.ae_notMem volume] with t ht htcb
      rw [uIoc_of_le hcb] at htcb
      refine hasDerivAt_arcDouble K hff' ⟨⟨htcb.1, htcb.2.lt_of_ne fun h ↦ ht ?_⟩, fun h ↦ ht ?_⟩
      · exact Or.inr h
      · exact Or.inl h)
    (by rw [arcDouble_of_ge K ha (by linarith), arcDouble_of_le K hab.le,
      show 2 * a - c = b by ring, K.reflection_mem_subspace_eq_self hb]) hg'2
  -- The mean of the doubled loop lies in `K`, and both sides are twice those for `f`.
  set m := ⨍ y in c..b, arcDouble K a f y
  have hmK : m ∈ K := average_arcDouble_mem K hab.le hf ha
  refine ⟨m, hmK, ?_⟩
  have hnorm (v : V) : ‖K.reflection v - m‖ = ‖v - m‖ := by
    rw [← K.reflection_mem_subspace_eq_self hmK, ← map_sub, LinearIsometryEquiv.norm_map,
      K.reflection_mem_subspace_eq_self hmK]
  have hdev : ∫ x in c..b, ‖arcDouble K a f x - m‖ ^ 2 = 2 * ∫ x in a..b, ‖f x - m‖ ^ 2 := by
    rw [integral_arcDouble K hab.le ha (F := fun v ↦ ‖v - m‖ ^ 2)
      (((hgc.sub continuousOn_const).norm.pow 2).intervalIntegrable_of_Icc hcb)]
    simp only [hnorm]
    ring
  rw [hdev, integral_norm_arcDoubleDeriv_sq K hab.le hf', show b - c = 2 * (b - a) by ring,
    show 2 * (b - a) / (2 * π) = (b - a) / π by field_simp] at hW
  linarith

end Vector

end TauCeti

namespace ContinuousLinearMap

variable {a b : ℝ}

/-- If `B m (f a) = B m (f b)` and `f - m` satisfies the Poincaré inequality
`∫ₐᵇ ‖f - m‖² ≤ c² ∫ₐᵇ ‖f'‖²`, then the integral of a continuous bilinear form `B (f x) (f' x)` is
bounded by `‖B‖ c` times the `L²` energy `∫ₐᵇ ‖f'‖²`. -/
theorem norm_integral_apply_apply_le_of_integral_norm_sub_sq_le {V G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : V →L[ℝ] V →L[ℝ] G) (hab : a ≤ b) {f f' : ℝ → V} {m : V} {c : ℝ} (hc : 0 < c)
    (hfc : ContinuousOn f (Icc a b)) (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) (hm : B m (f a) = B m (f b))
    (hW : ∫ x in a..b, ‖f x - m‖ ^ 2 ≤ c ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2) :
    ‖∫ x in a..b, B (f x) (f' x)‖ ≤ ‖B‖ * c * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  have hf'ii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hf'.integrable one_le_two)
  have hsq : IntervalIntegrable (fun x => ‖f' x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((memLp_two_iff_integrable_sq_norm hf'.aestronglyMeasurable).1 hf')
  have hdev : IntervalIntegrable (fun x => ‖f x - m‖ ^ 2) volume a b :=
    ((hfc.sub continuousOn_const).norm.pow 2).intervalIntegrable_of_Icc hab
  have hpt (x : ℝ) := B.norm_apply_apply_le_mul_add_sq hc (f x - m) (f' x)
  have hbound : IntervalIntegrable
      (fun x => ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2)) volume a b :=
    (((hdev.const_mul c⁻¹).add (hsq.const_mul c)).div_const 2).const_mul ‖B‖
  rw [B.intervalIntegral_apply_apply_eq_sub_const (uIcc_of_le hab ▸ hfc)
    (by rwa [min_eq_left hab, max_eq_right hab]) hm hf'ii]
  refine (norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall fun x _ => hpt x)
    hbound).trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hdev.const_mul c⁻¹) (hsq.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- The Poincaré inequality bounds the deviation term by the energy term.
  have key : (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c * ∫ x in a..b, ‖f' x‖ ^ 2 := by
    calc (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c⁻¹ * (c ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2) := by
          gcongr
      _ = c * ∫ x in a..b, ‖f' x‖ ^ 2 := by field_simp
  calc ‖B‖ * (((c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2)
      ≤ ‖B‖ * (((c * ∫ x in a..b, ‖f' x‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2) := by
        gcongr
    _ = ‖B‖ * c * ∫ x in a..b, ‖f' x‖ ^ 2 := by ring

/-- Along a loop `f` on `[a, b]` with square-integrable derivative, the integral of a continuous
bilinear form `B (f x) (f' x)` is bounded by `‖B‖ (b - a) / (2π)` times the `L²` energy of the
loop. For a symplectic form `B` the left side is twice the symplectic area enclosed by the loop,
and this is the isoperimetric inequality. -/
theorem norm_integral_apply_apply_le {V G : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : V →L[ℝ] V →L[ℝ] G) (hab : a < b) {f f' : ℝ → V}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ‖∫ x in a..b, B (f x) (f' x)‖ ≤
      ‖B‖ * ((b - a) / (2 * π)) * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'ii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hf'.integrable one_le_two)
  refine B.norm_integral_apply_apply_le_of_integral_norm_sub_sq_le hab.le
    (div_pos (sub_pos.2 hab) (by positivity)) (uIcc_of_le hab.le ▸ hfc)
    (fun x hx => hf x (Ioo_subset_Icc_self.trans Icc_subset_uIcc hx)) hf'
    (m := ⨍ y in a..b, f y) (by rw [hfab]) ?_
  -- Wirtinger's inequality for the loop.
  exact TauCeti.integral_norm_sub_average_sq_le hab
    (hfc.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable countable_empty
      (fun t ht => hf t (Ioo_subset_Icc_self ht.1)) hf'ii)
    (Filter.Eventually.of_forall fun t ht => hf t (uIoc_subset_uIcc ht)) hfab hf'

/-- Along an arc `f` on `[a, b]` with square-integrable derivative whose endpoints lie in a
subspace `K` on which `B` vanishes, the integral of a continuous bilinear form `B (f x) (f' x)` is
bounded by `‖B‖ (b - a) / π` times the `L²` energy of the arc. For a symplectic form `B` and an
isotropic subspace `K` this is the isoperimetric inequality for arcs with boundary on `K`. -/
theorem norm_integral_apply_apply_le_of_mem {V G : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : V →L[ℝ] V →L[ℝ] G) {K : Submodule ℝ V} (hK : ∀ v ∈ K, ∀ w ∈ K, B v w = 0)
    (hab : a < b) {f f' : ℝ → V} (hfc : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : MemLp f' 2 (volume.restrict (Ioc a b)))
    (ha : f a ∈ K) (hb : f b ∈ K) :
    ‖∫ x in a..b, B (f x) (f' x)‖ ≤ ‖B‖ * ((b - a) / π) * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  obtain ⟨m, hmK, hW⟩ := TauCeti.exists_mem_integral_norm_sub_sq_le K hab hfc hf hf' ha hb
  exact B.norm_integral_apply_apply_le_of_integral_norm_sub_sq_le hab.le
    (div_pos (sub_pos.2 hab) Real.pi_pos) hfc hf hf' (by rw [hK m hmK _ ha, hK m hmK _ hb]) hW

end ContinuousLinearMap
