/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import TauCeti.Analysis.Fourier.AbsolutelyContinuous
import TauCeti.Analysis.Fourier.SpectralGap

/-!
# Wirtinger's inequality for periodic functions

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

## Main results

* `TauCeti.integral_norm_sub_average_sq_le`: Wirtinger's inequality.
* `TauCeti.integral_norm_sub_average_sq_eq_iff`: its equality case.
* `ContinuousLinearMap.norm_integral_apply_apply_le`: the bound on the integral of a bilinear form
  along a loop.

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
  -- `g` is continuous on the compact interval, hence bounded, hence square integrable.
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) := by
    have hgc : ContinuousOn g (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hg.continuousOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
    exact MemLp.of_bound ((hgc.aestronglyMeasurable measurableSet_Icc).mono_set
      Ioc_subset_Icc_self) C
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))
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
  let G₀ := AddCircle.liftIoc (b - a) a g
  have hG₀ : MemLp G₀ 2 AddCircle.haarAddCircle := by
    have hab' : a + (b - a) = b := by ring
    have hgL2' : MemLp g 2 (volume.restrict (Ioc a (a + (b - a)))) := by
      rw [hab']
      exact hgL2
    exact hgL2'.memLp_liftIoc.haarAddCircle
  let G : Lp ℂ 2 AddCircle.haarAddCircle := hG₀.toLp
  have hGc (n : ℤ) : fourierCoeff G n = c n := by
    simp [G, G₀, c, fourierCoeff_congr_ae hG₀.coeFn_toLp, fourierCoeff_liftIoc_eq]
  have hGnorm : (∫ t, ‖G t‖ ^ 2 ∂AddCircle.haarAddCircle) =
      (b - a)⁻¹ * ∫ x in a..b, ‖g x‖ ^ 2 := by
    calc
      (∫ t, ‖G t‖ ^ 2 ∂AddCircle.haarAddCircle) =
          ∑' n : ℤ, ‖fourierCoeff G n‖ ^ 2 := (tsum_sq_fourierCoeff G).symm
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
    obtain ⟨u, v, hG⟩ := (integral_norm_sq_eq_tsum_frequency_sq_fourierCoeff_iff
      G hGzero hGenergy.summable).1 heq'
    intro n hn₁ hn₂
    classical
    rw [← hGc, ← fourierBasis_repr, HilbertBasis.repr_apply_apply, hG, coe_fourierBasis]
    simp [inner_add_right, inner_smul_right,
      orthonormal_iff_ite.mp (orthonormal_fourier (T := b - a)), hn₁, hn₂]
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

/-- The squared distance from the mean and the squared derivative split into the squares of their
coordinates in an orthonormal basis. -/
private theorem integral_norm_sq_eq_sum (hab : a < b) (hfc : ContinuousOn f [[a, b]])
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2) =
        ∑ i, ∫ x in a..b, ⟪stdOrthonormalBasis ℝ V i, f x - ⨍ y in a..b, f y⟫ ^ 2 ∧
      ∫ x in a..b, ‖f' x‖ ^ 2 = ∑ i, ∫ x in a..b, ⟪stdOrthonormalBasis ℝ V i, f' x⟫ ^ 2 := by
  set e := stdOrthonormalBasis ℝ V
  have hint₁ (i) : IntervalIntegrable (fun x => ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2) volume a b :=
    ((continuousOn_const.inner (hfc.sub continuousOn_const)).pow 2).intervalIntegrable
  have hint₂ (i) : IntervalIntegrable (fun x => ⟪e i, f' x⟫ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((innerSL ℝ (e i)).comp_memLp' hf').integrable_sq
  simp_rw [← e.sum_sq_inner_right]
  exact ⟨intervalIntegral.integral_finsetSum fun i _ => hint₁ i,
    intervalIntegral.integral_finsetSum fun i _ => hint₂ i⟩

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

end Vector

end TauCeti

namespace ContinuousLinearMap

variable {a b : ℝ}

/-- Along a loop `f` on `[a, b]` with square-integrable derivative, the integral of a continuous
bilinear form `B (f x) (f' x)` is bounded by `‖B‖ (b - a) / (2π)` times the `L²` energy of the
loop. For a symplectic form `B` the left side is twice the symplectic area enclosed by the loop,
and this is the isoperimetric inequality. -/
theorem norm_integral_apply_apply_le {V G : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (B : V →L[ℝ] V →L[ℝ] G) (hab : a < b) {f f' : ℝ → V}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ‖∫ x in a..b, B (f x) (f' x)‖ ≤
      ‖B‖ * ((b - a) / (2 * π)) * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set c := (b - a) / (2 * π)
  have hc : 0 < c := div_pos (sub_pos.2 hab) (by positivity)
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf'int : IntegrableOn f' (Ioc a b) := hf'.integrable one_le_two
  have hf'ii : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hf'int
  have hsq : IntervalIntegrable (fun x => ‖f' x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((memLp_two_iff_integrable_sq_norm hf'.aestronglyMeasurable).1 hf')
  have hdev : IntervalIntegrable (fun x => ‖f x - m‖ ^ 2) volume a b :=
    ((hfc.sub continuousOn_const).norm.pow 2).intervalIntegrable
  -- The mean contributes nothing, since `∫ f' = f b - f a = 0`.
  have hmean : ∫ x in a..b, B m (f' x) = 0 := by
    rw [(B m).intervalIntegral_comp_comm hf'ii,
      integral_eq_sub_of_hasDerivAt hf hf'ii, hfab, sub_self, map_zero]
  -- Pointwise, `‖B (f - m) f'‖ ≤ ‖B‖ (‖f - m‖² / c + c ‖f'‖²) / 2`.
  have hpt (x : ℝ) : ‖B (f x - m) (f' x)‖ ≤
      ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2) := by
    refine (B.le_opNorm₂ _ _).trans ?_
    rw [mul_assoc]
    gcongr
    have hsplit : (c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2 - ‖f x - m‖ * ‖f' x‖ =
        c⁻¹ * (‖f x - m‖ - c * ‖f' x‖) ^ 2 / 2 := by
      field_simp
      ring
    have : 0 ≤ c⁻¹ * (‖f x - m‖ - c * ‖f' x‖) ^ 2 / 2 := by positivity
    linarith
  have hbound : IntervalIntegrable
      (fun x => ‖B‖ * ((c⁻¹ * ‖f x - m‖ ^ 2 + c * ‖f' x‖ ^ 2) / 2)) volume a b :=
    (((hdev.const_mul c⁻¹).add (hsq.const_mul c)).div_const 2).const_mul ‖B‖
  have hint : IntervalIntegrable (fun x => B (f x - m) (f' x)) volume a b :=
    hbound.mono_fun' (B.aestronglyMeasurable_comp₂
      (((hfc.sub continuousOn_const).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc) hf'ii.def'.aestronglyMeasurable) (Filter.Eventually.of_forall hpt)
  have hrewrite : ∫ x in a..b, B (f x) (f' x) = ∫ x in a..b, B (f x - m) (f' x) := by
    have hBm : IntervalIntegrable (fun x => B m (f' x)) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 ((B m).integrable_comp hf'int)
    rw [← add_zero (∫ x in a..b, B (f x - m) (f' x)), ← hmean,
      ← intervalIntegral.integral_add hint hBm]
    simp [map_sub]
  rw [hrewrite]
  refine (norm_integral_le_of_norm_le hab.le (Filter.Eventually.of_forall fun x _ => hpt x)
    hbound).trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hdev.const_mul c⁻¹) (hsq.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- Wirtinger's inequality bounds the deviation term by the energy term.
  have key : (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c * ∫ x in a..b, ‖f' x‖ ^ 2 := by
    calc (c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) ≤ c⁻¹ * (c ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2) := by
          gcongr
          exact TauCeti.integral_norm_sub_average_sq_le hab
            (hfc.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable countable_empty
              (fun t ht => hf t (Ioo_subset_Icc_self ht.1)) hf'ii)
            (Filter.Eventually.of_forall fun t ht => hf t (uIoc_subset_uIcc ht)) hfab hf'
      _ = c * ∫ x in a..b, ‖f' x‖ ^ 2 := by field_simp
  calc ‖B‖ * (((c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2)
      ≤ ‖B‖ * (((c * ∫ x in a..b, ‖f' x‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2) := by
        gcongr
    _ = ‖B‖ * c * ∫ x in a..b, ‖f' x‖ ^ 2 := by ring

end ContinuousLinearMap
