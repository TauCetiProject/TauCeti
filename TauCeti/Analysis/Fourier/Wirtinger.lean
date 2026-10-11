/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# Wirtinger's inequality for periodic functions

Let `f : ℝ → V` be a differentiable function on `[a, b]` with `f a = f b`, valued in a
finite-dimensional real inner product space, whose derivative is square integrable. **Wirtinger's
inequality** bounds the `L²` distance of `f` from its mean by its derivative, with the sharp
constant:

`∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤ ((b - a) / (2π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2`
(`TauCeti.integral_norm_sub_average_sq_le`).

The constant is attained by `x ↦ cos (2π x / (b - a))`. The proof is Fourier-analytic: for
`n ≠ 0` the `n`-th Fourier coefficient of `f` on `[a, b]` is that of `f'` divided by
`2πin / (b - a)`, the zeroth coefficient of `f` minus its mean vanishes, and Parseval's identity
(`hasSum_sq_fourierCoeffOn`) turns the coefficientwise comparison into the inequality. Vector
values reduce to complex scalars coordinatewise in an orthonormal basis.

Together with the Cauchy--Schwarz inequality it bounds the integral of any continuous bilinear
form along a loop: since `∫ B(m, f') = B(m, f b - f a) = 0` for the mean `m`,

`‖∫ x in a..b, B (f x) (f' x)‖ ≤ ‖B‖ * ((b - a) / (2π)) * ∫ x in a..b, ‖f' x‖ ^ 2`
(`ContinuousLinearMap.norm_integral_apply_apply_le`).

For `B` a symplectic form this is the isoperimetric inequality for the symplectic area of a loop,
the estimate behind removal of singularities and energy quantization for holomorphic curves.

## Main results

* `TauCeti.integral_norm_sub_average_sq_le`: Wirtinger's inequality.
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

/-- Wirtinger's inequality for complex-valued functions; the vector-valued
`TauCeti.integral_norm_sub_average_sq_le` reduces to it coordinatewise. -/
private theorem integral_norm_sub_average_sq_le_complex (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set g : ℝ → ℂ := fun x => f x - m
  have hba : 0 < b - a := sub_pos.2 hab
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hg : ∀ x ∈ [[a, b]], HasDerivAt g (f' x) x := fun x hx => (hf x hx).sub_const m
  -- `g` is continuous on the compact interval, hence bounded, hence square integrable.
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) := by
    have hgc : ContinuousOn g (Icc a b) := by
      rw [← uIcc_of_le hab.le]
      exact hfc.sub continuousOn_const
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
    exact MemLp.of_bound ((hgc.aestronglyMeasurable measurableSet_Icc).mono_set
      Ioc_subset_Icc_self) C
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))
  have hf'int : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hf'.integrable one_le_two)
  -- Coefficientwise comparison of the Fourier coefficients of `g = f - m` and `f'`.
  have hcoeff (n : ℤ) : ‖fourierCoeffOn hab g n‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab f' n‖ ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · -- The zeroth coefficient of `g` is its mean, which vanishes.
      have hzero : fourierCoeffOn hab g 0 = 0 := by
        have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
        have hba' : (b : ℂ) - a ≠ 0 := by exact_mod_cast hba.ne'
        simp [fourierCoeffOn_eq_integral, g, m, interval_average_eq,
          intervalIntegral.integral_sub hfi intervalIntegrable_const, hba']
      simpa [hzero] using (by positivity :
        0 ≤ ((b - a) / (2 * π)) ^ 2 * ‖fourierCoeffOn hab f' 0‖ ^ 2)
    · -- Integration by parts: the coefficient of `g` is that of `f'` over `-2πin / (b - a)`.
      have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hnorm : ‖fourierCoeffOn hab g n‖ =
          (b - a) / (2 * π) / |(n : ℝ)| * ‖fourierCoeffOn hab f' n‖ := by
        rw [fourierCoeffOn_of_hasDerivAt hab hn hg hf'int]
        simp [g, hfab, ← ofReal_sub, abs_of_pos hba, abs_of_pos Real.pi_pos]
        field_simp
      rw [hnorm, mul_pow]
      gcongr ?_ ^ 2 * _
      exact div_le_self (by positivity) hn'
  have hsum := hasSum_le hcoeff (hasSum_sq_fourierCoeffOn hab hgL2)
    ((hasSum_sq_fourierCoeffOn hab hf').mul_left (((b - a) / (2 * π)) ^ 2))
  rw [smul_eq_mul, smul_eq_mul, mul_left_comm] at hsum
  exact le_of_mul_le_mul_left hsum (inv_pos.2 hba)

/-- **Wirtinger's inequality.** A function on `[a, b]` with `f a = f b`, valued in a
finite-dimensional real inner product space and with square-integrable derivative, deviates from
its mean in `L²` by at most `(b - a) / (2π)` times the `L²` norm of its derivative. -/
theorem integral_norm_sub_average_sq_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (hab : a < b) {f f' : ℝ → V}
    (hf : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set e := stdOrthonormalBasis ℝ V
  -- The `i`-th coordinate, read as a complex number.
  let L (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℂ := ofRealCLM.comp (innerSL ℝ (e i))
  have hL (i) (v : V) : ‖L i v‖ ^ 2 = ⟪e i, v⟫ ^ 2 := by simp [L]
  have hfc : ContinuousOn f [[a, b]] := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable
  have hm (i) : ⨍ y in a..b, L i (f y) = L i (⨍ y in a..b, f y) := by
    rw [interval_average_eq, interval_average_eq, (L i).map_smul,
      (L i).intervalIntegral_comp_comm hfi]
  have hcoord (i) : ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, f' x⟫ ^ 2 := by
    have h := integral_norm_sub_average_sq_le_complex hab
      (f := fun x => L i (f x)) (f' := fun x => L i (f' x))
      (fun x hx => (L i).hasFDerivAt.comp_hasDerivAt x (hf x hx)) (by rw [hfab])
      ((L i).comp_memLp' hf')
    simp_rw [hm i, ← (L i).map_sub, hL i] at h
    exact h
  have hint₁ (i) : IntervalIntegrable (fun x => ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2) volume a b :=
    ((continuousOn_const.inner (hfc.sub continuousOn_const)).pow 2).intervalIntegrable
  have hint₂ (i) : IntervalIntegrable (fun x => ⟪e i, f' x⟫ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((innerSL ℝ (e i)).comp_memLp' hf').integrable_sq
  calc ∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2
      = ∑ i, ∫ x in a..b, ⟪e i, f x - ⨍ y in a..b, f y⟫ ^ 2 := by
        simp_rw [← e.sum_sq_inner_right]
        exact intervalIntegral.integral_finsetSum fun i _ => hint₁ i
    _ ≤ ∑ i, ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ⟪e i, f' x⟫ ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
        rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun i _ => hint₂ i]
        simp_rw [e.sum_sq_inner_right]

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
          exact TauCeti.integral_norm_sub_average_sq_le hab hf hfab hf'
      _ = c * ∫ x in a..b, ‖f' x‖ ^ 2 := by field_simp
  calc ‖B‖ * (((c⁻¹ * ∫ x in a..b, ‖f x - m‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2)
      ≤ ‖B‖ * (((c * ∫ x in a..b, ‖f' x‖ ^ 2) + c * ∫ x in a..b, ‖f' x‖ ^ 2) / 2) := by
        gcongr
    _ = ‖B‖ * c * ∫ x in a..b, ‖f' x‖ ^ 2 := by ring

end ContinuousLinearMap
