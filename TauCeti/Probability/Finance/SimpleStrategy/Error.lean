/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weighted errors for stock gains

A stock with drift coefficient `D` and diffusion coefficient `V` requires one holding
approximation to converge in two different topologies: absolute drift variation and square
diffusion energy. For a target holding `a`, use the single weight
`w = |D| / (1 + |a|) + V²`. Its square-error integral controls both errors, even when the
holding has only integrable drift gains rather than square-integrable drift gains.

The drift estimate is Cauchy–Schwarz with the complementary weight `|D| (1 + |a|)`.
This weight is integrable as soon as both the asset drift and the target drift gains are
integrable. All results work for an arbitrary time measure, so they apply pathwise on a
finite horizon without any expected-energy or expected-variation assumption. Signed and
vanishing coefficients are allowed. These are error estimates, not constructions of
stochastic integrals. The drift and diffusion results are independent; measurability is
required only for the respective gain or square energy, not for each factor separately.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Filter Real

namespace TauCeti.Finance

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {a D V e : α → ℝ}

/-- Asset drift integrability and measurable target drift gains give finite mass for
`w = |D| / (1 + |a|) + V²`, without requiring measurable holdings separately. -/
theorem integrable_abs_div_one_add_abs_add_sq (hD : Integrable D μ)
    (haD : AEStronglyMeasurable (fun x ↦ a x * D x) μ)
    (hV : Integrable (fun x ↦ V x ^ 2) μ) :
    Integrable (fun x ↦ |D x| / (1 + |a x|) + V x ^ 2) μ := by
  have hm : AEStronglyMeasurable (fun x ↦ |D x| / (1 + |a x|)) μ := by
    have hmD := continuous_abs.comp_aestronglyMeasurable hD.aestronglyMeasurable
    have hmaD := continuous_abs.comp_aestronglyMeasurable haD
    convert (hmD.pow 2).div₀ (hmD.add hmaD) using 1
    ext x
    simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply]
    by_cases hd : D x = 0
    · simp [hd]
    · have hfactor : |D x| + |a x| * |D x| = |D x| * (1 + |a x|) := by ring
      rw [abs_mul, hfactor, pow_two, mul_div_mul_left _ _ (abs_ne_zero.mpr hd)]
  exact (hD.abs.mono_nonneg hm (ae_of_all _ fun x ↦ by positivity)
    (ae_of_all _ fun x ↦ div_le_self (abs_nonneg _) (by linarith [abs_nonneg (a x)]))).add hV

/-- Integrable target gains give finite target energy for the mixed weight, without
requiring finite drift-weight mass or measurable holdings separately. -/
theorem integrable_abs_div_one_add_abs_add_sq_mul_sq (hD : AEStronglyMeasurable D μ)
    (haD : Integrable (fun x ↦ a x * D x) μ)
    (haV : Integrable (fun x ↦ (a x * V x) ^ 2) μ) :
    Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * a x ^ 2) μ := by
  have hm : AEStronglyMeasurable (fun x ↦ |D x| / (1 + |a x|) * a x ^ 2) μ := by
    have hmD := continuous_abs.comp_aestronglyMeasurable hD
    have hmaD := continuous_abs.comp_aestronglyMeasurable haD.aestronglyMeasurable
    convert (hmaD.pow 2).div₀ (hmD.add hmaD) using 1
    ext x
    simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply]
    by_cases hd : D x = 0
    · simp [hd]
    · have hp : |D x| ≠ 0 := abs_ne_zero.mpr hd
      have hden : 1 + |a x| ≠ 0 := ne_of_gt (by positivity)
      have hfactor : |D x| + |a x| * |D x| = |D x| * (1 + |a x|) := by ring
      rw [abs_mul, hfactor]
      field_simp
      nlinarith [sq_abs (a x)]
  have hqa : Integrable (fun x ↦ |D x| / (1 + |a x|) * a x ^ 2) μ := by
    refine haD.abs.mono_nonneg hm
      (ae_of_all _ fun x ↦ by positivity) (ae_of_all _ fun x ↦ ?_)
    calc
      |D x| / (1 + |a x|) * a x ^ 2 = |D x| * (|a x| ^ 2 / (1 + |a x|)) := by
        rw [sq_abs]
        ring
      _ ≤ |D x| * |a x| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply (div_le_iff₀ (by positivity : 0 < 1 + |a x|)).2
        nlinarith [abs_nonneg (a x)]
      _ = |a x * D x| := by rw [abs_mul, mul_comm]
  convert hqa.add haV using 1
  ext x
  simp only [Pi.add_apply]
  ring

/-- The complementary drift weight is integrable under the asset and target drift-gain
integrability conditions. -/
theorem integrable_abs_mul_one_add_abs (hD : Integrable D μ)
    (haD : Integrable (fun x ↦ a x * D x) μ) :
    Integrable (fun x ↦ |D x| * (1 + |a x|)) μ := by
  convert hD.abs.add haD.abs using 1
  ext x
  simp only [Pi.add_apply, abs_mul]
  ring

-- Share the stock-specific square-root domination and Hölder argument between the two
-- independent public drift results.
private theorem drift_error_estimate
    (heD : AEStronglyMeasurable (fun x ↦ e x * D x) μ)
    (hA : Integrable (fun x ↦ |D x| * (1 + |a x|)) μ)
    (hE : Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2) μ) :
    Integrable (fun x ↦ e x * D x) μ ∧
    (∫ x, |e x * D x| ∂μ) ≤
      √(∫ x, |D x| * (1 + |a x|) ∂μ) *
        √(∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2 ∂μ) := by
  let A := fun x ↦ |D x| * (1 + |a x|)
  let E := fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2
  have hA0 (x) : 0 ≤ A x := by dsimp [A]; positivity
  have hE0 (x) : 0 ≤ E x := by dsimp [E]; positivity
  have hsA : MemLp (fun x ↦ √(A x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable)).2
    convert hA using 1
    ext x
    exact sq_sqrt (hA0 x)
  have hsE : MemLp (fun x ↦ √(E x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (continuous_sqrt.comp_aestronglyMeasurable hE.aestronglyMeasurable)).2
    convert hE using 1
    ext x
    exact sq_sqrt (hE0 x)
  have hprod : Integrable (fun x ↦ √(A x) * √(E x)) μ := hsA.integrable_mul hsE
  -- The first summand of the error weight pairs exactly with the drift mass.
  have hpoint (x) : |e x * D x| ≤ √(A x) * √(E x) := by
    have hid : A x * (|D x| / (1 + |a x|) * e x ^ 2) = (e x * D x) ^ 2 := by
      dsimp [A]
      field_simp
      nlinarith [sq_abs (D x)]
    calc
      |e x * D x| = √((e x * D x) ^ 2) := (sqrt_sq_eq_abs _).symm
      _ ≤ √(A x * E x) := by
        apply sqrt_le_sqrt
        rw [← hid]
        apply mul_le_mul_of_nonneg_left _ (hA0 x)
        dsimp only [E]
        nlinarith [mul_nonneg (sq_nonneg (V x)) (sq_nonneg (e x))]
      _ = √(A x) * √(E x) := sqrt_mul (hA0 x) _
  have hDi : Integrable (fun x ↦ e x * D x) μ :=
    hprod.mono' heD (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hpoint x)
  refine ⟨hDi, ?_⟩
  calc
    (∫ x, |e x * D x| ∂μ) ≤ ∫ x, √(A x) * √(E x) ∂μ :=
      integral_mono_ae hDi.abs hprod (ae_of_all _ hpoint)
    _ ≤ √(∫ x, A x ∂μ) * √(∫ x, E x ∂μ) := by
      have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (ae_of_all μ fun x ↦ sqrt_nonneg (A x))
        (ae_of_all μ fun x ↦ sqrt_nonneg (E x)) (by simpa using hsA) (by simpa using hsE)
      simpa only [Real.rpow_two, sq_sqrt (hA0 _), sq_sqrt (hE0 _),
        ← one_div, ← sqrt_eq_rpow] using h

/-- Finite mixed weighted square error implies integrability of measurable drift gains. -/
theorem integrable_mul_of_integrable_abs_div_one_add_abs_add_sq_mul_sq
    (heD : AEStronglyMeasurable (fun x ↦ e x * D x) μ)
    (hA : Integrable (fun x ↦ |D x| * (1 + |a x|)) μ)
    (hE : Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2) μ) :
    Integrable (fun x ↦ e x * D x) μ :=
  (drift_error_estimate heD hA hE).1

/-- The drift L¹ error is bounded by the square roots of complementary drift mass and
mixed weighted square error. -/
theorem integral_abs_mul_le_sqrt_mul_sqrt
    (heD : AEStronglyMeasurable (fun x ↦ e x * D x) μ)
    (hA : Integrable (fun x ↦ |D x| * (1 + |a x|)) μ)
    (hE : Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2) μ) :
    (∫ x, |e x * D x| ∂μ) ≤
      √(∫ x, |D x| * (1 + |a x|) ∂μ) *
        √(∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2 ∂μ) :=
  (drift_error_estimate heD hA hE).2

/-- Finite mixed weighted square error implies integrability of measurable diffusion
square energy; no drift-mass hypothesis is needed. -/
theorem integrable_mul_sq_of_integrable_abs_div_one_add_abs_add_sq_mul_sq
    (heV : AEStronglyMeasurable (fun x ↦ (e x * V x) ^ 2) μ)
    (hE : Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2) μ) :
    Integrable (fun x ↦ (e x * V x) ^ 2) μ := by
  refine hE.mono_nonneg heV (ae_of_all _ fun x ↦ sq_nonneg _) (ae_of_all _ fun x ↦ ?_)
  have : 0 ≤ |D x| / (1 + |a x|) := by positivity
  nlinarith [mul_nonneg this (sq_nonneg (e x))]

/-- Diffusion square energy is bounded by the mixed weighted square error. -/
theorem integral_mul_sq_le
    (heV : AEStronglyMeasurable (fun x ↦ (e x * V x) ^ 2) μ)
    (hE : Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2) μ) :
    (∫ x, (e x * V x) ^ 2 ∂μ) ≤
      ∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2 ∂μ := by
  refine integral_mono_ae
    (integrable_mul_sq_of_integrable_abs_div_one_add_abs_add_sq_mul_sq heV hE) hE
    (ae_of_all _ fun x ↦ ?_)
  have : 0 ≤ |D x| / (1 + |a x|) := by positivity
  nlinarith [mul_nonneg this (sq_nonneg (e x))]

/-- Mixed weighted square-error convergence implies drift L¹ convergence. Integrability
and measurability are required only eventually along the index filter. -/
theorem tendsto_integral_abs_mul_of_tendsto_integral {ι : Type*} {l : Filter ι}
    {e : ι → α → ℝ}
    (hA : Integrable (fun x ↦ |D x| * (1 + |a x|)) μ)
    (heD : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ e i x * D x) μ)
    (hE : ∀ᶠ i in l, Integrable
      (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e i x ^ 2) μ)
    (hlim : Tendsto
      (fun i ↦ ∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e i x ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun i ↦ ∫ x, |e i x * D x| ∂μ) l (nhds 0) := by
  have hs := (tendsto_const_nhds (x := √(∫ x, |D x| * (1 + |a x|) ∂μ))).mul
    (Real.continuous_sqrt.continuousAt.tendsto.comp hlim)
  simp only [sqrt_zero, mul_zero] at hs
  refine squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun x ↦ abs_nonneg _) ?_ hs
  filter_upwards [heD, hE] with i hiD hiE
  exact integral_abs_mul_le_sqrt_mul_sqrt hiD hA hiE

/-- Mixed weighted square-error convergence implies diffusion square-energy convergence,
independently of drift integrability, with only eventual measurability and integrability. -/
theorem tendsto_integral_mul_sq_of_tendsto_integral {ι : Type*} {l : Filter ι}
    {e : ι → α → ℝ}
    (heV : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ (e i x * V x) ^ 2) μ)
    (hE : ∀ᶠ i in l, Integrable
      (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e i x ^ 2) μ)
    (hlim : Tendsto
      (fun i ↦ ∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e i x ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun i ↦ ∫ x, (e i x * V x) ^ 2 ∂μ) l (nhds 0) := by
  refine squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun x ↦ sq_nonneg _) ?_ hlim
  filter_upwards [heV, hE] with i hiV hiE
  exact integral_mul_sq_le hiV hiE

end TauCeti.Finance
