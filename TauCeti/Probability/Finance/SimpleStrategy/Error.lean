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
stochastic integrals.

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

/-- The asset and holding integrability conditions imply finite mass and target energy for
`w = |D| / (1 + |a|) + V²`. This permits weighted square approximation without imposing
square-integrable drift gains. -/
theorem integrable_stockErrorWeight (ha : AEStronglyMeasurable a μ) (hD : Integrable D μ)
    (haD : Integrable (fun x ↦ a x * D x) μ)
    (hV : Integrable (fun x ↦ V x ^ 2) μ)
    (haV : Integrable (fun x ↦ (V x * a x) ^ 2) μ) :
    Integrable (fun x ↦ |D x| / (1 + |a x|) + V x ^ 2) μ ∧
    Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * a x ^ 2) μ := by
  have hm : AEStronglyMeasurable (fun x ↦ |D x| / (1 + |a x|)) μ :=
    (continuous_abs.comp_aestronglyMeasurable hD.aestronglyMeasurable).div₀
      (aestronglyMeasurable_const.add (continuous_abs.comp_aestronglyMeasurable ha))
  have hq : Integrable (fun x ↦ |D x| / (1 + |a x|)) μ :=
    hD.abs.mono_nonneg hm (ae_of_all _ fun x ↦ by positivity)
      (ae_of_all _ fun x ↦ div_le_self (abs_nonneg _) (by linarith [abs_nonneg (a x)]))
  have hqa : Integrable (fun x ↦ |D x| / (1 + |a x|) * a x ^ 2) μ := by
    refine haD.abs.mono_nonneg (hm.mul (ha.pow 2))
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
  refine ⟨hq.add hV, ?_⟩
  convert hqa.add haV using 1
  ext x
  simp only [Pi.add_apply]
  ring

/-- Finite weighted square error gives integrable drift and diffusion errors, and bounds
the drift L¹ error and diffusion square energy. The drift mass is `∫ |D| (1 + |a|)`;
no square-integrability assumption on `a` against the drift variation is needed. -/
theorem stockGainsError_bound (hD : AEStronglyMeasurable D μ)
    (hV : AEStronglyMeasurable V μ) (he : AEStronglyMeasurable e μ)
    (hA : Integrable (fun x ↦ |D x| * (1 + |a x|)) μ)
    (hE : Integrable (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2) μ) :
    Integrable (fun x ↦ D x * e x) μ ∧
    Integrable (fun x ↦ (V x * e x) ^ 2) μ ∧
    (∫ x, |D x * e x| ∂μ) ≤
      √(∫ x, |D x| * (1 + |a x|) ∂μ) *
        √(∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2 ∂μ) ∧
    (∫ x, (V x * e x) ^ 2 ∂μ) ≤
      ∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e x ^ 2 ∂μ := by
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
  have hpoint (x) : |D x * e x| ≤ √(A x) * √(E x) := by
    have hid : A x * (|D x| / (1 + |a x|) * e x ^ 2) = (D x * e x) ^ 2 := by
      dsimp [A]
      field_simp
      nlinarith [sq_abs (D x)]
    calc
      |D x * e x| = √((D x * e x) ^ 2) := (sqrt_sq_eq_abs _).symm
      _ ≤ √(A x * E x) := by
        apply sqrt_le_sqrt
        rw [← hid]
        apply mul_le_mul_of_nonneg_left _ (hA0 x)
        dsimp only [E]
        nlinarith [mul_nonneg (sq_nonneg (V x)) (sq_nonneg (e x))]
      _ = √(A x) * √(E x) := sqrt_mul (hA0 x) _
  -- The diffusion energy is bounded by the second summand of the same weight.
  have hdiff (x) : (V x * e x) ^ 2 ≤ E x := by
    have : 0 ≤ |D x| / (1 + |a x|) := by positivity
    dsimp [E]
    nlinarith [mul_nonneg this (sq_nonneg (e x))]
  have hDi : Integrable (fun x ↦ D x * e x) μ :=
    hprod.mono' (hD.mul he) (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hpoint x)
  have hVi : Integrable (fun x ↦ (V x * e x) ^ 2) μ :=
    hE.mono_nonneg ((hV.mul he).pow 2) (ae_of_all _ fun x ↦ sq_nonneg _) (ae_of_all _ hdiff)
  -- Apply native Hölder to the two square roots, with conjugate exponents 2 and 2.
  refine ⟨hDi, hVi, ?_, integral_mono_ae hVi hE (ae_of_all _ hdiff)⟩
  calc
    (∫ x, |D x * e x| ∂μ) ≤ ∫ x, √(A x) * √(E x) ∂μ :=
      integral_mono_ae hDi.abs hprod (ae_of_all _ hpoint)
    _ ≤ √(∫ x, A x ∂μ) * √(∫ x, E x ∂μ) := by
      have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (ae_of_all μ fun x ↦ sqrt_nonneg (A x))
        (ae_of_all μ fun x ↦ sqrt_nonneg (E x)) (by simpa using hsA) (by simpa using hsE)
      simpa only [Real.rpow_two, sq_sqrt (hA0 _), sq_sqrt (hE0 _),
        ← one_div, ← sqrt_eq_rpow] using h

/-- Convergence in the single stock-error weight implies simultaneous drift L¹ and diffusion
square-energy convergence for the same holding errors. This is a pathwise statement: the
measure can be restricted time measure on any fixed sample path. -/
theorem tendsto_stockGainsErrors_of_weighted {ι : Type*} {l : Filter ι} {e : ι → α → ℝ}
    (hD : Integrable D μ) (haD : Integrable (fun x ↦ a x * D x) μ)
    (hV : AEStronglyMeasurable V μ) (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hE : ∀ i, Integrable
      (fun x ↦ (|D x| / (1 + |a x|) + V x ^ 2) * e i x ^ 2) μ)
    (hlim : Tendsto
      (fun i ↦ ∫ x, (|D x| / (1 + |a x|) + V x ^ 2) * e i x ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun i ↦ ∫ x, |D x * e i x| ∂μ) l (nhds 0) ∧
    Tendsto (fun i ↦ ∫ x, (V x * e i x) ^ 2 ∂μ) l (nhds 0) := by
  have hA : Integrable (fun x ↦ |D x| * (1 + |a x|)) μ := by
    convert hD.abs.add haD.abs using 1
    ext x
    simp only [Pi.add_apply, abs_mul]
    ring
  have hb i := stockGainsError_bound hD.aestronglyMeasurable hV (he i) hA (hE i)
  have hs := (tendsto_const_nhds (x := √(∫ x, |D x| * (1 + |a x|) ∂μ))).mul
    (Real.continuous_sqrt.continuousAt.tendsto.comp hlim)
  simp only [sqrt_zero, mul_zero] at hs
  exact ⟨squeeze_zero (fun i ↦ integral_nonneg fun x ↦ abs_nonneg _) (fun i ↦ (hb i).2.2.1) hs,
    squeeze_zero (fun i ↦ integral_nonneg fun x ↦ sq_nonneg _) (fun i ↦ (hb i).2.2.2) hlim⟩

end TauCeti.Finance
