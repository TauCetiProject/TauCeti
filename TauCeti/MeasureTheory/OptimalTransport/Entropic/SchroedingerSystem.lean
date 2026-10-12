/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The Schrödinger system for a bounded kernel

Let `μ` and `ν` be finite measures of equal mass on `X` and `Y`, and let `g : X × Y → ℝ` be a
bounded measurable function. The *Schrödinger system* asks for potentials `φ` on `X` and `ψ` on `Y`
such that `exp (φ(x) + ψ(y) + g(x, y))` is the density, against `μ.prod ν`, of a coupling of `μ` and
`ν`; that is,

`φ x = -log ∫ exp (g (x, y) + ψ y) dν(y)` and `ψ y = -log ∫ exp (g (x, y) + φ x) dμ(x)`

for `μ`-almost every `x` and `ν`-almost every `y`.

This file proves that the system has a solution by bounded measurable potentials
(`TauCeti.exists_isCoupling_withDensity_exp_add`). The two equations are the two half-steps of the
Sinkhorn iteration, and the solution is found as a fixed point of a full Sinkhorn sweep. If
`|g| ≤ M`, a half-step contracts the oscillation `sup (u - v) - inf (u - v)` of the difference of
two potentials by the factor `1 - exp (-4M)`. Indeed, the kernels at two points of `X` differ by at
most the factor `exp (2M)`, so after normalisation each of the two probability measures
`exp (g (x, y) + v y) dν(y) / ∫ exp (g (x, ·) + v) dν` dominates `exp (-4M)` times the other, and
the contraction then follows from the convexity of `exp`. Normalised to vanish at a base point, the
iterates of the sweep therefore converge uniformly, at a geometric rate, to a fixed point up to an
additive constant, and equality of the masses of `μ` and `ν` forces that constant to vanish.

The solution identifies the minimizers of the two entropic transport problems of
`TauCeti/MeasureTheory/OptimalTransport/Entropic/Basic.lean` when the log-density of the reference
measure is bounded.

* For a reference measure `R` with density `exp g` against `μ.prod ν`, the Schrödinger minimizer has
  density `exp (φ(x) + ψ(y))` against `R`
  (`TauCeti.IsCoupling.exists_eq_withDensity_exp_add_of_klDiv_eq_schroedingerValue`).
* For a bounded measurable cost `c` and a positive temperature `ε`, the entropically regularised
  transport cost is attained by a coupling with density `exp ((φ(x) + ψ(y) - c(x, y)) / ε)` against
  `μ.prod ν` (`TauCeti.exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost`).

Boundedness of `g` is what makes the Sinkhorn sweep a contraction. The general theorem, for a
reference measure equivalent to `μ.prod ν` that admits a coupling of finite relative entropy, needs
a different argument and is not proved here.

## Main statements

* `TauCeti.exists_isCoupling_withDensity_exp_add`: the Schrödinger system for a bounded measurable
  kernel has a solution by bounded measurable potentials.
* `TauCeti.IsCoupling.exists_eq_withDensity_exp_add_of_klDiv_eq_schroedingerValue`: the Schrödinger
  minimizer for a reference measure with bounded log-density against `μ.prod ν` has a product
  density.
* `TauCeti.exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost`: for a bounded cost
  the entropic optimal plan exists and has a Gibbs density with bounded potentials.

## References

* R. Fortet, *Résolution d'un système d'équations de M. Schrödinger*, J. Math. Pures Appl. 19
  (1940), 83–105, for the existence of solutions of the Schrödinger system for bounded kernels.
* J. M. Borwein, A. S. Lewis and R. D. Nussbaum, *Entropy minimization, DAD problems, and doubly
  stochastic kernels*, J. Funct. Anal. 123 (1994), 264–307, and Y. Chen, T. T. Georgiou and M.
  Pavon, *Entropic and displacement interpolation: a computational approach using the Hilbert
  metric*, SIAM J. Appl. Math. 76 (2016), 2375–2396, for the Sinkhorn iteration as a contraction for
  positive kernels bounded above and below.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  Theorem 2.1, for the product form of the density of the Schrödinger minimizer.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal NNReal

namespace TauCeti

section HalfStep

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] {ν : Measure B}
  {h : A × B → ℝ} {M : ℝ} {ψ ψ₁ ψ₂ : B → ℝ}

/-- `log ∫ exp (h (a, b) + ψ b) dν(b)`, the logarithm of the partition function of the kernel
`exp h` tilted by `exp ψ`. A Sinkhorn half-step replaces the potential on `A` by its negative. -/
private def logIntegralExp (h : A × B → ℝ) (ν : Measure B) (ψ : B → ℝ) (a : A) : ℝ :=
  Real.log (∫ b, Real.exp (h (a, b) + ψ b) ∂ν)

private theorem measurable_logIntegralExp [SFinite ν] (hh : Measurable h) (hψ : Measurable ψ) :
    Measurable (logIntegralExp h ν ψ) := by
  have : StronglyMeasurable fun z : A × B ↦ Real.exp (h z + ψ z.2) :=
    (by fun_prop : Measurable fun z : A × B ↦ Real.exp (h z + ψ z.2)).stronglyMeasurable
  exact this.integral_prod_right'.measurable.log

/-- Integrating `exp (h (a, b) + ψ b + t)` against `ν` gives `exp (t + logIntegralExp h ν ψ a)`. -/
private theorem lintegral_ofReal_exp_add [IsFiniteMeasure ν] (hν : ν ≠ 0) (hh : Measurable h)
    (hM : ∀ z, |h z| ≤ M) (hψ : Measurable ψ) {C : ℝ} (hC : ∀ b, |ψ b| ≤ C) (a : A) (t : ℝ) :
    ∫⁻ b, ENNReal.ofReal (Real.exp (h (a, b) + ψ b + t)) ∂ν =
      ENNReal.ofReal (Real.exp (t + logIntegralExp h ν ψ a)) := by
  have := NeZero.mk hν
  have hint : Integrable (fun b ↦ Real.exp (h (a, b) + ψ b)) ν := by
    simpa using ProbabilityTheory.integrable_exp_mul_of_le 1 (M + C) zero_le_one (by fun_prop)
      (ae_of_all _ fun b ↦ by linarith [(abs_le.1 (hM (a, b))).2, (abs_le.1 (hC b)).2])
  have hsplit : (fun b ↦ Real.exp (h (a, b) + ψ b + t)) =
      fun b ↦ Real.exp (h (a, b) + ψ b) * Real.exp t := funext fun b ↦ Real.exp_add _ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hsplit ▸ hint.mul_const _)
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), hsplit, integral_mul_const, logIntegralExp,
    Real.exp_add, Real.exp_log (integral_exp_pos hint), mul_comm]

private theorem abs_logIntegralExp_le [IsFiniteMeasure ν] (hν : ν ≠ 0) (hh : Measurable h)
    (hM : ∀ z, |h z| ≤ M) (hψ : Measurable ψ) {C : ℝ} (hC : ∀ b, |ψ b| ≤ C) (a : A) :
    |logIntegralExp h ν ψ a| ≤ M + C + |Real.log (ν.real univ)| := by
  have hν' : 0 < ν.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hν) (measure_ne_top _ _)
  have hint : Integrable (fun b ↦ Real.exp (h (a, b) + ψ b)) ν := by
    simpa using ProbabilityTheory.integrable_exp_mul_of_le 1 (M + C) zero_le_one (by fun_prop)
      (ae_of_all _ fun b ↦ by linarith [(abs_le.1 (hM (a, b))).2, (abs_le.1 (hC b)).2])
  have hlo : Real.exp (-(M + C)) * ν.real univ ≤ ∫ b, Real.exp (h (a, b) + ψ b) ∂ν := by
    rw [mul_comm, ← smul_eq_mul, ← integral_const]
    refine integral_mono (integrable_const _) hint fun b ↦ Real.exp_le_exp.2 ?_
    linarith [(abs_le.1 (hM (a, b))).1, (abs_le.1 (hC b)).1]
  have hhi : ∫ b, Real.exp (h (a, b) + ψ b) ∂ν ≤ Real.exp (M + C) * ν.real univ := by
    rw [mul_comm, ← smul_eq_mul, ← integral_const]
    refine integral_mono hint (integrable_const _) fun b ↦ Real.exp_le_exp.2 ?_
    linarith [(abs_le.1 (hM (a, b))).2, (abs_le.1 (hC b)).2]
  have hpos : 0 < Real.exp (-(M + C)) * ν.real univ := by positivity
  have h₁ := Real.log_le_log hpos hlo
  have h₂ := Real.log_le_log (hpos.trans_le hlo) hhi
  rw [Real.log_mul (Real.exp_pos _).ne' hν'.ne', Real.log_exp] at h₁
  rw [Real.log_mul (Real.exp_pos _).ne' hν'.ne', Real.log_exp] at h₂
  unfold logIntegralExp
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le (Real.log (ν.real univ)), le_abs_self (Real.log (ν.real univ))]

/-- **The half-step contracts oscillations**, in bracket form: if `m ≤ ψ₁ - ψ₂ ≤ m + ω`, then the
difference of the log-partition functions of `ψ₁` and `ψ₂` has oscillation at most
`(1 - exp (-4M)) * ω`, where `|h| ≤ M`. -/
private theorem logIntegralExp_sub_sub_le_of_le [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hh : Measurable h) (hM : ∀ z, |h z| ≤ M) (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ b, |ψ₁ b| ≤ C₁) (hC₂ : ∀ b, |ψ₂ b| ≤ C₂) {m ω : ℝ}
    (hm : ∀ b, m ≤ ψ₁ b - ψ₂ b) (hmω : ∀ b, ψ₁ b - ψ₂ b ≤ m + ω) (a a' : A) :
    (logIntegralExp h ν ψ₁ a - logIntegralExp h ν ψ₂ a) -
      (logIntegralExp h ν ψ₁ a' - logIntegralExp h ν ψ₂ a') ≤
        (1 - Real.exp (-(4 * M))) * ω := by
  have := NeZero.mk hν
  have hM0 : 0 ≤ M := by
    obtain ⟨b₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hν)
    exact (abs_nonneg _).trans (hM (a, b₀))
  -- The four partition functions `A₁, A₂` at `a` and `B₁, B₂` at `a'`.
  have hi (a : A) {ψ : B → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ b, |ψ b| ≤ C) :
      Integrable (fun b ↦ Real.exp (h (a, b) + ψ b)) ν := by
    simpa using ProbabilityTheory.integrable_exp_mul_of_le 1 (M + C) zero_le_one (by fun_prop)
      (ae_of_all _ fun b ↦ by linarith [(abs_le.1 (hM (a, b))).2, (abs_le.1 (hC b)).2])
  set A₁ := ∫ b, Real.exp (h (a, b) + ψ₁ b) ∂ν
  set A₂ := ∫ b, Real.exp (h (a, b) + ψ₂ b) ∂ν
  set B₁ := ∫ b, Real.exp (h (a', b) + ψ₁ b) ∂ν
  set B₂ := ∫ b, Real.exp (h (a', b) + ψ₂ b) ∂ν
  have hA₁ : 0 < A₁ := integral_exp_pos (hi a hψ₁ hC₁)
  have hA₂ : 0 < A₂ := integral_exp_pos (hi a hψ₂ hC₂)
  have hB₁ : 0 < B₁ := integral_exp_pos (hi a' hψ₁ hC₁)
  have hB₂ : 0 < B₂ := integral_exp_pos (hi a' hψ₂ hC₂)
  -- `exp m * A₂ ≤ A₁ ≤ exp (m + ω) * A₂`.
  have hA₁lo : Real.exp m * A₂ ≤ A₁ := by
    rw [← integral_const_mul]
    refine integral_mono ((hi a hψ₂ hC₂).const_mul _) (hi a hψ₁ hC₁) fun b ↦ ?_
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [hm b]
  have hA₁hi : A₁ ≤ Real.exp (m + ω) * A₂ := by
    rw [← integral_const_mul]
    refine integral_mono (hi a hψ₁ hC₁) ((hi a hψ₂ hC₂).const_mul _) fun b ↦ ?_
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [hmω b]
  -- The kernels at `a` and `a'` differ at most by the factor `exp (2M)`.
  have hB₂A₂ : Real.exp (-(2 * M)) * B₂ ≤ A₂ := by
    rw [← integral_const_mul]
    refine integral_mono ((hi a' hψ₂ hC₂).const_mul _) (hi a hψ₂ hC₂) fun b ↦ ?_
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [(abs_le.1 (hM (a, b))).1, (abs_le.1 (hM (a', b))).2]
  have hBA : Real.exp (-(2 * M)) * (A₁ - Real.exp m * A₂) ≤ B₁ - Real.exp m * B₂ := by
    have hfa := (hi a hψ₁ hC₁).sub ((hi a hψ₂ hC₂).const_mul (Real.exp m))
    have hfa' := (hi a' hψ₁ hC₁).sub ((hi a' hψ₂ hC₂).const_mul (Real.exp m))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi a hψ₁ hC₁)
      ((hi a hψ₂ hC₂).const_mul _), ← integral_const_mul, ← integral_sub (hi a' hψ₁ hC₁)
      ((hi a' hψ₂ hC₂).const_mul _)]
    refine integral_mono (hfa.const_mul _) hfa' fun b ↦ ?_
    have hsplit (a'' : A) : Real.exp (h (a'', b) + ψ₁ b) - Real.exp m *
        Real.exp (h (a'', b) + ψ₂ b) =
          Real.exp (h (a'', b) + ψ₂ b) * (Real.exp (ψ₁ b - ψ₂ b) - Real.exp m) := by
      simp only [mul_sub, ← Real.exp_add]
      ring_nf
    simp only [hsplit]
    rw [← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (sub_nonneg.2 (Real.exp_le_exp.2 (hm b)))
    linarith [(abs_le.1 (hM (a, b))).2, (abs_le.1 (hM (a', b))).1]
  -- With `s = exp (-4M)`: `s * A₁ * B₂ + (1 - s) * exp m * A₂ * B₂ ≤ B₁ * A₂`.
  have hss : Real.exp (-(2 * M)) * Real.exp (-(2 * M)) = Real.exp (-(4 * M)) := by
    rw [← Real.exp_add]
    ring_nf
  set s := Real.exp (-(4 * M))
  have hkey : s * A₁ * B₂ + (1 - s) * Real.exp m * A₂ * B₂ ≤ B₁ * A₂ := by
    have h₁ : 0 ≤ A₁ - Real.exp m * A₂ := sub_nonneg.2 hA₁lo
    have h₂ := mul_le_mul hBA hB₂A₂ (by positivity)
      ((mul_nonneg (Real.exp_pos _).le h₁).trans hBA)
    have h₃ : Real.exp (-(2 * M)) * (A₁ - Real.exp m * A₂) * (Real.exp (-(2 * M)) * B₂) =
        s * (A₁ - Real.exp m * A₂) * B₂ := by
      rw [← hss]
      ring
    rw [h₃] at h₂
    linarith
  -- With `E = exp ((1 - s) * ω)`, convexity of `exp` and `A₁ ≤ exp (m + ω) * A₂` give
  -- `A₁ ≤ E * (s * A₁ + (1 - s) * exp m * A₂)`, which with `hkey` yields `A₁ * B₂ ≤ E * (A₂ * B₁)`.
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : s ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hconv : Real.exp (s * ω) ≤ s * Real.exp ω + (1 - s) := by
    simpa using convexOn_exp.2 (mem_univ ω) (mem_univ 0) hs0.le (sub_nonneg.2 hs1) (by ring)
  set E := Real.exp ((1 - s) * ω)
  have hE : E * Real.exp (s * ω) = Real.exp ω := by
    rw [← Real.exp_add]
    ring_nf
  have hEpos : 0 < E := Real.exp_pos _
  have h₁ : A₁ * Real.exp ω ≤
      E * (s * A₁ * Real.exp ω + (1 - s) * Real.exp m * Real.exp ω * A₂) := by
    have h₁a : A₁ * Real.exp ω = E * A₁ * Real.exp (s * ω) := by
      rw [← hE]
      ring
    have h₁b := mul_le_mul_of_nonneg_left hconv (mul_nonneg hEpos.le hA₁.le)
    have h₁c := mul_le_mul_of_nonneg_left ((Real.exp_add m ω) ▸ hA₁hi)
      (mul_nonneg hEpos.le (sub_nonneg.2 hs1))
    linarith
  have h₂ : A₁ ≤ E * (s * A₁ + (1 - s) * Real.exp m * A₂) := by
    have hω0 := Real.exp_pos ω
    nlinarith [h₁]
  have hmain : A₁ * B₂ ≤ E * (A₂ * B₁) := by nlinarith [hkey, h₂, hB₂, hEpos]
  unfold logIntegralExp
  have := Real.log_le_log (by positivity) hmain
  rw [Real.log_mul hA₁.ne' hB₂.ne', Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_exp, Real.log_mul hA₂.ne' hB₁.ne'] at this
  linarith

/-- **The half-step contracts oscillations.** If the difference of two potentials on `B` has
oscillation at most `ω`, then the difference of their log-partition functions on `A` has
oscillation at most `(1 - exp (-4M)) * ω`, where `|h| ≤ M`. -/
private theorem logIntegralExp_sub_sub_le [IsFiniteMeasure ν] (hν : ν ≠ 0) (hh : Measurable h)
    (hM : ∀ z, |h z| ≤ M) (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂) {C₁ C₂ : ℝ}
    (hC₁ : ∀ b, |ψ₁ b| ≤ C₁) (hC₂ : ∀ b, |ψ₂ b| ≤ C₂) {ω : ℝ}
    (hω : ∀ b b', (ψ₁ b - ψ₂ b) - (ψ₁ b' - ψ₂ b') ≤ ω) (a a' : A) :
    (logIntegralExp h ν ψ₁ a - logIntegralExp h ν ψ₂ a) -
      (logIntegralExp h ν ψ₁ a' - logIntegralExp h ν ψ₂ a') ≤
        (1 - Real.exp (-(4 * M))) * ω := by
  obtain ⟨b₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hν)
  have : Nonempty B := ⟨b₀⟩
  -- Bracket `ψ₁ - ψ₂` between its infimum `m` and `m + ω`.
  have hbdd : BddBelow (range fun b ↦ ψ₁ b - ψ₂ b) :=
    ⟨ψ₁ b₀ - ψ₂ b₀ - ω, by rintro _ ⟨b, rfl⟩; linarith [hω b₀ b]⟩
  refine logIntegralExp_sub_sub_le_of_le hν hh hM hψ₁ hψ₂ hC₁ hC₂ (m := ⨅ b, (ψ₁ b - ψ₂ b))
    (fun b ↦ ciInf_le hbdd b) (fun b ↦ ?_) a a'
  have : ψ₁ b - ψ₂ b - ω ≤ ⨅ b, (ψ₁ b - ψ₂ b) := le_ciInf fun b' ↦ by linarith [hω b b']
  linarith

end HalfStep

section Sweep

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {g : X × Y → ℝ} {M : ℝ}

/-- One sweep of the Sinkhorn iteration on the potential `ψ` on `Y`: first the row potential
`φ x = -log ∫ exp (g (x, y) + ψ y) dν(y)`, then the column potential
`y ↦ -log ∫ exp (g (x, y) + φ x) dμ(x)`. -/
private def sinkhornSweep (g : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) (ψ : Y → ℝ) :
    Y → ℝ :=
  fun y ↦ -logIntegralExp (g ∘ Prod.swap) μ (fun x ↦ -logIntegralExp g ν ψ x) y

private theorem measurable_sinkhornSweep [SFinite μ] [SFinite ν] (hg : Measurable g) {ψ : Y → ℝ}
    (hψ : Measurable ψ) : Measurable (sinkhornSweep g μ ν ψ) :=
  (measurable_logIntegralExp (hg.comp measurable_swap)
    (measurable_logIntegralExp hg hψ).neg).neg

private theorem abs_sinkhornSweep_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) {ψ : Y → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) (y : Y) :
    |sinkhornSweep g μ ν ψ y| ≤
      M + (M + C + |Real.log (ν.real univ)|) + |Real.log (μ.real univ)| := by
  rw [sinkhornSweep, abs_neg]
  exact abs_logIntegralExp_le hμ (hg.comp measurable_swap) (fun z ↦ hgM z.swap)
    (measurable_logIntegralExp hg hψ).neg
    (fun x ↦ (abs_neg _).trans_le (abs_logIntegralExp_le hν hg hgM hψ hC x)) y

/-- **A Sinkhorn sweep contracts oscillations** by the factor `(1 - exp (-4M)) ^ 2`. -/
private theorem sinkhornSweep_sub_sub_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) {ψ₁ ψ₂ : Y → ℝ}
    (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂) {C₁ C₂ : ℝ} (hC₁ : ∀ y, |ψ₁ y| ≤ C₁)
    (hC₂ : ∀ y, |ψ₂ y| ≤ C₂) {ω : ℝ} (hω : ∀ y y', (ψ₁ y - ψ₂ y) - (ψ₁ y' - ψ₂ y') ≤ ω)
    (y y' : Y) :
    (sinkhornSweep g μ ν ψ₁ y - sinkhornSweep g μ ν ψ₂ y) -
      (sinkhornSweep g μ ν ψ₁ y' - sinkhornSweep g μ ν ψ₂ y') ≤
        (1 - Real.exp (-(4 * M))) ^ 2 * ω := by
  have hrow := logIntegralExp_sub_sub_le hν hg hgM hψ₁ hψ₂ hC₁ hC₂ hω
  have hcol := logIntegralExp_sub_sub_le (ν := μ) (ψ₁ := fun x ↦ -logIntegralExp g ν ψ₁ x)
    (ψ₂ := fun x ↦ -logIntegralExp g ν ψ₂ x) (ω := (1 - Real.exp (-(4 * M))) * ω) hμ
    (hg.comp measurable_swap)
    (fun z ↦ hgM z.swap) (measurable_logIntegralExp hg hψ₁).neg
    (measurable_logIntegralExp hg hψ₂).neg
    (fun x ↦ (abs_neg _).trans_le (abs_logIntegralExp_le hν hg hgM hψ₁ hC₁ x))
    (fun x ↦ (abs_neg _).trans_le (abs_logIntegralExp_le hν hg hgM hψ₂ hC₂ x))
    (fun x x' ↦ by linarith [hrow x' x]) y' y
  simp only [sinkhornSweep]
  rw [sq, mul_assoc]
  linarith [hcol]

/-- The Sinkhorn sweep normalised to vanish at the base point `y₀`. -/
private def normalizedSweep (g : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) (y₀ : Y)
    (ψ : Y → ℝ) : Y → ℝ :=
  fun y ↦ sinkhornSweep g μ ν ψ y - sinkhornSweep g μ ν ψ y₀

private theorem normalizedSweep_base (g : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) (y₀ : Y)
    (ψ : Y → ℝ) : normalizedSweep g μ ν y₀ ψ y₀ = 0 :=
  sub_self _

private theorem measurable_normalizedSweep [SFinite μ] [SFinite ν] (hg : Measurable g)
    {y₀ : Y} {ψ : Y → ℝ} (hψ : Measurable ψ) : Measurable (normalizedSweep g μ ν y₀ ψ) :=
  (measurable_sinkhornSweep hg hψ).sub_const _

private theorem exists_abs_normalizedSweep_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) {y₀ : Y}
    {ψ : Y → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) :
    ∃ C', ∀ y, |normalizedSweep g μ ν y₀ ψ y| ≤ C' := by
  refine ⟨2 * (M + (M + C + |Real.log (ν.real univ)|) + |Real.log (μ.real univ)|), fun y ↦ ?_⟩
  have h₁ := abs_sinkhornSweep_le hμ hν hg hgM hψ hC y
  have h₂ := abs_sinkhornSweep_le hμ hν hg hgM hψ hC y₀
  have := abs_sub (sinkhornSweep g μ ν ψ y) (sinkhornSweep g μ ν ψ y₀)
  rw [normalizedSweep]
  linarith

private theorem normalizedSweep_sub_sub_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) {y₀ : Y} {ψ₁ ψ₂ : Y → ℝ}
    (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂) (hb₁ : ∃ C, ∀ y, |ψ₁ y| ≤ C)
    (hb₂ : ∃ C, ∀ y, |ψ₂ y| ≤ C) {ω : ℝ} (hω : ∀ y y', (ψ₁ y - ψ₂ y) - (ψ₁ y' - ψ₂ y') ≤ ω)
    (y y' : Y) :
    (normalizedSweep g μ ν y₀ ψ₁ y - normalizedSweep g μ ν y₀ ψ₂ y) -
      (normalizedSweep g μ ν y₀ ψ₁ y' - normalizedSweep g μ ν y₀ ψ₂ y') ≤
        (1 - Real.exp (-(4 * M))) ^ 2 * ω := by
  obtain ⟨C₁, hC₁⟩ := hb₁
  obtain ⟨C₂, hC₂⟩ := hb₂
  have := sinkhornSweep_sub_sub_le hμ hν hg hgM hψ₁ hψ₂ hC₁ hC₂ hω y y'
  simp only [normalizedSweep]
  linarith

private theorem measurable_normalizedSweep_iterate [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) (y₀ : Y) (n : ℕ) :
    Measurable ((normalizedSweep g μ ν y₀)^[n] 0) ∧
      ∃ C, ∀ y, |(normalizedSweep g μ ν y₀)^[n] 0 y| ≤ C := by
  induction n with
  | zero => exact ⟨measurable_const, 0, fun y ↦ by simp⟩
  | succ n ih =>
    obtain ⟨hm, C, hC⟩ := ih
    rw [Function.iterate_succ_apply']
    exact ⟨measurable_normalizedSweep hg hm, exists_abs_normalizedSweep_le hμ hν hg hgM hm hC⟩

/-- **The normalised Sinkhorn iteration converges uniformly.** Started from `0`, the iterates of
the normalised sweep converge, geometrically in the uniform distance, to a bounded measurable
potential. -/
private theorem exists_dist_normalizedSweep_iterate_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) (y₀ : Y) :
    ∃ (ψ : Y → ℝ) (K : ℝ), Measurable ψ ∧ (∃ C, ∀ y, |ψ y| ≤ C) ∧ 0 ≤ K ∧
      ∀ n y, dist ((normalizedSweep g μ ν y₀)^[n] 0 y) (ψ y) ≤
        K * ((1 - Real.exp (-(4 * M))) ^ 2) ^ n := by
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hμ)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM (x₀, y₀))
  -- The contraction factor `r` of one sweep, and the iterates `χ n` started at `0`.
  set r := (1 - Real.exp (-(4 * M))) ^ 2
  have hr1 : r < 1 := pow_lt_one₀ (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
    (sub_lt_self _ (Real.exp_pos _)) two_ne_zero
  set χ : ℕ → Y → ℝ := fun n ↦ (normalizedSweep g μ ν y₀)^[n] 0
  have hχ_succ (n : ℕ) : χ (n + 1) = normalizedSweep g μ ν y₀ (χ n) :=
    Function.iterate_succ_apply' _ n 0
  have hχ_base (n : ℕ) : χ n y₀ = 0 := by
    cases n with
    | zero => rfl
    | succ n => rw [hχ_succ]; exact normalizedSweep_base g μ ν y₀ _
  have hχmb := measurable_normalizedSweep_iterate hμ hν hg hgM y₀
  -- Consecutive iterates differ by an oscillation at most `ω₀ * r ^ n`, hence, since they
  -- vanish at `y₀`, by at most `ω₀ * r ^ n` uniformly.
  obtain ⟨C₁, hC₁⟩ := (hχmb 1).2
  set ω₀ := 2 * C₁
  have hω₀ : 0 ≤ ω₀ := by linarith [abs_nonneg (χ 1 y₀), hC₁ y₀]
  have hosc (n : ℕ) (y y' : Y) :
      (χ (n + 1) y - χ n y) - (χ (n + 1) y' - χ n y') ≤ ω₀ * r ^ n := by
    induction n generalizing y y' with
    | zero =>
      have hχ₀ : χ 0 = 0 := rfl
      simp only [hχ₀, Pi.zero_apply, sub_zero, pow_zero, mul_one]
      linarith [(abs_le.1 (hC₁ y)).2, (abs_le.1 (hC₁ y')).1]
    | succ n ih =>
      have := normalizedSweep_sub_sub_le (y₀ := y₀) hμ hν hg hgM (hχmb (n + 1)).1 (hχmb n).1
        (hχmb (n + 1)).2 (hχmb n).2 ih y y'
      rw [← hχ_succ, ← hχ_succ] at this
      rw [pow_succ]
      linarith
  have hdist (y : Y) (n : ℕ) : dist (χ n y) (χ (n + 1) y) ≤ ω₀ * r ^ n := by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hosc n y y₀, hosc n y₀ y, hχ_base n, hχ_base (n + 1)]
  have hlim (y : Y) : ∃ l, Tendsto (fun n ↦ χ n y) atTop (𝓝 l) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r ω₀ hr1 (hdist y))
  choose ψ hψ using hlim
  have hest (n : ℕ) (y : Y) : dist (χ n y) (ψ y) ≤ ω₀ / (1 - r) * r ^ n := by
    rw [div_mul_eq_mul_div]
    exact dist_le_of_le_geometric_of_tendsto r ω₀ hr1 (hdist y) (hψ y) n
  refine ⟨ψ, ω₀ / (1 - r), measurable_of_tendsto_metrizable (fun n ↦ (hχmb n).1)
    (tendsto_pi_nhds.2 hψ), ⟨ω₀ / (1 - r), fun y ↦ ?_⟩, div_nonneg hω₀ (sub_pos.2 hr1).le, hest⟩
  have := hest 0 y
  have hχ₀ : χ 0 = 0 := rfl
  rwa [hχ₀, Pi.zero_apply, Real.dist_eq, zero_sub, abs_neg, pow_zero, mul_one] at this

/-- **The Sinkhorn sweep has a fixed point up to an additive constant.** The limit `ψ` of the
normalised iteration satisfies `sinkhornSweep g μ ν ψ = ψ + c`. -/
private theorem exists_sinkhornSweep_eq_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) :
    ∃ (ψ : Y → ℝ) (C c : ℝ), Measurable ψ ∧ (∀ y, |ψ y| ≤ C) ∧
      ∀ y, sinkhornSweep g μ ν ψ y = ψ y + c := by
  obtain ⟨y₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hν)
  obtain ⟨ψ, K, hψm, ⟨C, hψb⟩, hK, hest⟩ :=
    exists_dist_normalizedSweep_iterate_le hμ hν hg hgM y₀
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hμ)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM (x₀, y₀))
  refine ⟨ψ, C, sinkhornSweep g μ ν ψ y₀, hψm, hψb, fun y ↦ ?_⟩
  set r := (1 - Real.exp (-(4 * M))) ^ 2
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := pow_lt_one₀ (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
    (sub_lt_self _ (Real.exp_pos _)) two_ne_zero
  set χ : ℕ → Y → ℝ := fun n ↦ (normalizedSweep g μ ν y₀)^[n] 0
  have hmb := measurable_normalizedSweep_iterate hμ hν hg hgM y₀
  -- `χ (n + 1)` is the normalised sweep of `χ n`. It tends to `ψ`, and by the contraction it is
  -- within `2 * r * K * r ^ n` of the normalised sweep of `ψ`; so `ψ` is a fixed point.
  have hbound (n : ℕ) : |ψ y - normalizedSweep g μ ν y₀ ψ y| ≤ 3 * K * r ^ n := by
    have hdiff (y y' : Y) : (χ n y - ψ y) - (χ n y' - ψ y') ≤ 2 * (K * r ^ n) := by
      have h₁ := hest n y
      have h₂ := hest n y'
      rw [Real.dist_eq, abs_le] at h₁ h₂
      linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    have h₁ := normalizedSweep_sub_sub_le (y₀ := y₀) hμ hν hg hgM (hmb n).1 hψm (hmb n).2
      ⟨_, hψb⟩ hdiff y y₀
    have h₂ := normalizedSweep_sub_sub_le (y₀ := y₀) hμ hν hg hgM (hmb n).1 hψm (hmb n).2
      ⟨_, hψb⟩ hdiff y₀ y
    have h₃ := hest (n + 1) y
    rw [Function.iterate_succ_apply', Real.dist_eq, abs_le] at h₃
    rw [normalizedSweep_base, normalizedSweep_base] at h₁ h₂
    have hKr : 0 ≤ K * r ^ n := by positivity
    have hr₁ : K * r ^ (n + 1) ≤ K * r ^ n := by
      rw [pow_succ, ← mul_assoc]
      exact mul_le_of_le_one_right hKr hr1.le
    have hr₂ : r * (2 * (K * r ^ n)) ≤ 2 * (K * r ^ n) := by nlinarith
    rw [abs_le]
    constructor <;> linarith [h₃.1, h₃.2]
  have hlim0 : Tendsto (fun n : ℕ ↦ 3 * K * r ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (3 * K)
  have h0 := abs_nonpos_iff.1 (ge_of_tendsto' hlim0 hbound)
  simp only [normalizedSweep] at h0
  linarith

end Sweep

section Existence

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {g : X × Y → ℝ} {M : ℝ}

/-- **The Schrödinger system for a bounded kernel.** Let `μ` and `ν` be finite measures of equal
mass and `g` a bounded measurable function on `X × Y`. Then there are bounded measurable
potentials `φ` and `ψ` such that `exp (φ(x) + ψ(y) + g(x, y))` is the density, against
`μ.prod ν`, of a coupling of `μ` and `ν`. -/
theorem exists_isCoupling_withDensity_exp_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ univ = ν univ) (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (C : ℝ), Measurable φ ∧ Measurable ψ ∧ (∀ x, |φ x| ≤ C) ∧
      (∀ y, |ψ y| ≤ C) ∧ IsCoupling ((μ.prod ν).withDensity fun z ↦
        ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2 + g z))) μ ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := by rw [← Measure.measure_univ_eq_zero, ← hμν, hμ, Measure.coe_zero,
      Pi.zero_apply]
    subst hμ hν
    exact ⟨0, 0, 0, measurable_const, measurable_const, fun _ ↦ by simp, fun _ ↦ by simp,
      by simp⟩
  have hν : ν ≠ 0 := by
    rwa [Ne, ← Measure.measure_univ_eq_zero, ← hμν, Measure.measure_univ_eq_zero]
  obtain ⟨ψ, C, c, hψ, hC, hfix⟩ := exists_sinkhornSweep_eq_add hμ hν hg hgM
  -- The row potential of `ψ`; together with `ψ` it solves the Schrödinger system up to `c`.
  set φ : X → ℝ := fun x ↦ -logIntegralExp g ν ψ x with hφ_def
  have hφ : Measurable φ := (measurable_logIntegralExp hg hψ).neg
  have hφC (x : X) : |φ x| ≤ M + C + |Real.log (ν.real univ)| :=
    (abs_neg _).trans_le (abs_logIntegralExp_le hν hg hgM hψ hC x)
  set f : X × Y → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2 + g z)) with hf_def
  have hf : Measurable f := by fun_prop
  have hrow (x : X) : ∫⁻ y, f (x, y) ∂ν = 1 := by
    have := lintegral_ofReal_exp_add hν hg hgM hψ hC x (φ x)
    have h0 : φ x + logIntegralExp g ν ψ x = 0 := by simp only [hφ_def, neg_add_cancel]
    rw [h0, Real.exp_zero, ENNReal.ofReal_one] at this
    rw [← this]
    refine lintegral_congr fun y ↦ ?_
    simp only [hf_def, hφ_def]
    ring_nf
  have hcol (y : Y) : ∫⁻ x, f (x, y) ∂μ = ENNReal.ofReal (Real.exp (-c)) := by
    have := lintegral_ofReal_exp_add (ν := μ) hμ (hg.comp measurable_swap) (fun z ↦ hgM z.swap)
      hφ hφC y (ψ y)
    have hl : logIntegralExp (g ∘ Prod.swap) μ φ y = -(ψ y + c) := by
      rw [← hfix y, sinkhornSweep, neg_neg]
    have hc : ψ y + -(ψ y + c) = -c := by ring
    rw [hl, hc] at this
    rw [← this]
    refine lintegral_congr fun x ↦ ?_
    rw [hf_def]
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    ring_nf
  have hfst : ((μ.prod ν).withDensity f).fst = μ := by
    ext s hs
    rw [Measure.fst_apply hs, ← prod_univ, withDensity_apply _ (hs.prod MeasurableSet.univ),
      setLIntegral_prod _ hf.aemeasurable]
    simp_rw [Measure.restrict_univ, hrow]
    rw [setLIntegral_const, one_mul]
  have hsnd (t : Set Y) (ht : MeasurableSet t) :
      ((μ.prod ν).withDensity f).snd t = ENNReal.ofReal (Real.exp (-c)) * ν t := by
    rw [Measure.snd_apply ht, ← univ_prod, withDensity_apply _ (MeasurableSet.univ.prod ht),
      setLIntegral_prod_symm _ hf.aemeasurable]
    simp_rw [Measure.restrict_univ, hcol]
    rw [setLIntegral_const]
  -- Comparing total masses forces `exp (-c) = 1`.
  have hc : ENNReal.ofReal (Real.exp (-c)) = 1 := by
    have h₁ := hsnd univ MeasurableSet.univ
    rw [Measure.snd_univ, ← Measure.fst_univ, hfst, hμν] at h₁
    exact ((ENNReal.mul_eq_right (Measure.measure_univ_ne_zero.2 hν) (measure_ne_top _ _)).1
      h₁.symm)
  refine ⟨φ, ψ, max (M + C + |Real.log (ν.real univ)|) C, hφ, hψ,
    fun x ↦ (hφC x).trans (le_max_left _ _), fun y ↦ (hC y).trans (le_max_right _ _),
    ⟨hfst, ?_⟩⟩
  ext t ht
  rw [hsnd t ht, hc, one_mul]

/-- **The Schrödinger minimizer has a product density.** Let the reference measure `R` have density
`exp g` against `μ.prod ν`, for a bounded measurable `g`, and let `μ` be finite. Then a coupling of
`μ` and `ν` attaining the Schrödinger value has density `exp (φ(x) + ψ(y))` against `R`, for bounded
measurable potentials `φ` and `ψ`. Such a coupling exists whenever `μ` and `ν` have equal mass, by
`TauCeti.exists_isCoupling_withDensity_exp_add` and
`TauCeti.IsCoupling.klDiv_eq_schroedingerValue_of_eq_withDensity`. -/
theorem IsCoupling.exists_eq_withDensity_exp_add_of_klDiv_eq_schroedingerValue
    [IsFiniteMeasure μ] {π R : Measure (X × Y)} (hπ : IsCoupling π μ ν) (hg : Measurable g)
    (hgM : ∀ z, |g z| ≤ M)
    (hR : R = (μ.prod ν).withDensity fun z ↦ ENNReal.ofReal (Real.exp (g z)))
    (hπR : klDiv π R = schroedingerValue R μ ν) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (C : ℝ), Measurable φ ∧ Measurable ψ ∧ (∀ x, |φ x| ≤ C) ∧
      (∀ y, |ψ y| ≤ C) ∧ π = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)) := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  obtain ⟨φ, ψ, C, hφ, hψ, hφC, hψC, hσ⟩ :=
    exists_isCoupling_withDensity_exp_add hπ.measure_univ_eq hg hgM
  have hRσ : ((μ.prod ν).withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2 + g z))) =
      R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)) := by
    rw [hR, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_comm (g z)]
  rw [hRσ] at hσ
  have : IsFiniteMeasure R := by
    rw [hR]
    refine isFiniteMeasure_withDensity_ofReal (Integrable.of_bound (by fun_prop) (Real.exp M)
      (ae_of_all _ fun z ↦ ?_)).2
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact (abs_le.1 (hgM z)).2
  have hφi : Integrable φ μ :=
    Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x ↦ hφC x)
  have hψi : Integrable ψ ν :=
    Integrable.of_bound hψ.aestronglyMeasurable C (ae_of_all _ fun y ↦ hψC y)
  have hfin : schroedingerValue R μ ν ≠ ∞ := by
    rw [schroedingerValue_eq_ofReal_of_eq_withDensity hσ rfl hφ hψ hφi hψi]
    exact ENNReal.ofReal_ne_top
  exact ⟨φ, ψ, C, hφ, hψ, hφC, hψC, hπ.eq_of_klDiv_eq_schroedingerValue hσ hπR
    (hσ.klDiv_eq_schroedingerValue_of_eq_withDensity rfl hφ hψ hφi hψi) hfin⟩

/-- **The entropic optimal plan for a bounded cost.** For probability measures `μ` and `ν`, a
bounded measurable cost `c` and a positive temperature `ε`, the regularised transport cost
`TauCeti.entropicTransportCost c ε μ ν` is attained by a coupling whose density against
`μ.prod ν` is `exp ((φ(x) + ψ(y) - c(x, y)) / ε)`, for bounded measurable potentials `φ` and
`ψ`. -/
theorem exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : X × Y → ℝ≥0∞} (hc : Measurable c)
    {B : ℝ≥0} (hcB : ∀ z, c z ≤ B) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ π, IsCoupling π μ ν ∧ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν ∧
      ∃ (φ : X → ℝ) (ψ : Y → ℝ) (C : ℝ), Measurable φ ∧ Measurable ψ ∧ (∀ x, |φ x| ≤ C) ∧
        (∀ y, |ψ y| ≤ C) ∧ π = (μ.prod ν).withDensity fun z ↦
          ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε)) := by
  have hε' : (0 : ℝ) < ε := by positivity
  have hcB' (z : X × Y) : (c z).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.coe_ne_top (hcB z)).trans_eq (ENNReal.coe_toReal B)
  obtain ⟨φ, ψ, C, hφ, hψ, hφC, hψC, hσ⟩ := exists_isCoupling_withDensity_exp_add
    (μ := μ) (ν := ν) (g := fun z ↦ -((c z).toReal / ε)) (M := B / ε) (by simp)
    (hc.ennreal_toReal.div_const _).neg fun z ↦ by
      rw [abs_neg, abs_div, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_pos hε']
      exact div_le_div_of_nonneg_right (hcB' z) hε'.le
  have hGibbs : ((μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2 + -((c z).toReal / ε)))) =
      (μ.prod ν).withDensity fun z ↦
        ENNReal.ofReal (Real.exp ((ε * φ z.1 + ε * ψ z.2 - (c z).toReal) / ε)) := by
    congr 1
    funext z
    congr 2
    field_simp
    ring
  rw [hGibbs] at hσ
  have hφi : Integrable (fun x ↦ ε * φ x) μ :=
    (Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x ↦ hφC x)).const_mul _
  have hψi : Integrable (fun y ↦ ε * ψ y) ν :=
    (Integrable.of_bound hψ.aestronglyMeasurable C (ae_of_all _ fun y ↦ hψC y)).const_mul _
  have hopt := hσ.lintegral_add_mul_klDiv_eq_entropicTransportCost_of_eq_withDensity
    (φ := fun x ↦ ε * φ x) (ψ := fun y ↦ ε * ψ y) hc.aemeasurable
    (ae_of_all _ fun z ↦ ((hcB z).trans_lt ENNReal.coe_lt_top).ne) hε rfl hφi hψi
  refine ⟨_, hσ, hopt, fun x ↦ ε * φ x, fun y ↦ ε * ψ y, ε * C, hφ.const_mul _, hψ.const_mul _,
    fun x ↦ ?_, fun y ↦ ?_, rfl⟩
  · rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_left (hφC x) ε.coe_nonneg
  · rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_left (hψC y) ε.coe_nonneg

end Existence

end TauCeti
