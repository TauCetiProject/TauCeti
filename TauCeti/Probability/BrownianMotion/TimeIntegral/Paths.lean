/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.TimeIntegral.Basic
public import TauCeti.MeasureTheory.Integral.Bochner.Lp
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Samplewise Brownian time integrals and quadrature errors

Identify the mean-square Brownian time integral with the ordinary Bochner integral of
sample paths. Transfer the exact left-rectangle error formula to real random variables:
its second moment is one third of the sum of cubed cell lengths.

Only pre-Brownian laws and joint almost-everywhere strong measurability on the interval
are needed. In particular no filtration, independence from an external past, or sample-path
continuity is required. Product measurability cannot be inferred from pre-Brownian laws
alone. All identifications are almost sure, not pointwise statements about L² representatives.
These are ordinary time integrals, not stochastic integrals.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.3, for time quadrature in the polynomial Itô approximation.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The mean-square Brownian time integral represents the ordinary samplewise integral.
Joint a.e. measurability is required only on the interval being integrated. -/
theorem coeFn_integral_toL2 (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b)
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (a : ℝ) b)).prod P)) :
    ⇑(∫ u in (a : ℝ)..b, hB.toL2 u.toNNReal) =ᵐ[P]
      fun ω ↦ ∫ u in (a : ℝ)..b, B u.toNNReal ω := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [intervalIntegral.integral_of_le hab']
  have hi : IntegrableOn (fun u : ℝ ↦ hB.toL2 u.toNNReal) (Ioc (a : ℝ) b) volume :=
    hB.continuous_toL2_toNNReal.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact hi.coeFn_integral_Lp hm (Eventually.of_forall fun u ↦ hB.coeFn_toL2 u.toNNReal)

/-- The ordinary Brownian time integral is square integrable whenever its integrand is
jointly a.e. strongly measurable on the interval. -/
theorem memLp_integral (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b)
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (a : ℝ) b)).prod P)) :
    MemLp (fun ω ↦ ∫ u in (a : ℝ)..b, B u.toNNReal ω) 2 P :=
  (Lp.memLp _).ae_eq (hB.coeFn_integral_toL2 hab hm)

/-- The sum of mean-square cell errors represents the actual left quadrature error.
This identifies the representatives before computing their second moments. -/
theorem coeFn_sum_leftRiemannError (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (n : ℕ) (hspan : t 0 ≤ t n)
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (t 0 : ℝ) (t n))).prod P)) :
    ⇑(∑ i ∈ Finset.range n, hB.leftRiemannError (t i) (t (i + 1))) =ᵐ[P]
      fun ω ↦ (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω) -
        ∫ u in (t 0 : ℝ)..t n, B u.toNNReal ω := by
  rw [hB.sum_leftRiemannError_eq]
  have hsum : ⇑(∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) • hB.toL2 (t i)) =ᵐ[P]
      fun ω ↦ ∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω := by
    have hterm (i : ℕ) : ⇑(((t (i + 1) : ℝ) - t i) • hB.toL2 (t i)) =ᵐ[P]
        fun ω ↦ ((t (i + 1) : ℝ) - t i) * B (t i) ω :=
      (Lp.coeFn_smul _ _).trans ((hB.coeFn_toL2 (t i)).mono fun ω hω ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, hω])
    filter_upwards [(Lp.coeFn_finsetSum (Finset.range n)
      (fun i ↦ ((t (i + 1) : ℝ) - t i) • hB.toL2 (t i))).trans
      (eventuallyEq_sum fun i _ ↦ hterm i)] with ω hω
    simpa only [Finset.sum_apply] using hω
  exact (Lp.coeFn_sub _ _).trans
    (hsum.sub (hB.coeFn_integral_toL2 hspan hm))

/-- The exact second moment of ordinary Brownian left-rectangle quadrature error is
one third of the sum of cubed cell lengths. Empty grids and repeated dates are allowed. -/
theorem integral_sq_sum_mul_sub_integral (hB : IsPreBrownianReal B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n))
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (t 0 : ℝ) (t n))).prod P)) :
    (∫ ω, ((∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω) -
      ∫ u in (t 0 : ℝ)..t n, B u.toNNReal ω) ^ 2 ∂P) =
        (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) ^ 3) / 3 := by
  rw [← hB.norm_sum_leftRiemannError_sq ht, ← Lp.integral_norm_sq_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [hB.coeFn_sum_leftRiemannError t n
    (ht (Nat.zero_le n) self_mem_Iic (Nat.zero_le n)) hm] with ω hω
  rw [hω, Real.norm_eq_abs, sq_abs]

/-- Actual Brownian quadrature errors are square integrable, not merely random
variables with a formally computed Bochner second moment. -/
theorem memLp_sum_mul_sub_integral (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (n : ℕ) (hspan : t 0 ≤ t n)
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (t 0 : ℝ) (t n))).prod P)) :
    MemLp (fun ω ↦ (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) * B (t i) ω) -
      ∫ u in (t 0 : ℝ)..t n, B u.toNNReal ω) 2 P :=
  (Lp.memLp _).ae_eq (hB.coeFn_sum_leftRiemannError t n hspan hm)

/-- Ordinary Brownian quadrature errors converge in probability on bounded horizons
along any vanishing-mesh family, with no nesting requirement. -/
theorem tendstoInMeasure_sum_mul_sub_integral_zero (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {t : ι → ℕ → ℝ≥0} {n : ι → ℕ} {δ : ι → ℝ}
    (ht : ∀ k, MonotoneOn (t k) (Set.Iic (n k))) {T : ℝ≥0} (hT : ∀ k, t k (n k) ≤ T)
    (hδ : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0))
    (hm : ∀ k, AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (t k 0 : ℝ) (t k (n k)))).prod P)) :
    TendstoInMeasure P (fun k ω ↦
      (∑ i ∈ Finset.range (n k), ((t k (i + 1) : ℝ) - t k i) * B (t k i) ω) -
        ∫ u in (t k 0 : ℝ)..t k (n k), B u.toNNReal ω) l (fun _ ↦ 0) := by
  have hLp := hB.tendsto_sum_leftRiemannError_zero ht hT hδ hlim
  exact TendstoInMeasure.congr
    (fun k ↦ hB.coeFn_sum_leftRiemannError (t k) (n k)
      (ht k (Nat.zero_le _) self_mem_Iic (Nat.zero_le _)) (hm k))
    (Lp.coeFn_zero _ _ _) (tendstoInMeasure_of_tendsto_Lp hLp)

end ProbabilityTheory.IsPreBrownianReal
