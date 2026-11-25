/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Grönwall's inequality for tail integrals on a ray

Let `P * g` be integrable on `(x, ∞)` and `u ≤ C * P` on `[x, ∞)`, and suppose that for every
`y ≥ x` and every majorant `b` of `u` on `(y, ∞)` with `g * b` integrable there,
`u y ≤ P y * (A + ∫ v in Ioi y, g v * b v)`. Then
`u x ≤ P x * A * exp (∫ v in Ioi x, P v * g v)`
(`TauCeti.le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi`).

Stating the hypothesis for the majorants `b` of `u` rather than for `u` itself lets `u` be
non-measurable. This is the form in which the inequality bounds an arbitrary solution of a
Volterra integral equation on a ray, `TauCeti.norm_volterra_solution_le_of_isBigO_principal_Ici`.
The weight `P` lets the bound grow or decay with `y`; for `P = 1` it is the tail-integral analogue
of the integral Grönwall inequality `TauCeti.le_mul_exp_integral_of_le_add_integral_mul_rev` on a
bounded interval.

The proof iterates the inequality: the `k`-th iterate gives
`u y ≤ P y * (A * ∑ j < k, Ψ y ^ j / j! + C * (Ψ y ^ k / k!))` for `Ψ` the tail integral of
`P * g`, by the identity `∫ v in Ioi y, g v * P v * Ψ v ^ j = Ψ y ^ (j + 1) / (j + 1)`
(`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`), and then lets `k → ∞`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
-/

public section

open Filter Set MeasureTheory
open scoped Nat Topology

namespace TauCeti

/-- **Grönwall's inequality on a ray.** Let `u ≤ C * P` on `[x, ∞)`, and suppose that for every
`y ≥ x` and every majorant `b` of `u` on `(y, ∞)` with `g * b` integrable there,
`u y ≤ P y * (A + ∫ v in Ioi y, g v * b v)`. Then
`u x ≤ P x * A * exp (∫ v in Ioi x, P v * g v)`.

Quantifying over the majorants `b` lets `u` be non-measurable. The `k`-th iterate of the
inequality gives `u y ≤ P y * (A * ∑ j < k, Ψ y ^ j / j! + C * (Ψ y ^ k / k!))` for `Ψ` the
tail integral of `P * g`. -/
theorem le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi {u P g : ℝ → ℝ} {x A C : ℝ}
    (hg : IntegrableOn (fun v ↦ P v * g v) (Ioi x)) (hC : ∀ y ∈ Ici x, u y ≤ C * P y)
    (hu : ∀ y ∈ Ici x, ∀ b : ℝ → ℝ, (∀ v ∈ Ioi y, u v ≤ b v) →
      IntegrableOn (fun v ↦ g v * b v) (Ioi y) → u y ≤ P y * (A + ∫ v in Ioi y, g v * b v)) :
    u x ≤ P x * A * Real.exp (∫ v in Ioi x, P v * g v) := by
  set Ψ : ℝ → ℝ := fun y ↦ ∫ v in Ioi y, P v * g v with hΨ_def
  set B : ℕ → ℝ → ℝ := fun k y ↦
    A * ∑ j ∈ Finset.range k, Ψ y ^ j / j ! + C * (Ψ y ^ k / k !) with hB
  have hiter : ∀ k : ℕ, ∀ y ∈ Ici x, u y ≤ P y * B k y := by
    intro k
    induction k with
    | zero => intro y hy; simpa [hB, mul_comm] using hC y hy
    | succ k ih =>
      intro y (hy : x ≤ y)
      have hgy := hg.mono_set (Ioi_subset_Ioi hy)
      -- each term `g * P * Ψ ^ j / j!` integrates to `Ψ y ^ (j + 1) / (j + 1)!`
      have hfun (j : ℕ) : (fun v ↦ g v * (P v * (Ψ v ^ j / j !))) =
          fun v ↦ P v * g v * (∫ u in Ioi v, P u * g u) ^ j / j ! := by
        ext v; simp only [hΨ_def]; ring
      have hint (j : ℕ) : IntegrableOn (fun v ↦ g v * (P v * (Ψ v ^ j / j !))) (Ioi y) := by
        rw [hfun]; exact (hgy.mul_comp_integral_Ioi (continuous_pow j).continuousOn).div_const _
      have heq (j : ℕ) :
          ∫ v in Ioi y, g v * (P v * (Ψ v ^ j / j !)) = Ψ y ^ (j + 1) / (j + 1)! := by
        rw [hfun, integral_div, hgy.integral_Ioi_mul_pow_integral_Ioi j, Nat.factorial_succ]
        push_cast
        field_simp
        rfl
      have hsplit : (fun v ↦ g v * (P v * B k v)) = fun v ↦
          A * ∑ j ∈ Finset.range k, g v * (P v * (Ψ v ^ j / j !)) +
            C * (g v * (P v * (Ψ v ^ k / k !))) := by
        ext v; simp only [hB, ← Finset.mul_sum]; ring
      have hbint : IntegrableOn (fun v ↦ g v * (P v * B k v)) (Ioi y) := by
        rw [hsplit]
        exact ((integrable_finsetSum _ fun j _ ↦ hint j).const_mul A).add ((hint k).const_mul C)
      refine (hu y hy _ (fun v hv ↦ ih v (hy.trans hv.le)) hbint).trans_eq ?_
      rw [hsplit, integral_add ((integrable_finsetSum _ fun j _ ↦ hint j).const_mul A)
        ((hint k).const_mul C), integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun j _ ↦ hint j]
      simp only [heq, hB, Finset.sum_range_succ' _ k, pow_zero, Nat.factorial_zero, Nat.cast_one,
        div_one]
      ring
  -- let `k → ∞`
  have hlim : Tendsto (fun k ↦ P x * B k x) atTop (𝓝 (P x * A * Real.exp (Ψ x))) := by
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (Ψ x)).tendsto_sum_nat
    rw [← Real.exp_eq_exp_ℝ] at hexp
    simpa [hB, mul_assoc] using ((hexp.const_mul A).add
      ((FloorSemiring.tendsto_pow_div_factorial_atTop (Ψ x)).const_mul C)).const_mul (P x)
  exact ge_of_tendsto' hlim fun k ↦ hiter k x self_mem_Ici

end TauCeti
