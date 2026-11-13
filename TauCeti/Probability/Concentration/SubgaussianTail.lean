/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Two-sided sub-Gaussian tails

A random variable `X` that is sub-Gaussian with variance proxy `c` satisfies the two-sided Chernoff
bound `P(ε ≤ |X|) ≤ 2 exp (-ε² / (2c))` for `ε ≥ 0`, the sum of Mathlib's upper-tail bound for `X`
and for `-X`.

If `g - c` is sub-Gaussian with variance proxy `σ` and the center `c` is within `ε / 2` of a
target `t`, then `g` deviates from `t` by at least `ε` with probability at most
`2 exp (-(ε / 2)² / (2σ))`. This is how a concentration bound centered at the mean transfers to a
nearby target value.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.measureReal_abs_ge_le`
* `TauCeti.Probability.measureReal_abs_sub_ge_le_of_hasSubgaussianMGF`
* `Measurable.exists_forall_abs_integral_le_of_hasSubgaussianMGF`: a family bounded by
  `|f| + 1` with a common centered sub-Gaussian bound has uniformly bounded means.

## References

* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`.
  The two-tail calculation is adapted from that file; here it is stated for an arbitrary measure
  and a general sub-Gaussian variable rather than for the graphon sampling law.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- **Two-sided Chernoff bound** for a sub-Gaussian random variable: if `X` is sub-Gaussian with
variance proxy `c`, then `|X| ≥ ε` has probability at most `2 exp (-ε² / (2c))` for `ε ≥ 0`. -/
theorem measureReal_abs_ge_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) :=
  calc μ.real {ω | ε ≤ |X ω|} ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} :=
        TauCeti.measureReal_le_abs_le_add
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
        add_le_add (h.measure_ge_le hε) (h.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

end ProbabilityTheory.HasSubgaussianMGF

/-- Functions bounded by `|f| + 1` that are uniformly sub-Gaussian about their means have
uniformly bounded means. -/
theorem Measurable.exists_forall_abs_integral_le_of_hasSubgaussianMGF {ι Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {g : ι → Ω → ℝ} {c : ℝ≥0}
    (hgf : ∀ n x, |g n x| ≤ |f x| + 1)
    (hsub : ∀ n, HasSubgaussianMGF (fun x ↦ g n x - ∫ y, g n y ∂μ) c μ) :
    ∃ B, ∀ n, |∫ y, g n y ∂μ| ≤ B := by
  -- Some sublevel set `S = {|f| ≤ N}` has positive mass.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, μ {x | |f x| ≤ N} ≠ 0 := by
    by_contra! H
    have hU : (⋃ N : ℕ, {x | |f x| ≤ N}) = univ :=
      eq_univ_of_forall fun x ↦ mem_iUnion.2 (exists_nat_ge |f x|)
    simpa [hU] using measure_iUnion_null_iff.2 H
  have hS : MeasurableSet {x | |f x| ≤ N} := measurableSet_le (by fun_prop) measurable_const
  have hp : 0 < μ.real {x | |f x| ≤ N} := ENNReal.toReal_pos hN (measure_ne_top _ _)
  refine ⟨N + 1 + 2 * exp (c / 2) / μ.real {x | |f x| ≤ N}, fun n ↦ ?_⟩
  set m := ∫ y, g n y ∂μ
  have hX := hsub n
  -- The first absolute moment about the mean is at most `2 exp (c / 2)`.
  have habs : ∫ x, |g n x - m| ∂μ ≤ 2 * exp (c / 2) := by
    calc ∫ x, |g n x - m| ∂μ
        ≤ ∫ x, (exp (1 * (g n x - m)) + exp ((-1) * (g n x - m))) ∂μ :=
          integral_mono hX.integrable.abs
            ((hX.integrable_exp_mul 1).add (hX.integrable_exp_mul (-1))) fun x ↦ by
              simp only [one_mul, neg_one_mul]
              linarith [add_one_le_exp |g n x - m|, exp_abs_le (g n x - m)]
      _ = mgf (fun x ↦ g n x - m) μ 1 + mgf (fun x ↦ g n x - m) μ (-1) :=
          integral_add (hX.integrable_exp_mul 1) (hX.integrable_exp_mul (-1))
      _ ≤ exp (c * 1 ^ 2 / 2) + exp (c * (-1) ^ 2 / 2) := add_le_add (hX.mgf_le 1) (hX.mgf_le (-1))
      _ = 2 * exp (c / 2) := by norm_num; ring
  -- On `S`, `|g n - m| ≥ |m| - (N + 1)`.
  have hset : μ.real {x | |f x| ≤ N} * (|m| - (N + 1)) ≤ ∫ x, |g n x - m| ∂μ :=
    calc μ.real {x | |f x| ≤ N} * (|m| - (N + 1))
        = ∫ _ in {x | |f x| ≤ N}, (|m| - (N + 1)) ∂μ := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ x in {x | |f x| ≤ N}, |g n x - m| ∂μ :=
          setIntegral_mono_on (integrable_const _).integrableOn hX.integrable.abs.integrableOn hS
            fun x (hx : |f x| ≤ N) ↦ by
              linarith [abs_sub_abs_le_abs_sub m (g n x), abs_sub_comm m (g n x), hgf n x]
      _ ≤ ∫ x, |g n x - m| ∂μ := setIntegral_le_integral hX.integrable.abs (.of_forall fun _ ↦
          abs_nonneg _)
  have : |m| - (N + 1) ≤ 2 * exp (c / 2) / μ.real {x | |f x| ≤ N} := by
    rw [le_div_iff₀ hp]; linarith
  linarith

namespace TauCeti.Probability

/-- Two-sided sub-Gaussian tail around a shifted center: if `g - c` is sub-Gaussian with variance
proxy `σ` and the center `c` is within `ε / 2` of the target `t`, then `g` deviates from `t` by at
least `ε` with probability at most `2 exp (-(ε / 2)² / (2σ))`. -/
theorem measureReal_abs_sub_ge_le_of_hasSubgaussianMGF {α : Type*} [MeasurableSpace α]
    {P : Measure α} {g : α → ℝ} {c t ε : ℝ} {σ : ℝ≥0}
    (h : ProbabilityTheory.HasSubgaussianMGF (fun x => g x - c) σ P) (hct : |c - t| ≤ ε / 2) :
    P.real {x | ε ≤ |g x - t|} ≤ 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by
  have hε : 0 ≤ ε := by linarith [abs_nonneg (c - t)]
  have : IsFiniteMeasure P := by
    exact (integrable_const_iff_isFiniteMeasure (c := (1 : ℝ)) one_ne_zero).1
      (by simpa using h.integrable_exp_mul 0)
  have htail₁ := h.measure_ge_le (ε := ε / 2) (by positivity)
  have htail₂ := h.neg.measure_ge_le (ε := ε / 2) (by positivity)
  have hincl : {x | ε ≤ |g x - t|} ⊆ {x | ε / 2 ≤ |g x - c|} := fun x hx => by
    rw [Set.mem_ofPred_eq] at hx ⊢
    have htri : |g x - t| ≤ |g x - c| + |c - t| := abs_sub_le _ _ _
    linarith
  calc
    P.real {x | ε ≤ |g x - t|} ≤ P.real {x | ε / 2 ≤ |g x - c|} := measureReal_mono hincl
    _ ≤ P.real {x | ε / 2 ≤ g x - c} + P.real {x | ε / 2 ≤ -(g x - c)} :=
      TauCeti.measureReal_le_abs_le_add (f := fun x => g x - c)
    _ ≤ Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) + Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) :=
      add_le_add htail₁ htail₂
    _ = 2 * Real.exp (-(ε / 2) ^ 2 / (2 * (σ : ℝ))) := by ring

end TauCeti.Probability
