/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete

/-!
# Completeness at the infinite Wasserstein exponent

On a complete separable metric space, every anchored finite-`W_∞` component is complete. The
measure-level result `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_top_le_tsum` gives the
quantitative core: if consecutive probability laws are at `W_∞`-distance at most `b n` and
`b` is summable, then they converge to a probability law whose distance from the `n`th law is at
most the corresponding tail of `b`.

The proof chooses an optimal coupling for every consecutive pair using
`TauCeti.exists_isCoupling_eLpNorm_top_eq_wassersteinEDist`, then realizes all those couplings on
one path space using `TauCeti.Measure.chainMeasure`. The essential-supremum bounds hold
simultaneously at every time almost surely, so almost every path is Cauchy. Its pointwise limit
provides the limiting probability law and retains the same tail bound.

The Cauchy argument is specific to the infinite exponent; the pathwise-limit extraction
`TauCeti.Measure.exists_measurable_isCoupling_map_chainMeasure` and the completeness criterion
`TauCeti.WassersteinComponent.completeSpace_of_exists_tendsto_wassersteinEDist` are shared
with the finite-exponent development in
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete`.

## Main statements

* `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_top_le_tsum` — a chain of probability
  laws with summable `W_∞` jumps has a limit law with the corresponding tail bounds;
* `TauCeti.WassersteinComponent.instCompleteSpaceTop` — every anchored finite-`W_∞` component
  over a Polish metric space is complete.

## References

* C. R. Givens and R. M. Shortt, *A class of Wasserstein metrics for probability distributions*,
  Michigan Math. J. 31 (1984), 231–240.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace TauCeti

universe u

variable {X : Type u}

section Limit

variable [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X]

/-- **A chain of laws with summable `W_∞` jumps converges.** If consecutive probability laws
have infinite-exponent Wasserstein distance at most `b n`, where `b` is summable, then some
probability law `ν` is at distance at most `∑' k, b (n + k)` from the `n`th law.

The weak inequality is available because optimal `W_∞` couplings exist on Polish spaces. -/
theorem exists_isProbabilityMeasure_wassersteinEDist_top_le_tsum
    {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)] {b : ℕ → ℝ≥0∞}
    (hb : ∑' n, b n ≠ ∞) (hμ : ∀ n, wassersteinEDist ∞ (μ n) (μ (n + 1)) ≤ b n) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∀ n, wassersteinEDist ∞ (μ n) ν ≤ ∑' k, b (n + k) := by
  let _ : Nonempty X := Measure.nonempty_of_neZero (μ 0)
  choose π hπ hπopt using fun n ↦
    exists_isCoupling_eLpNorm_top_eq_wassersteinEDist (μ n) (μ (n + 1))
      ⟨(μ n).prod (μ (n + 1)), isCoupling_prod (μ n) (μ (n + 1))⟩
  have : ∀ n, IsProbabilityMeasure (π n) := fun n ↦ (hπ n).isProbabilityMeasure
  set P : Measure (ℕ → X) := TauCeti.Measure.chainMeasure (X := fun _ ↦ X) π
  have hev : ∀ n, Measurable fun x : ℕ → X ↦ x n := fun n ↦ measurable_pi_apply n
  have hadj : ∀ n, P.map (fun x ↦ (x n, x (n + 1))) = π n :=
    TauCeti.Measure.map_adjacent_chainMeasure_of_isCoupling hπ
  have hjumpNorm : ∀ n,
      eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) ∞ P ≤ b n := fun n ↦ by
    calc
      eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) ∞ P
          = eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ (π n) := by
            rw [← hadj n, eLpNorm_map_measure measurable_edist.aestronglyMeasurable
              ((hev n).prodMk (hev (n + 1))).aemeasurable]
            rfl
      _ = wassersteinEDist ∞ (μ n) (μ (n + 1)) := hπopt n
      _ ≤ b n := hμ n
  have hjump : ∀ n, ∀ᵐ x ∂P, edist (x n) (x (n + 1)) ≤ b n := fun n ↦ by
    have hm : AEStronglyMeasurable (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) P :=
      ((hev n).edist (hev (n + 1))).aestronglyMeasurable
    have hess : eLpNormEssSup (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) P ≤ b n := by
      rw [← eLpNorm_exponent_top hm]
      exact hjumpNorm n
    filter_upwards [ae_le_eLpNormEssSup
      (f := fun x : ℕ → X ↦ edist (x n) (x (n + 1)))] with x hx
    have hx' : edist (x n) (x (n + 1)) ≤
        eLpNormEssSup (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) P := by
      simpa using hx
    exact hx'.trans hess
  have hcauchy : ∀ᵐ x ∂P, CauchySeq fun n ↦ x n := by
    filter_upwards [ae_all_iff.2 hjump] with x hx
    exact cauchySeq_of_edist_le_of_tsum_ne_top b
      (fun n ↦ by simpa only [Nat.succ_eq_add_one] using hx n) hb
  obtain ⟨Z, hZ, hZtendsto, hcoupling⟩ :=
    TauCeti.Measure.exists_measurable_isCoupling_map_chainMeasure hπ hcauchy
  refine ⟨P.map Z, (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance,
    fun n ↦ ?_⟩
  calc
    wassersteinEDist ∞ (μ n) (P.map Z)
        ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ (P.map fun x ↦ (x n, Z x)) :=
      wassersteinEDist_le (hcoupling n) ∞
    _ = eLpNorm (fun x : ℕ → X ↦ edist (x n) (Z x)) ∞ P := by
      rw [eLpNorm_map_measure measurable_edist.aestronglyMeasurable
        ((hev n).prodMk hZ).aemeasurable]
      rfl
    _ ≤ ∑' k, b (n + k) := by
      have hm : AEStronglyMeasurable (fun x : ℕ → X ↦ edist (x n) (Z x)) P :=
        ((hev n).edist hZ).aestronglyMeasurable
      rw [eLpNorm_exponent_top hm]
      refine eLpNormEssSup_le_of_ae_enorm_bound ?_
      filter_upwards [ae_all_iff.2 hjump, hZtendsto] with x hx hxlim
      simpa using edist_le_tsum_of_edist_le_of_tendsto b
        (fun k ↦ by simpa only [Nat.succ_eq_add_one] using hx k) hxlim n

end Limit

section Complete

variable [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] {μ₀ : ProbabilityMeasure X}

/-- Every anchored finite-`W_∞` component over a Polish metric space is complete. -/
instance WassersteinComponent.instCompleteSpaceTop : CompleteSpace (WassersteinComponent ∞ μ₀) :=
  WassersteinComponent.completeSpace_of_exists_tendsto_wassersteinEDist fun _ _ hμ ↦ by
    have hb : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ∞ := by
      simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    obtain ⟨ν, hν, hle⟩ := exists_isProbabilityMeasure_wassersteinEDist_top_le_tsum hb
      fun n ↦ (hμ n).le
    refine ⟨ν, hν, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ zero_le) hle⟩
    simpa only [add_comm] using ENNReal.tendsto_sum_nat_add _ hb

end Complete

end TauCeti
