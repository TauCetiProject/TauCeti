/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
-- Proof-only: realizes countably many consecutive optimal couplings on one path space.
import TauCeti.MeasureTheory.OptimalTransport.Chain

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

This argument is specific to the infinite exponent. For finite exponents, completeness instead
uses the averaged `L^p` estimates in
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete`.

## Main statements

* `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_top_le_tsum` — a chain of probability
  laws with summable `W_∞` jumps has a limit law with the corresponding tail bounds;
* `TauCeti.WassersteinComponent.completeSpaceTop` and
  `TauCeti.WassersteinComponent.instCompleteSpaceTop` — every anchored finite-`W_∞` component
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
  [CompleteSpace X] [StandardBorelSpace X]

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
  have hchain : ∀ n, (π n).snd = (π (n + 1)).fst := fun n ↦ by
    rw [(hπ n).snd_eq, (hπ (n + 1)).fst_eq]
  set P : Measure (ℕ → X) := TauCeti.Measure.chainMeasure π with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hev : ∀ n, Measurable fun x : ℕ → X ↦ x n := fun n ↦ measurable_pi_apply n
  have hcoord : ∀ n, P.map (fun x ↦ x n) = μ n := fun n ↦ by
    rw [hP, TauCeti.Measure.map_eval_chainMeasure π hchain n, (hπ n).fst_eq]
  have hadj : ∀ n, P.map (fun x ↦ (x n, x (n + 1))) = π n := fun n ↦ by
    rw [hP, TauCeti.Measure.map_adjacent_chainMeasure π hchain n]
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
    have hess : eLpNormEssSup (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) P ≤ b n := by
      rw [← eLpNorm_exponent_top]
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
  have hlim : ∀ᵐ x ∂P, Tendsto (fun n ↦ x n) atTop (𝓝 (limUnder atTop fun n ↦ x n)) := by
    filter_upwards [hcauchy] with x hx
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hx)
  obtain ⟨Z, hZ, hZlim⟩ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ (hev n).aemeasurable) hlim
  have hZtendsto : ∀ᵐ x ∂P, Tendsto (fun n ↦ x n) atTop (𝓝 (Z x)) := by
    filter_upwards [hlim, hZlim] with x hx hx' using hx' ▸ hx
  refine ⟨P.map Z, (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance,
    fun n ↦ ?_⟩
  have hcoupling : IsCoupling (P.map fun x ↦ (x n, Z x)) (μ n) (P.map Z) := by
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst ((hev n).prodMk hZ)]
      exact hcoord n
    · rw [Measure.snd, Measure.map_map measurable_snd ((hev n).prodMk hZ)]
      rfl
  calc
    wassersteinEDist ∞ (μ n) (P.map Z)
        ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) ∞ (P.map fun x ↦ (x n, Z x)) :=
      wassersteinEDist_le hcoupling ∞
    _ = eLpNorm (fun x : ℕ → X ↦ edist (x n) (Z x)) ∞ P := by
      rw [eLpNorm_map_measure measurable_edist.aestronglyMeasurable
        ((hev n).prodMk hZ).aemeasurable]
      rfl
    _ ≤ ∑' k, b (n + k) := by
      rw [eLpNorm_exponent_top]
      refine eLpNormEssSup_le_of_ae_enorm_bound ?_
      filter_upwards [ae_all_iff.2 hjump, hZtendsto] with x hx hxlim
      simpa using edist_le_tsum_of_edist_le_of_tendsto b
        (fun k ↦ by simpa only [Nat.succ_eq_add_one] using hx k) hxlim n

end Limit

section Complete

variable [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [StandardBorelSpace X]

/-- The geometric-tail specialization used to prove completeness of an anchored component. -/
private theorem exists_isProbabilityMeasure_wassersteinEDist_top_le_geometric
    {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, wassersteinEDist ∞ (μ n) (μ (n + 1)) ≤ 2⁻¹ ^ n) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∀ n, wassersteinEDist ∞ (μ n) ν ≤ 2⁻¹ ^ n * 2 := by
  have hgeom : ∀ n : ℕ, ∑' k, (2 : ℝ≥0∞)⁻¹ ^ (n + k) = 2⁻¹ ^ n * 2 := fun n ↦ by
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  have hb : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ∞ := by
    simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
  obtain ⟨ν, hν, hνle⟩ := exists_isProbabilityMeasure_wassersteinEDist_top_le_tsum hb hμ
  exact ⟨ν, hν, fun n ↦ (hνle n).trans (hgeom n).le⟩

/-- The geometric tails bounding the distances to the limit tend to zero. -/
private theorem tendsto_geometric_mul_two :
    Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ n * 2) atTop (𝓝 0) := by
  have h2 : (2 : ℝ≥0∞)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]
    norm_num
  simpa using ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h2) (Or.inr (by simp))

namespace WassersteinComponent

variable {μ₀ : ProbabilityMeasure X}

/-- Every anchored finite-`W_∞` component over a Polish metric space is complete. -/
theorem completeSpaceTop : CompleteSpace (WassersteinComponent ∞ μ₀) := by
  refine EMetric.complete_of_convergent_controlled_sequences (fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ ENNReal.pow_pos (by simp) n) fun u hu ↦ ?_
  have hjump : ∀ n, wassersteinEDist ∞
      ((u n : ProbabilityMeasure X) : Measure X)
      ((u (n + 1) : ProbabilityMeasure X) : Measure X) ≤ 2⁻¹ ^ n := fun n ↦ by
    have h := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rw [edist_def] at h
    exact h.le
  obtain ⟨ν, hν, hνle⟩ :=
    exists_isProbabilityMeasure_wassersteinEDist_top_le_geometric hjump
  have hanchor : wassersteinEDist ∞ (μ₀ : Measure X) ν ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨wassersteinEDist_anchor_ne_top (u 0), ?_⟩)
      (wassersteinEDist_triangle measurable_edist le_top _ _ _)
    exact ne_top_of_le_ne_top (by simp) (hνle 0)
  have hcoe : ((mk (⟨ν, hν⟩ : ProbabilityMeasure X) hanchor :
      WassersteinComponent ∞ μ₀) : ProbabilityMeasure X) = ⟨ν, hν⟩ := coe_mk _ _
  refine ⟨mk ⟨ν, hν⟩ hanchor, tendsto_iff_edist_tendsto_0.2 ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_geometric_mul_two (fun _ ↦ zero_le) fun n ↦ ?_
  rw [edist_def, hcoe]
  exact hνle n

/-- The canonical complete-space instance on an anchored finite-`W_∞` component. -/
instance instCompleteSpaceTop : CompleteSpace (WassersteinComponent ∞ μ₀) :=
  completeSpaceTop

end WassersteinComponent

end Complete

end TauCeti
