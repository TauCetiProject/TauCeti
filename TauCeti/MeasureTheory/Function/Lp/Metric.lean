/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Limits of metric-valued functions with summable `Lᵖ` jumps

For a complete pseudometric target, a sequence of almost everywhere strongly measurable
functions with summable `Lᵖ` distances between successive terms has a strongly measurable
limit. The distance to the limit is bounded by the corresponding tail of the jump bounds.
This includes the essential-supremum exponent and does not require a separable target or a
finite measure. It is useful when coupling constructions put a sequence on a common carrier.

The argument uses Mathlib's pointwise summability theorem for the real-valued distances,
then its Fatou inequality for `Lᵖ` seminorms to retain the tail bound.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Proposition 8, for metric-valued `Lᵖ` completeness.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

/-- Summable `Lᵖ` jumps in a complete pseudometric target give a strongly measurable limit
with the same tail bound, for every `1 ≤ p ≤ ∞`. The measure need not be finite. -/
theorem exists_stronglyMeasurable_limit_of_summable_eLpNorm_dist
    {α Z : Type*} [MeasurableSpace α] {μ : Measure α}
    [PseudoMetricSpace Z] [CompleteSpace Z] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → α → Z} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {b : ℕ → ℝ≥0∞} (hb : ∑' n, b n ≠ ∞)
    (hjump : ∀ n, eLpNorm (fun x ↦ dist (f n x) (f (n + 1) x)) p μ ≤ b n) :
    ∃ g : α → Z, StronglyMeasurable g ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) ∧
      ∀ n, eLpNorm (fun x ↦ dist (f n x) (g x)) p μ ≤ ∑' k, b (n + k) := by
  have hsum : ∀ᵐ x ∂μ, Summable (fun n ↦ dist (f n x) (f (n + 1) x)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
      summable_norm_of_tsum_eLpNorm_ne_top hp
        (ne_top_of_le_ne_top hb (ENNReal.tsum_le_tsum hjump))
  have hcauchy : ∀ᵐ x ∂μ, CauchySeq fun n ↦ f n x := by
    filter_upwards [hsum] with x hx
    exact cauchySeq_of_dist_le_of_summable (fun n ↦ dist (f n x) (f (n + 1) x))
      (fun n ↦ le_rfl) hx
  obtain ⟨g, hg, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hf
    (hcauchy.mono fun _ hx ↦ cauchySeq_tendsto_of_complete hx)
  refine ⟨g, hg, hlim, fun n ↦ ?_⟩
  have hstep : ∀ N, eLpNorm (fun x ↦ dist (f n x) (f (n + N) x)) p μ ≤
      ∑ k ∈ Finset.range N, b (n + k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        calc
          eLpNorm (fun x ↦ dist (f n x) (f (n + (N + 1)) x)) p μ
              ≤ eLpNorm (fun x ↦ dist (f n x) (f (n + N) x) +
                  dist (f (n + N) x) (f (n + N + 1) x)) p μ :=
            eLpNorm_mono (by fun_prop) fun x ↦ by
              simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
                abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg), Nat.add_assoc] using
                dist_triangle (f n x) (f (n + N) x) (f (n + N + 1) x)
          _ ≤ eLpNorm (fun x ↦ dist (f n x) (f (n + N) x)) p μ +
                eLpNorm (fun x ↦ dist (f (n + N) x) (f (n + N + 1) x)) p μ :=
            eLpNorm_add_le hp
          _ ≤ (∑ k ∈ Finset.range N, b (n + k)) + b (n + N) :=
            add_le_add ih (hjump (n + N))
          _ = ∑ k ∈ Finset.range (N + 1), b (n + k) :=
            (Finset.sum_range_succ _ _).symm
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (Eventually.of_forall fun N ↦ (hstep N).trans (ENNReal.sum_le_tsum _))
    (fun N ↦ (hf n).dist (hf (n + N))) ((hf n).dist hg.aestronglyMeasurable) ?_
  filter_upwards [hlim] with x hx
  exact tendsto_const_nhds.dist
    (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))

end TauCeti
