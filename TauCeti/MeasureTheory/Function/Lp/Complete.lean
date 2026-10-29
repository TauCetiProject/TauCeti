/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# `Lᵖ` limits of Cauchy sequences and sequences with summable jumps

Mathlib's completeness theorem for the `Lᵖ` seminorm, `MeasureTheory.Lp.cauchy_complete_eLpNorm`,
takes a sequence of `MemLp` functions with a *summable* Cauchy modulus `B`: for `N ≤ n, m`,
`eLpNorm (f n - f m) p μ < B N`. This file states the form a compactness argument naturally
produces, where the modulus only tends to zero and the terms are merely almost everywhere strongly
measurable. Only differences of sufficiently late terms are guaranteed finite `Lᵖ` seminorm, while
the individual terms need not lie in `Lᵖ`.

Passing to a subsequence along which the modulus is summable reduces to Mathlib's almost-everywhere
convergence theorem `MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm`; the passage of an eventual
`Lᵖ` bound to almost everywhere limits, `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`, then carries
the Cauchy bound to the limit for the whole sequence. Since `Lᵖ` convergence implies
convergence in measure, an almost everywhere convergent subsequence is recovered from the conclusion
by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` and
`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`.

## Main results

* `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` — a sequence with an `Lᵖ` Cauchy
  modulus tending to zero converges in `Lᵖ` to a strongly measurable function.
* `TauCeti.exists_stronglyMeasurable_limit_of_summable_eLpNorm_dist` — summable `Lᵖ`
  distances between successive terms in a complete pseudometric target give a strongly
  measurable limit, with the distance to the limit bounded by the tail of the jump bounds.
  This includes `p = ∞` and requires neither a separable target nor a finite measure.
  The proof uses Mathlib's pointwise summability theorem for real-valued distances and
  its Fatou inequality for `Lᵖ` seminorms.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Proposition 8, for metric-valued `Lᵖ` completeness.
-/

public section

open Filter MeasureTheory

open scoped ENNReal Topology

namespace TauCeti

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [CompleteSpace E] {p : ℝ≥0∞}

/-- **Completeness of the `Lᵖ` seminorm under a vanishing Cauchy modulus.** For `1 ≤ p`, a
sequence of almost everywhere strongly measurable functions whose terms of index at least `N` are
within `B N` of each other in `Lᵖ`, where `B N → 0`, converges in `Lᵖ` to a strongly measurable
function.

Unlike `MeasureTheory.Lp.cauchy_complete_eLpNorm`, the modulus need not be summable and the terms
need not lie in `Lᵖ`. -/
theorem exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {B : ℕ → ℝ≥0∞} (hB : Tendsto B atTop (𝓝 0))
    (h_cau : ∀ N n m, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ ≤ B N) :
    ∃ g : α → E, StronglyMeasurable g ∧
      Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  -- A subsequence along which the modulus is dominated by the summable sequence `2⁻¹ ^ n`.
  have hB_eventually : ∀ n, ∀ᶠ k in atTop, B k < 2⁻¹ ^ n := fun n ↦
    (tendsto_order.1 hB).2 _ (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_forall_of_eventually hB_eventually
  have h_cau_sub : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (f (φ n) - f (φ m)) p μ < 2⁻¹ ^ N := fun N n m hn hm ↦
    (h_cau (φ N) (φ n) (φ m) (hφ.monotone hn) (hφ.monotone hm)).trans_lt (hφB N)
  -- Along it, the terms converge almost everywhere.
  obtain ⟨g, hg, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae (fun n ↦ hf (φ n))
    (Lp.ae_tendsto_of_cauchy_eLpNorm (fun n ↦ hf (φ n)) hp (B := fun n ↦ 2⁻¹ ^ n) (by simp)
      h_cau_sub)
  refine ⟨g, hg, ?_⟩
  -- The Cauchy bound passes to the almost everywhere limit, for every term of the sequence.
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp hB) ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  refine (Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun m ↦ f n - f (φ m)) ?_
    (fun m ↦ (hf n).sub (hf (φ m))) ((hf n).sub hg.aestronglyMeasurable)
    (hlim.mono fun x hx ↦ ?_)).trans (hN N le_rfl)
  · filter_upwards [hφ.tendsto_atTop (eventually_ge_atTop N)] with m hm
    exact h_cau N n (φ m) hn hm
  · simpa only [Pi.sub_apply] using tendsto_const_nhds.sub hx

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
        rw [Finset.sum_range_succ, ← Nat.add_assoc]
        exact (eLpNorm_dist_le_eLpNorm_dist_add hp ((hf n).dist (hf (n + N + 1)))).trans
          (add_le_add ih (hjump (n + N)))
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (Eventually.of_forall fun N ↦ (hstep N).trans (ENNReal.sum_le_tsum _))
    (fun N ↦ (hf n).dist (hf (n + N))) ((hf n).dist hg.aestronglyMeasurable) ?_
  filter_upwards [hlim] with x hx
  exact tendsto_const_nhds.dist
    (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))

end TauCeti
