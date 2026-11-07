/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow

/-!
# `Lᵖ` limits of metric-valued chains and sequences with a vanishing Cauchy modulus

Mathlib's completeness theorem for the `Lᵖ` seminorm, `MeasureTheory.Lp.cauchy_complete_eLpNorm`,
requires a normed group target, `MemLp` terms, and a *summable* Cauchy modulus. Optimal-transport
gluing and compactness arguments instead produce sequences into a complete metric or extended metric
space `Z` with no linear structure and no global separability assumption, where only differences or
consecutive jumps have controlled `Lᵖ` seminorm.

This file provides `Lᵖ` completeness in that setting for every exponent `1 ≤ p ≤ ∞` and every
measure `μ`:

1. `TauCeti.ae_tsum_edist_lt_top_of_eLpNorm_le` and `TauCeti.exists_eLpNorm_edist_le_tsum` prove
   that a sequence of almost everywhere strongly measurable functions into a complete
   pseudo-extended-metric space whose consecutive `Lᵖ` jumps are bounded by a summable sequence `b`
   converges almost everywhere to a strongly measurable limit `g`, with tail bound
   `eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ ∑' k, b (n + k)` for every `n`, passing finite
   partial-sum bounds to the limit via `TauCeti.eLpNorm_ennreal_le_of_ae_tendsto`.
2. `TauCeti.exists_tendsto_eLpNorm_edist_of_tendsto_bound` and its normed-group specialization
   `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` deduce `Lᵖ` convergence under a
   merely vanishing Cauchy modulus `B N → 0` by extracting a geometrically summable subsequence
   and passing the eventual `Lᵖ` Cauchy bound to the almost-everywhere limit.

## Main results

* `TauCeti.exists_eLpNorm_edist_le_tsum` — a chain of `Z`-valued functions with summable
  consecutive `Lᵖ` jumps converges almost everywhere and in `Lᵖ`, with the tail bound.
* `TauCeti.exists_tendsto_eLpNorm_edist_of_tendsto_bound` — a `Z`-valued sequence with an `Lᵖ`
  Cauchy modulus tending to zero converges in `Lᵖ` to a strongly measurable function.
* `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` — the normed-group specialization for
  `eLpNorm (f n - g) p μ`.
-/

public section

open Filter MeasureTheory

open scoped ENNReal Topology

namespace TauCeti

variable {α Z E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

section PseudoEMetricSpace

variable [PseudoEMetricSpace Z]

/-- **Almost-everywhere summability of metric `Lᵖ` jumps.** For `1 ≤ p` (including `p = ∞`), if the
consecutive `Lᵖ` discrepancies of a sequence of a.e. strongly measurable functions into `Z` are
bounded by a summable sequence `b`, then the pointwise jump series is finite almost everywhere. -/
theorem ae_tsum_edist_lt_top_of_eLpNorm_le (hp : 1 ≤ p) {f : ℕ → α → Z}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {b : ℕ → ℝ≥0∞} (hb : ∑' n, b n ≠ ∞)
    (hjump : ∀ n, eLpNorm (fun x ↦ edist (f n x) (f (n + 1) x)) p μ ≤ b n) :
    ∀ᵐ x ∂μ, ∑' n, edist (f n x) (f (n + 1) x) < ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  let d : ℕ → α → ℝ≥0∞ := fun k x ↦ edist (f k x) (f (k + 1) x)
  have hd : ∀ k, AEMeasurable (d k) μ := fun k ↦ (hf k).edist (hf (k + 1))
  have htsum_le : eLpNorm (fun x ↦ ∑' k, d k x) p μ ≤ ∑' k, b k := by
    refine eLpNorm_ennreal_le_of_ae_tendsto (u := atTop)
      (fun N ↦ (Finset.range N).aemeasurable_fun_sum fun k _ ↦ hd k)
      (.of_forall fun x ↦ ENNReal.tendsto_nat_tsum fun k ↦ d k x) (.of_forall fun N ↦ ?_)
    have hsum : (fun x ↦ ∑ k ∈ Finset.range N, d k x) = ∑ k ∈ Finset.range N, d k := by
      ext x; simp
    rw [hsum]
    exact (eLpNorm_sum_le hp).trans ((Finset.sum_le_sum fun k _ ↦ hjump k).trans (sum_le_tsum _))
  exact ae_lt_top_of_eLpNorm_ne_top hp0 (ne_top_of_le_ne_top hb htsum_le)

/-- **Finite displacement estimate.** For `1 ≤ p`, the `Lᵖ` norm of the distance from `f n` to
`f (n + N)` is bounded by the sum of the bounds `b (n + k)` on the consecutive `Lᵖ` jumps. -/
theorem eLpNorm_edist_le_sum_of_eLpNorm_le (hp : 1 ≤ p) {f : ℕ → α → Z}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {b : ℕ → ℝ≥0∞}
    (hjump : ∀ n, eLpNorm (fun x ↦ edist (f n x) (f (n + 1) x)) p μ ≤ b n) (n N : ℕ) :
    eLpNorm (fun x ↦ edist (f n x) (f (n + N) x)) p μ ≤ ∑ k ∈ Finset.range N, b (n + k) :=
  calc eLpNorm (fun x ↦ edist (f n x) (f (n + N) x)) p μ
      ≤ eLpNorm (∑ k ∈ Finset.range N, fun x ↦ edist (f (n + k) x) (f (n + k + 1) x)) p μ :=
        eLpNorm_mono_enorm (((hf n).edist (hf (n + N))).aestronglyMeasurable) fun x ↦ by
          simpa [Finset.sum_apply, ← Nat.add_assoc] using
            edist_le_range_sum_edist (fun k ↦ f (n + k) x) N
    _ ≤ ∑ k ∈ Finset.range N, eLpNorm (fun x ↦ edist (f (n + k) x) (f (n + k + 1) x)) p μ :=
        eLpNorm_sum_le hp
    _ ≤ ∑ k ∈ Finset.range N, b (n + k) := Finset.sum_le_sum fun k _ ↦ hjump (n + k)

/-- **Metric-valued `Lᵖ` chain completeness.** For `1 ≤ p` (including `p = ∞`) and a complete
pseudo-extended-metric target `Z` (with no global separability assumption), if consecutive `Lᵖ`
discrepancies of a sequence `f` of a.e. strongly measurable functions are bounded by a summable
sequence `b`, then `f` converges almost everywhere to a strongly measurable limit `g` satisfying
the tail bound `eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ ∑' k, b (n + k)` for every `n`. -/
theorem exists_eLpNorm_edist_le_tsum [CompleteSpace Z] (hp : 1 ≤ p) {f : ℕ → α → Z}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {b : ℕ → ℝ≥0∞} (hb : ∑' n, b n ≠ ∞)
    (hjump : ∀ n, eLpNorm (fun x ↦ edist (f n x) (f (n + 1) x)) p μ ≤ b n) :
    ∃ g : α → Z, StronglyMeasurable g ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) ∧
      ∀ n, eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ ∑' k, b (n + k) := by
  have hcauchy : ∀ᵐ x ∂μ, CauchySeq fun n ↦ f n x :=
    (ae_tsum_edist_lt_top_of_eLpNorm_le hp hf hb hjump).mono fun x hx ↦
      cauchySeq_of_edist_le_of_tsum_ne_top _ (fun _ ↦ le_rfl) hx.ne
  obtain ⟨g, hg, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hf
    (hcauchy.mono fun _ hx ↦ cauchySeq_tendsto_of_complete hx)
  refine ⟨g, hg, hlim, fun n ↦ ?_⟩
  refine eLpNorm_ennreal_le_of_ae_tendsto (u := atTop)
    (fun N ↦ (hf n).edist (hf (n + N))) ?_ (.of_forall fun N ↦ ?_)
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.edist
      (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))
  · exact (eLpNorm_edist_le_sum_of_eLpNorm_le hp hf hjump n N).trans (sum_le_tsum _)

/-- **Completeness of metric `Lᵖ` discrepancies under a vanishing Cauchy modulus.** For `1 ≤ p` and
a complete pseudo-extended-metric target `Z`, a sequence of a.e. strongly measurable functions
whose terms of index at least `N` have `Lᵖ` discrepancy at most `B N`, where `B N → 0`, converges
in `Lᵖ` to a strongly measurable function. -/
theorem exists_tendsto_eLpNorm_edist_of_tendsto_bound [CompleteSpace Z] (hp : 1 ≤ p)
    {f : ℕ → α → Z} (hf : ∀ n, AEStronglyMeasurable (f n) μ) {B : ℕ → ℝ≥0∞}
    (hB : Tendsto B atTop (𝓝 0))
    (h_cau : ∀ N n m, N ≤ n → N ≤ m → eLpNorm (fun x ↦ edist (f n x) (f m x)) p μ ≤ B N) :
    ∃ g : α → Z, StronglyMeasurable g ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ edist (f n x) (g x)) p μ) atTop (𝓝 0) := by
  have hB_eventually : ∀ n, ∀ᶠ k in atTop, B k < 2⁻¹ ^ n := fun n ↦
    (tendsto_order.1 hB).2 _ (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_forall_of_eventually hB_eventually
  have hjump : ∀ n, eLpNorm (fun x ↦ edist (f (φ n) x) (f (φ (n + 1)) x)) p μ ≤ 2⁻¹ ^ n :=
    fun n ↦ (h_cau (φ n) (φ n) (φ (n + 1)) le_rfl (hφ.monotone (Nat.le_succ n))).trans (hφB n).le
  obtain ⟨g, hg, hlim, -⟩ := exists_eLpNorm_edist_le_tsum hp (fun n ↦ hf (φ n))
    (by simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]) hjump
  refine ⟨g, hg, ENNReal.tendsto_atTop_zero.2 fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 hB) ε hε
  refine ⟨N, fun n hn ↦ (eLpNorm_ennreal_le_of_ae_tendsto (u := atTop)
    (fun m ↦ (hf n).edist (hf (φ m)))
    (hlim.mono fun x hx ↦ tendsto_const_nhds.edist hx) ?_).trans (hN N le_rfl)⟩
  filter_upwards [hφ.tendsto_atTop (eventually_ge_atTop N)] with m hm
  exact h_cau N n (φ m) hn hm

end PseudoEMetricSpace

/-- **Completeness of the `Lᵖ` seminorm under a vanishing Cauchy modulus.** For `1 ≤ p`, a
sequence of almost everywhere strongly measurable functions whose terms of index at least `N` are
within `B N` of each other in `Lᵖ`, where `B N → 0`, converges in `Lᵖ` to a strongly measurable
function.

Unlike `MeasureTheory.Lp.cauchy_complete_eLpNorm`, the modulus need not be summable and the terms
need not lie in `Lᵖ`. -/
theorem exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound [NormedAddCommGroup E] [CompleteSpace E]
    (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ) {B : ℕ → ℝ≥0∞}
    (hB : Tendsto B atTop (𝓝 0))
    (h_cau : ∀ N n m, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ ≤ B N) :
    ∃ g : α → E, StronglyMeasurable g ∧
      Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have hnorm : ∀ {u v : α → E}, AEStronglyMeasurable u μ → AEStronglyMeasurable v μ →
      eLpNorm (fun x ↦ edist (u x) (v x)) p μ = eLpNorm (u - v) p μ := fun {u v} hu hv ↦ by
    simpa only [edist_eq_enorm_sub, Pi.sub_apply] using eLpNorm_enorm (u - v) (hu.sub hv)
  obtain ⟨g, hg, hlim⟩ := exists_tendsto_eLpNorm_edist_of_tendsto_bound hp hf hB
    fun N n m hn hm ↦ (hnorm (hf n) (hf m)).trans_le (h_cau N n m hn hm)
  exact ⟨g, hg, (tendsto_congr fun n ↦ hnorm (hf n) hg.aestronglyMeasurable).1 hlim⟩

end TauCeti
