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

1. `TauCeti.eLpNorm_ennreal_le_of_ae_tendsto` extends Fatou's lemma for the `Lᵖ` seminorm of
   `ℝ≥0∞`-valued functions to all exponents `p : ℝ≥0∞` (including `0` and `∞`) and countably
   generated filters, deducing almost-everywhere measurability of the limit automatically.
2. `TauCeti.ae_tsum_edist_lt_top_of_eLpNorm_le` and `TauCeti.exists_eLpNorm_edist_le_tsum` prove
   that a sequence of almost everywhere strongly measurable functions into a complete
   pseudo-extended-metric space whose consecutive `Lᵖ` jumps are bounded by a summable sequence `b`
   converges almost everywhere to a strongly measurable limit `g`, with tail bound
   `eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ ∑' k, b (n + k)` for every `n`.
3. `TauCeti.exists_tendsto_eLpNorm_edist_of_tendsto_bound` and its normed-group specialization
   `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` deduce `Lᵖ` convergence under a
   merely vanishing Cauchy modulus `B N → 0` by extracting a geometrically summable subsequence
   and passing the eventual `Lᵖ` Cauchy bound to the almost-everywhere limit.

## Main results

* `TauCeti.eLpNorm_ennreal_le_of_ae_tendsto` — Fatou's lemma for `eLpNorm` of `ℝ≥0∞`-valued
  functions at arbitrary `p : ℝ≥0∞` along a countably generated filter.
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

/-- **Fatou's lemma for the `Lᵖ` seminorm of `ℝ≥0∞`-valued functions**, at every exponent
`p : ℝ≥0∞` (including `0` and `∞`) and along any countably generated `NeBot` filter. Almost
everywhere measurability of the limit is deduced from the pointwise convergence. -/
theorem eLpNorm_ennreal_le_of_ae_tendsto {ι : Type*} {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) u (𝓝 (g x)))
    (hle : ∀ᶠ i in u, eLpNorm (f i) p μ ≤ C) :
    eLpNorm g p μ ≤ C := by
  obtain ⟨v, hv⟩ := exists_seq_tendsto u
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hv.eventually hle)
  let f' : ℕ → α → ℝ≥0∞ := fun n ↦ f (v (n + N))
  have hf' : ∀ n, AEMeasurable (f' n) μ := fun n ↦ hf (v (n + N))
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f' n x) atTop (𝓝 (g x)) :=
    hlim.mono fun x hx ↦ (hx.comp hv).comp (tendsto_add_atTop_nat N)
  have hle' : ∀ n, eLpNorm (f' n) p μ ≤ C := fun n ↦ hN (n + N) (Nat.le_add_left N n)
  have hg : AEMeasurable g μ := ENNReal.aemeasurable_of_tendsto hf' hlim'
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hg.aestronglyMeasurable]
    exact zero_le
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hg.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm]
    simp only [enorm_eq_self]
    have hcongr : essSup g μ = essSup (fun x ↦ atTop.liminf fun n ↦ f' n x) μ :=
      essSup_congr_ae (hlim'.mono fun x hx ↦ hx.liminf_eq.symm)
    rw [hcongr]
    refine (ENNReal.essSup_liminf_le f').trans (liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_))
    simpa [eLpNorm_exponent_top (hf' n).aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm] using
      hle' n
  · exact eLpNorm_le_of_ae_tendsto_ennreal hp0 hp hf' hlim' hle'

/-- At any nonzero exponent (including `∞`), an `ℝ≥0∞`-valued function with finite `Lᵖ` seminorm is
finite almost everywhere. -/
theorem ae_lt_top_of_eLpNorm_ne_top (hp0 : p ≠ 0) {f : α → ℝ≥0∞} (h : eLpNorm f p μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  have hf : AEMeasurable f μ := (aestronglyMeasurable_of_eLpNorm_ne_top h).aemeasurable
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm] at h
    simp only [enorm_eq_self] at h
    exact ae_lt_of_essSup_lt h.lt_top
  · have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have hint : ∫⁻ x, f x ^ p.toReal ∂μ ≠ ∞ := by
      rw [← eLpNorm_rpow_eq_lintegral hp0 hp hf]
      exact (ENNReal.rpow_lt_top_of_nonneg hr.le h).ne
    filter_upwards [ae_lt_top' (hf.pow_const p.toReal) hint] with x hx
    rwa [← ENNReal.lt_rpow_inv_iff hr, ENNReal.top_rpow_of_pos (inv_pos.2 hr)] at hx

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
  -- Finite triangle steps bound the `Lᵖ` distance along the chain before passing to the a.e. limit.
  have hstep : ∀ N, eLpNorm (fun x ↦ edist (f n x) (f (n + N) x)) p μ ≤
      ∑ k ∈ Finset.range N, b (n + k) := fun N ↦ by
    induction N with
    | zero => simp
    | succ N ih =>
      calc eLpNorm (fun x ↦ edist (f n x) (f (n + (N + 1)) x)) p μ
          ≤ eLpNorm ((fun x ↦ edist (f n x) (f (n + N) x)) +
              fun x ↦ edist (f (n + N) x) (f (n + N + 1) x)) p μ :=
            eLpNorm_mono_enorm (((hf n).edist (hf (n + (N + 1)))).aestronglyMeasurable) fun x ↦ by
              simpa [Pi.add_apply, ← Nat.add_assoc] using
                edist_triangle (f n x) (f (n + N) x) (f (n + N + 1) x)
        _ ≤ eLpNorm (fun x ↦ edist (f n x) (f (n + N) x)) p μ +
              eLpNorm (fun x ↦ edist (f (n + N) x) (f (n + N + 1) x)) p μ := eLpNorm_add_le hp
        _ ≤ (∑ k ∈ Finset.range N, b (n + k)) + b (n + N) := add_le_add ih (hjump (n + N))
        _ = ∑ k ∈ Finset.range (N + 1), b (n + k) := (Finset.sum_range_succ _ _).symm
  refine eLpNorm_ennreal_le_of_ae_tendsto (u := atTop)
    (fun N ↦ (hf n).edist (hf (n + N))) ?_
    (.of_forall fun N ↦ (hstep N).trans (sum_le_tsum _))
  filter_upwards [hlim] with x hx
  exact tendsto_const_nhds.edist
    (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))

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
