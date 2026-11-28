/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# `Lᵖ` limits of metric-valued chains and sequences with a vanishing Cauchy modulus

Mathlib's completeness theorem for the `Lᵖ` seminorm, `MeasureTheory.Lp.cauchy_complete_eLpNorm`,
requires a normed group target, `MemLp` terms, and a *summable* Cauchy modulus. Optimal-transport
gluing and compactness arguments instead produce sequences into a complete metric or extended metric
space `Z` with no linear structure and no global separability assumption, where only differences or
consecutive jumps have controlled `Lᵖ` seminorm.

This file provides `Lᵖ` completeness in that setting for every measure `μ`; the chain results need
`1 ≤ p ≤ ∞`, the vanishing-modulus results hold for every exponent `p`:

1. `TauCeti.ae_tsum_lt_top_of_eLpNorm_le` shows that a countable family of `[0, ∞]`-valued
   functions with `Lᵖ` seminorms bounded by a summable family `b` has an almost everywhere finite
   pointwise sum. For `0 < p ≤ 1`, `TauCeti.ae_tsum_lt_top_of_eLpNorm_le_of_le_one` replaces the
   summability of `b` by that of `b i ^ p`, using subadditivity of `t ↦ t ^ p`, and
   `TauCeti.ae_tsum_lt_top_of_eLpNorm_le_pow` covers geometric bounds at every `p ≠ 0`.
2. `TauCeti.exists_eLpNorm_edist_le_tsum` applies this to consecutive jumps: a sequence of almost
   everywhere strongly measurable functions into a complete pseudo-extended-metric space whose
   consecutive `Lᵖ` jumps are bounded by a summable sequence `b` converges almost everywhere to a
   strongly measurable limit `g`, with tail bound
   `eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ ∑' k, b (n + k)` for every `n`, passing finite
   partial-sum bounds to the limit via `TauCeti.eLpNorm_ennreal_le_of_ae_tendsto`.
3. `TauCeti.exists_tendsto_eLpNorm_edist_of_tendsto_bound` and its seminormed-group specialization
   `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` deduce `Lᵖ` convergence under a
   merely vanishing Cauchy modulus `B N → 0`, with the rate `B N` past index `N`, by extracting a
   subsequence with geometrically small jumps and passing the `Lᵖ` Cauchy bound to the
   almost-everywhere limit.
4. `TauCeti.ae_tendsto_of_tsum_eLpNorm_sub_ne_top` turns summable `Lᵖ` distances to a function
   into almost-everywhere convergence to it, for every `1 ≤ p`.
5. `TauCeti.ae_eq_zero_of_tendsto_of_eLpNorm_le` identifies an almost-everywhere limit of
   functions whose `Lᵖ` seminorms tend to zero with `0`.

## Main results

* `TauCeti.exists_eLpNorm_edist_le_tsum` — a chain of `Z`-valued functions with summable
  consecutive `Lᵖ` jumps converges almost everywhere and in `Lᵖ`, with the tail bound.
* `TauCeti.exists_tendsto_eLpNorm_edist_of_tendsto_bound` — a `Z`-valued sequence with an `Lᵖ`
  Cauchy modulus tending to zero converges in `Lᵖ` to a strongly measurable function, within the
  modulus.
* `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` — the seminormed-group specialization
  for `eLpNorm (f n - g) p μ`.
* `TauCeti.ae_tendsto_of_tsum_eLpNorm_sub_ne_top` — summable `Lᵖ` distances to `g` give
  almost-everywhere convergence to `g`.
* `TauCeti.ae_eq_zero_of_tendsto_of_eLpNorm_le` — Fatou's lemma for `Lᵖ` approximation: an
  almost-everywhere limit of `Lᵖ`-null sequences vanishes almost everywhere.
-/

public section

open Filter MeasureTheory

open scoped ENNReal Topology

namespace TauCeti

variable {α Z E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- **Almost-everywhere summability from summable `Lᵖ` bounds.** For `1 ≤ p` (including `p = ∞`),
if the `Lᵖ` seminorms of a countable family of `[0, ∞]`-valued functions are bounded by a summable
family `b`, then the pointwise sum of the family is finite almost everywhere. No measurability of
the functions is needed: the finite `Lᵖ` bounds make each of them a.e. strongly measurable. -/
theorem ae_tsum_lt_top_of_eLpNorm_le (hp : 1 ≤ p) {ι : Type*} [Countable ι]
    {d : ι → α → ℝ≥0∞} {b : ι → ℝ≥0∞} (hb : ∑' i, b i ≠ ∞) (hd : ∀ i, eLpNorm (d i) p μ ≤ b i) :
    ∀ᵐ x ∂μ, ∑' i, d i x < ∞ := by
  have hmeas (i : ι) : AEMeasurable (d i) μ :=
    (aestronglyMeasurable_of_eLpNorm_ne_top
      ((hd i).trans_lt (ENNReal.lt_top_of_tsum_ne_top hb i)).ne).aemeasurable
  exact ae_lt_top_of_eLpNorm_ne_top (zero_lt_one.trans_le hp).ne'
    (ne_top_of_le_ne_top hb ((eLpNorm_tsum_le hmeas hp).trans (tsum_le_tsum hd)))

/-- **Almost-everywhere summability from `Lᵖ` bounds for `0 < p ≤ 1`.** For `0 < p ≤ 1`, if the
`Lᵖ` seminorms of a countable family of `[0, ∞]`-valued functions are bounded by a family `b` whose
`p`-th powers are summable, then the pointwise sum of the family is finite almost everywhere. For
`p < 1`, summability of `b` itself, as in `TauCeti.ae_tsum_lt_top_of_eLpNorm_le`, is not enough. No
measurability of the functions is needed. -/
theorem ae_tsum_lt_top_of_eLpNorm_le_of_le_one (hp0 : p ≠ 0) (hp1 : p ≤ 1) {ι : Type*}
    [Countable ι] {d : ι → α → ℝ≥0∞} {b : ι → ℝ≥0∞} (hb : ∑' i, b i ^ p.toReal ≠ ∞)
    (hd : ∀ i, eLpNorm (d i) p μ ≤ b i) :
    ∀ᵐ x ∂μ, ∑' i, d i x < ∞ := by
  have hp : p ≠ ∞ := (hp1.trans_lt ENNReal.one_lt_top).ne
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1)
  have hmeas (i : ι) : AEMeasurable (d i) μ :=
    (aestronglyMeasurable_of_eLpNorm_ne_top ((hd i).trans_lt
      ((ENNReal.rpow_lt_top_iff_of_pos hq).1 (ENNReal.lt_top_of_tsum_ne_top hb i))).ne).aemeasurable
  -- The `p`-th powers of the functions have summable integrals, so their sum is finite a.e.
  have hint : ∫⁻ x, ∑' i, d i x ^ p.toReal ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun i ↦ (hmeas i).pow_const _]
    refine ne_top_of_le_ne_top hb (tsum_le_tsum fun i ↦ ?_)
    rw [← eLpNorm_rpow_eq_lintegral hp0 hp (hmeas i)]
    exact ENNReal.rpow_le_rpow (hd i) hq.le
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun i ↦ (hmeas i).pow_const _) hint] with x hx
  -- Subadditivity of `t ↦ t ^ p` bounds each finite partial sum by `(∑' i, d i x ^ p) ^ p⁻¹`.
  refine (CompleteLattice.summable.tsum_le_of_sum_le fun s ↦ ?_).trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hq.le) hx.ne)
  rw [ENNReal.le_rpow_inv_iff hq]
  exact (ENNReal.rpow_sum_le_sum_rpow _ _ hq hq1).trans (sum_le_tsum s)

/-- **Almost-everywhere summability from geometric `Lᵖ` bounds.** For every exponent `p ≠ 0`
(including `p = ∞`) and every `r < 1`, if the `Lᵖ` seminorm of the `n`-th term of a sequence of
`[0, ∞]`-valued functions is at most `r ^ n`, then the pointwise sum of the sequence is finite
almost everywhere. -/
theorem ae_tsum_lt_top_of_eLpNorm_le_pow (hp0 : p ≠ 0) {d : ℕ → α → ℝ≥0∞} {r : ℝ≥0∞}
    (hr : r < 1) (hd : ∀ n, eLpNorm (d n) p μ ≤ r ^ n) :
    ∀ᵐ x ∂μ, ∑' n, d n x < ∞ := by
  rcases le_total 1 p with hp | hp
  · exact ae_tsum_lt_top_of_eLpNorm_le hp (tsum_geometric_lt_top.2 hr).ne hd
  · have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 (hp.trans_lt ENNReal.one_lt_top).ne
    refine ae_tsum_lt_top_of_eLpNorm_le_of_le_one hp0 hp ?_ hd
    simp_rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm _ p.toReal, ENNReal.rpow_mul,
      ENNReal.rpow_natCast]
    exact (tsum_geometric_lt_top.2 (ENNReal.rpow_lt_one hr hq)).ne

section PseudoEMetricSpace

variable [PseudoEMetricSpace Z]

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
    (ae_tsum_lt_top_of_eLpNorm_le hp hb hjump).mono fun x hx ↦
      cauchySeq_of_edist_le_of_tsum_ne_top _ (fun _ ↦ le_rfl) hx.ne
  obtain ⟨g, hg, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hf
    (hcauchy.mono fun _ hx ↦ cauchySeq_tendsto_of_complete hx)
  refine ⟨g, hg, hlim, fun n ↦ ?_⟩
  refine eLpNorm_ennreal_le_of_ae_tendsto (u := atTop)
    (fun N ↦ (hf n).edist (hf (n + N))) ?_ (.of_forall fun N ↦ ?_)
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.edist
      (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))
  · calc eLpNorm (fun x ↦ edist (f n x) (f (n + N) x)) p μ
        ≤ eLpNorm (∑ k ∈ Finset.range N, fun x ↦ edist (f (n + k) x) (f (n + k + 1) x)) p μ :=
          eLpNorm_mono_eNorm (((hf n).edist (hf (n + N))).aestronglyMeasurable) fun x ↦ by
            simpa [Finset.sum_apply, ← Nat.add_assoc] using
              edist_le_range_sum_edist (fun k ↦ f (n + k) x) N
      _ ≤ ∑ k ∈ Finset.range N, eLpNorm (fun x ↦ edist (f (n + k) x) (f (n + k + 1) x)) p μ :=
          eLpNorm_sum_le hp
      _ ≤ ∑ k ∈ Finset.range N, b (n + k) := Finset.sum_le_sum fun k _ ↦ hjump (n + k)
      _ ≤ ∑' k, b (n + k) := sum_le_tsum _

/-- **Completeness of metric `Lᵖ` discrepancies under a vanishing Cauchy modulus.** For every
exponent `p` and a complete pseudo-extended-metric target `Z`, a sequence of functions infinitely
many of which are a.e. strongly measurable, whose terms of index at least `N` have `Lᵖ` discrepancy
at most `B N`, where `B N → 0`, converges in `Lᵖ` to a strongly measurable function `g`, and every
term of index at least `N` lies within `B N` of `g` in `Lᵖ`. -/
theorem exists_tendsto_eLpNorm_edist_of_tendsto_bound [CompleteSpace Z] {f : ℕ → α → Z}
    (hf : ∃ᶠ n in atTop, AEStronglyMeasurable (f n) μ) {B : ℕ → ℝ≥0∞}
    (hB : Tendsto B atTop (𝓝 0))
    (h_cau : ∀ N n m, N ≤ n → N ≤ m → eLpNorm (fun x ↦ edist (f n x) (f m x)) p μ ≤ B N) :
    ∃ g : α → Z, StronglyMeasurable g ∧
      (∀ N n, N ≤ n → eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ B N) ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ edist (f n x) (g x)) p μ) atTop (𝓝 0) := by
  suffices ∃ g : α → Z, StronglyMeasurable g ∧
      ∀ N n, N ≤ n → eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ B N by
    obtain ⟨g, hg, hbound⟩ := this
    exact ⟨g, hg, hbound, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
      (fun _ ↦ zero_le) fun n ↦ hbound n n le_rfl⟩
  rcases eq_or_ne p 0 with rfl | hp0
  · -- At `p = 0`, `eLpNorm` is `0` on a.e. strongly measurable functions and `∞` otherwise. Every
    -- index `N` with `B N` finite is at least the first such index `N₀`, so a strongly measurable
    -- version of an a.e. strongly measurable term of index at least `N₀` will do.
    have hex : ∃ N, B N ≠ ∞ := (hB.eventually (eventually_ne_nhds ENNReal.zero_ne_top)).exists
    obtain ⟨m, hm, hm0⟩ := (hf.and_eventually (eventually_ge_atTop (Nat.find hex))).exists
    refine ⟨hm.mk _, hm.stronglyMeasurable_mk, fun N n hn ↦ ?_⟩
    rcases eq_or_ne (B N) ∞ with hBN | hBN
    · exact hBN ▸ le_top
    have hmeas := aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top (Nat.find_spec hex)
      (h_cau _ n m ((Nat.find_min' hex hBN).trans hn) hm0))
    rw [eLpNorm_exponent_zero (hmeas.congr (hm.ae_eq_mk.mono fun x hx ↦ by simp only [hx]))]
    exact zero_le
  -- Extract a subsequence of a.e. strongly measurable terms with geometrically decaying modulus.
  have hB_frequently : ∀ n, ∃ᶠ k in atTop, AEStronglyMeasurable (f k) μ ∧ B k < 2⁻¹ ^ n :=
    fun n ↦ hf.and_eventually
      ((tendsto_order.1 hB).2 _ (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n))
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_forall_of_frequently hB_frequently
  have hjump : ∀ n, eLpNorm (fun x ↦ edist (f (φ n) x) (f (φ (n + 1)) x)) p μ ≤ 2⁻¹ ^ n :=
    fun n ↦ (h_cau (φ n) (φ n) (φ (n + 1)) le_rfl (hφ.monotone (Nat.le_succ n))).trans
      (hφB n).2.le
  -- The jumps along `φ` are summable a.e., so `f ∘ φ` converges a.e.
  obtain ⟨g, hg, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae (fun n ↦ (hφB n).1)
    ((ae_tsum_lt_top_of_eLpNorm_le_pow hp0 (by norm_num) hjump).mono fun x hx ↦
      cauchySeq_tendsto_of_complete (cauchySeq_of_edist_le_of_tsum_ne_top _ (fun _ ↦ le_rfl) hx.ne))
  -- Pass the Cauchy bound to the almost-everywhere limit along the tail `φ (· + N)`. When `B N` is
  -- finite, the discrepancies from `f n` along it are a.e. measurable, even if `f n` is not.
  have hbound (N n : ℕ) (hn : N ≤ n) :
      eLpNorm (fun x ↦ edist (f n x) (g x)) p μ ≤ B N := by
    rcases eq_or_ne (B N) ∞ with hBN | hBN
    · exact hBN ▸ le_top
    have hle (m : ℕ) : eLpNorm (fun x ↦ edist (f n x) (f (φ (m + N)) x)) p μ ≤ B N :=
      h_cau N n _ hn ((Nat.le_add_left N m).trans hφ.le_apply)
    exact eLpNorm_ennreal_le_of_ae_tendsto (u := atTop)
      (fun m ↦ (aestronglyMeasurable_of_eLpNorm_ne_top
        ((hle m).trans_lt hBN.lt_top).ne).aemeasurable)
      (hlim.mono fun x hx ↦ tendsto_const_nhds.edist (hx.comp (tendsto_add_atTop_nat N)))
      (.of_forall hle)
  exact ⟨g, hg, hbound⟩

end PseudoEMetricSpace

/-- **Completeness of the `Lᵖ` seminorm under a vanishing Cauchy modulus.** For every exponent
`p`, a sequence of functions into a complete seminormed additive group that is a topological group
(for instance any complete seminormed commutative group), infinitely many of which are a.e.
strongly measurable, whose terms of index at least `N` are within `B N` of each other in `Lᵖ`, where
`B N → 0`, converges in `Lᵖ` to a strongly measurable function `g`, and every term of index at least
`N` lies within `B N` of `g` in `Lᵖ`.

Unlike `MeasureTheory.Lp.cauchy_complete_eLpNorm`, the modulus need not be summable and the terms
need not lie in `Lᵖ`. -/
theorem exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound [SeminormedAddGroup E]
    [IsTopologicalAddGroup E] [CompleteSpace E] {f : ℕ → α → E}
    (hf : ∃ᶠ n in atTop, AEStronglyMeasurable (f n) μ) {B : ℕ → ℝ≥0∞}
    (hB : Tendsto B atTop (𝓝 0))
    (h_cau : ∀ N n m, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ ≤ B N) :
    ∃ g : α → E, StronglyMeasurable g ∧ (∀ N n, N ≤ n → eLpNorm (f n - g) p μ ≤ B N) ∧
      Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  -- Taking pointwise norms never increases `eLpNorm`: a non-measurable function has norm `∞`.
  have hle (u : α → E) : eLpNorm (fun x ↦ ‖u x‖ₑ) p μ ≤ eLpNorm u p μ := by
    by_cases hu : AEStronglyMeasurable u μ
    · exact (eLpNorm_eNorm u hu).le
    · simp [eLpNorm_of_not_aestronglyMeasurable hu]
  -- The distance is `edist a b = ‖-a + b‖ₑ`, so `‖a - b‖ₑ` is the distance from `-a` to `-b`: apply
  -- the metric result to `-f n` and negate its limit.
  have hedist (a b : E) : edist (-a) (-b) = ‖a - b‖ₑ := by
    rw [eDist_eq_eNorm_neg_add, neg_neg, sub_eq_add_neg]
  obtain ⟨h, hh, hbound, -⟩ := exists_tendsto_eLpNorm_edist_of_tendsto_bound
    (f := fun n x ↦ -f n x) (hf.mono fun _ hn ↦ hn.neg) hB fun N n m hn hm ↦ by
      simpa only [hedist, Pi.sub_apply] using (hle _).trans (h_cau N n m hn hm)
  -- When `B N` is finite, `f n - -h = (f n - f m) - (-h - f m)` is a.e. strongly measurable.
  have hbound' (N n : ℕ) (hn : N ≤ n) : eLpNorm (f n - -h) p μ ≤ B N := by
    rcases eq_or_ne (B N) ∞ with hBN | hBN
    · exact hBN ▸ le_top
    obtain ⟨m, hm, hNm⟩ := (hf.and_eventually (eventually_ge_atTop N)).exists
    have hmeas : AEStronglyMeasurable (f n - -h) μ := by
      simpa [sub_eq_add_neg, add_assoc] using (aestronglyMeasurable_of_eLpNorm_ne_top
        ((h_cau N n m hn hNm).trans_lt hBN.lt_top).ne).sub (hh.aestronglyMeasurable.neg.sub hm)
    rw [← eLpNorm_eNorm _ hmeas]
    simpa only [Pi.sub_apply, Pi.neg_apply, ← hedist, neg_neg] using hbound N n hn
  exact ⟨-h, hh.neg, hbound', tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
    (fun _ ↦ zero_le) fun n ↦ hbound' n n le_rfl⟩

/-- **Almost-everywhere convergence from summable `Lᵖ` distances.** For `1 ≤ p` (including
`p = ∞`), if the `Lᵖ` distances from `f n` to `g` are summable, then `f n → g` almost everywhere.
This is the step of the Riesz–Fischer theorem that turns `Lᵖ` convergence at a summable rate into
pointwise convergence without passing to a subsequence. -/
theorem ae_tendsto_of_tsum_eLpNorm_sub_ne_top [SeminormedAddCommGroup E] (hp : 1 ≤ p)
    {f : ℕ → α → E} {g : α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ) (h : ∑' n, eLpNorm (f n - g) p μ ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  filter_upwards [ae_tsum_lt_top_of_eLpNorm_le hp (d := fun n x ↦ ‖f n x - g x‖ₑ) h
    fun n ↦ (eLpNorm_eNorm _ ((hf n).sub hg)).le] with x hx
  rw [tendsto_iff_edist_tendsto_0]
  simpa only [eDist_eq_eNorm_sub] using ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

/-- **Fatou's lemma for `Lᵖ` approximation.** For `p ≠ 0`, if `g n → g₀` almost everywhere and the
`Lᵖ` seminorms of `g n` are bounded by a sequence tending to `0`, then `g₀ = 0` almost everywhere.
No measurability is assumed: the bounds are eventually finite, which makes the tail of the sequence,
and hence its limit, a.e. strongly measurable. -/
theorem ae_eq_zero_of_tendsto_of_eLpNorm_le [NormedAddGroup E] {g : ℕ → α → E} {g₀ : α → E}
    {c : ℕ → ℝ≥0∞} (hp : p ≠ 0) (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ g n x) atTop (𝓝 (g₀ x)))
    (hgc : ∀ n, eLpNorm (g n) p μ ≤ c n) (hc : Tendsto c atTop (𝓝 0)) :
    g₀ =ᵐ[μ] 0 := by
  -- Past some index `N` the bounds are finite, so the shifted terms are a.e. strongly measurable.
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hc).2 1 one_pos)
  have hg (n : ℕ) : AEStronglyMeasurable (g (n + N)) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      ((hgc _).trans_lt ((hN _ (Nat.le_add_left N n)).trans ENNReal.one_lt_top)).ne
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun n ↦ g (n + N) x) atTop (𝓝 (g₀ x)) :=
    hlim.mono fun x hx ↦ hx.comp (tendsto_add_atTop_nat N)
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) hg g₀
    (aestronglyMeasurable_of_tendsto_ae atTop hg hlim') hlim'
  refine (eLpNorm_eq_zero_iff hp).1 (le_antisymm (hfatou.trans ?_) (by positivity))
  rw [← (hc.comp (tendsto_add_atTop_nat N)).liminf_eq]
  exact liminf_le_liminf (.of_forall fun n ↦ hgc (n + N))

end TauCeti
