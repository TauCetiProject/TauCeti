/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Poincaré asymptotic expansions and scales

This file supplements `TauCeti.Analysis.Asymptotics.AsymptoticExpansion` with Poincaré asymptotic
scales and expansions at infinity and at finite points (NIST DLMF §2.1): ratio-limit
characterizations, uniqueness on unbounded sets and accumulation points, convergent series in
inverse powers, and convergent power series.

## Main results

* `Asymptotics.isAsymptoticScale_inv_pow_cobounded`,
  `Asymptotics.isAsymptoticScale_inv_pow_atTop`,
  `Asymptotics.isAsymptoticScale_sub_pow_nhdsWithin`: inverse-power and shifted-power scales.
* `Asymptotics.hasAsymptoticExpansion_iff_tendsto`: ratio-limit characterization when `phi n` is
  eventually nonzero.
* `Asymptotics.HasAsymptoticExpansion.unique_inv_pow_cobounded`,
  `Asymptotics.HasAsymptoticExpansion.unique_inv_pow_atTop`,
  `Asymptotics.HasAsymptoticExpansion.unique_sub_pow_nhdsWithin`: coefficient uniqueness for
  Poincaré scales.
* `Asymptotics.hasAsymptoticExpansion_inv_pow_iff`: DLMF 2.1.15 characterization of Poincaré
  expansions at infinity.
* `Asymptotics.hasAsymptoticExpansion_of_hasSum`: a series `∑ (z ^ s)⁻¹ • a s` converging outside
  a ball is the Poincaré expansion of its sum along `Bornology.cobounded`.
* `HasFPowerSeriesAt.hasAsymptoticExpansion`: a convergent power series at `c` is the
  Poincaré expansion of its sum along `𝓝 c`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1, <https://dlmf.nist.gov/2.1>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1.
-/

public section

open Filter Topology Finset Set
open scoped Real

namespace Asymptotics

/-! ### Poincaré scales and ratio-limit characterization -/

section Scale

variable {α 𝕜 E : Type*} [NormedField 𝕜]

/-- The inverse-power scale `z ↦ (z ^ n)⁻¹` at infinity in a subset `X`. -/
theorem isAsymptoticScale_inv_pow_cobounded (X : Set 𝕜) :
    IsAsymptoticScale (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) := by
  have hw : Tendsto (Inv.inv : 𝕜 → 𝕜) (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 0) :=
    (Filter.tendsto_inv₀_cobounded (α := 𝕜)).mono_left inf_le_left
  exact (isAsymptoticScale_pow hw).congr' fun n =>
    Eventually.of_forall fun z => by simp [inv_pow]

/-- The inverse-power scale `x ↦ (x ^ n)⁻¹` along `atTop` on `ℝ`. -/
theorem isAsymptoticScale_inv_pow_atTop :
    IsAsymptoticScale atTop (fun n (x : ℝ) => (x ^ n)⁻¹) := by
  have hw : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  exact (isAsymptoticScale_pow hw).congr' fun n =>
    Eventually.of_forall fun x => by simp [inv_pow]

/-- The power scale `z ↦ (z - c) ^ n` near a finite point `c` within a subset `X`
(DLMF 2.1.16). -/
theorem isAsymptoticScale_sub_pow_nhdsWithin (X : Set 𝕜) (c : 𝕜) :
    IsAsymptoticScale (𝓝[X] c) (fun n z => (z - c) ^ n) := by
  have hw : Tendsto (fun z : 𝕜 => z - c) (𝓝[X] c) (𝓝 0) := by
    have h : Tendsto (fun z : 𝕜 => z - c) (𝓝 c) (𝓝 0) := by
      simpa using (continuous_sub_right c).tendsto c
    exact h.mono_left nhdsWithin_le_nhds
  exact isAsymptoticScale_pow hw

/-- Ratio-limit characterization of an asymptotic expansion when the scale functions are eventually
nonzero along `l`. -/
theorem hasAsymptoticExpansion_iff_tendsto [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {l : Filter α} {phi : ℕ → α → 𝕜} {a : ℕ → E} {f : α → E}
    (hphi : IsAsymptoticScale l phi) (hne : ∀ n, ∀ᶠ x in l, phi n x ≠ 0) :
    HasAsymptoticExpansion l phi a f ↔
      ∀ n, Tendsto (fun x => (phi n x)⁻¹ • (f x - ∑ s ∈ range n, phi s x • a s))
        l (𝓝 (a n)) := by
  rw [hphi.hasAsymptoticExpansion_iff_isLittleO]
  refine forall_congr' fun n => ?_
  rw [← isLittleO_norm_left, ← isLittleO_norm_right,
    isLittleO_iff_tendsto' ((hne n).mono fun x hx h => absurd (norm_eq_zero.mp h) hx)]
  conv_rhs => rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_congr' ((hne n).mono fun x hx => ?_)
  dsimp only
  have hrew : (phi n x)⁻¹ • (f x - ∑ s ∈ range n, phi s x • a s) - a n =
      (phi n x)⁻¹ • (f x - ∑ s ∈ range (n + 1), phi s x • a s) := by
    conv_rhs => rw [sum_range_succ, sub_add_eq_sub_sub, smul_sub, inv_smul_smul₀ hx]
  rw [hrew, norm_smul, norm_inv, div_eq_inv_mul]

end Scale

/-! ### Poincaré expansions -/

section Poincare

variable {𝕜 E : Type*}

/-- Uniqueness of Poincaré expansions at infinity on an unbounded subset `X`
(`(Bornology.cobounded 𝕜 ⊓ 𝓟 X).NeBot`). -/
theorem HasAsymptoticExpansion.unique_inv_pow_cobounded [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {X : Set 𝕜}
    [hX : (Bornology.cobounded 𝕜 ⊓ 𝓟 X).NeBot] {a b : ℕ → E} {f : 𝕜 → E}
    (ha : HasAsymptoticExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) a f)
    (hb : HasAsymptoticExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) b f) :
    a = b := by
  refine ha.unique (isAsymptoticScale_inv_pow_cobounded X) (fun n => ?_) hb
  refine Filter.Eventually.frequently ?_
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono inf_le_left]
    with z hz
  exact inv_ne_zero (pow_ne_zero n (norm_pos_iff.mp hz))

/-- Uniqueness of Poincaré expansions along `atTop` on `ℝ`. -/
theorem HasAsymptoticExpansion.unique_inv_pow_atTop [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → E} {f : ℝ → E}
    (ha : HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) a f)
    (hb : HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) b f) :
    a = b := by
  refine ha.unique isAsymptoticScale_inv_pow_atTop (fun n => ?_) hb
  refine Filter.Eventually.frequently ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact inv_ne_zero (pow_ne_zero n hx.ne')

/-- Uniqueness of Poincaré expansions at an accumulation point `c` of `X`
(`(𝓝[X \ {c}] c).NeBot`, DLMF 2.1.16). -/
theorem HasAsymptoticExpansion.unique_sub_pow_nhdsWithin [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {X : Set 𝕜} {c : 𝕜}
    [hX : (𝓝[X \ {c}] c).NeBot] {a b : ℕ → E} {f : 𝕜 → E}
    (ha : HasAsymptoticExpansion (𝓝[X \ {c}] c) (fun n z => (z - c) ^ n) a f)
    (hb : HasAsymptoticExpansion (𝓝[X \ {c}] c) (fun n z => (z - c) ^ n) b f) :
    a = b := by
  refine ha.unique (isAsymptoticScale_sub_pow_nhdsWithin (X \ {c}) c) (fun n => ?_) hb
  refine Filter.Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact pow_ne_zero n (sub_ne_zero.mpr hz.2)

/-- DLMF 2.1.15: the Poincaré expansion at infinity in `X` is equivalent to the limits
`z ^ n • (f z - ∑_{s < n} (z ^ s)⁻¹ • a s) → a n`. -/
theorem hasAsymptoticExpansion_inv_pow_iff [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (X : Set 𝕜) (a : ℕ → E) (f : 𝕜 → E) :
    HasAsymptoticExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) a f ↔
      ∀ n, Tendsto (fun z => z ^ n • (f z - ∑ s ∈ range n, (z ^ s)⁻¹ • a s))
        (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 (a n)) := by
  have hne : ∀ n, ∀ᶠ z in Bornology.cobounded 𝕜 ⊓ 𝓟 X, (z ^ n)⁻¹ ≠ 0 := fun n => by
    filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono inf_le_left]
      with z hz
    exact inv_ne_zero (pow_ne_zero n (norm_pos_iff.mp hz))
  exact (hasAsymptoticExpansion_iff_tendsto (isAsymptoticScale_inv_pow_cobounded X) hne).trans
    (forall_congr' fun n => by simp only [inv_inv])

/-- A series `∑ (z ^ s)⁻¹ • a s` convergent for `‖z‖ > R` is the Poincaré asymptotic expansion
of its sum along `Bornology.cobounded 𝕜`. -/
theorem hasAsymptoticExpansion_of_hasSum [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {R : ℝ} {a : ℕ → E} {f : 𝕜 → E}
    (hf : ∀ z : 𝕜, R < ‖z‖ → HasSum (fun s => (z ^ s)⁻¹ • a s) (f z)) :
    HasAsymptoticExpansion (Bornology.cobounded 𝕜) (fun n z => (z ^ n)⁻¹) a f := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  by_cases hex : ∃ z₀ : 𝕜, max R 0 < ‖z₀‖
  · obtain ⟨z₀, hz₀⟩ := hex
    have hrR : R < ‖z₀‖ := (le_max_left R 0).trans_lt hz₀
    have hr0 : 0 < ‖z₀‖ := (le_max_right R 0).trans_lt hz₀
    obtain ⟨A, hA⟩ := (hf z₀ hrR).summable.tendsto_cofinite_zero.norm.bddAbove_range_of_cofinite
    set M : ℝ := max A 0
    have hcoeff : ∀ s, ‖a s‖ ≤ M * ‖z₀‖ ^ s := fun s => by
      have h1 : ‖(z₀ ^ s)⁻¹ • a s‖ ≤ M := (hA ⟨s, rfl⟩).trans (le_max_left A 0)
      rw [norm_smul, norm_inv, norm_pow, inv_mul_eq_div, div_le_iff₀ (pow_pos hr0 s)] at h1
      exact h1
    refine IsBigO.of_bound (2 * M * ‖z₀‖ ^ N) ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (2 * ‖z₀‖)] with z hz
    have hz0 : 0 < ‖z‖ := by linarith
    have hzR : R < ‖z‖ := by linarith
    have htail : HasSum (fun k => (z ^ (k + N))⁻¹ • a (k + N))
        (f z - ∑ s ∈ range N, (z ^ s)⁻¹ • a s) :=
      (hasSum_nat_add_iff' N).mpr (hf z hzR)
    have hgeom : HasSum (fun k : ℕ => (M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * ((1 / 2 : ℝ) ^ k))
        ((M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * (1 - 1 / 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
    have hle : ‖f z - ∑ s ∈ range N, (z ^ s)⁻¹ • a s‖ ≤
        (M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * (1 - 1 / 2)⁻¹ := by
      refine le_of_tendsto_of_tendsto htail.tendsto_sum_nat.norm hgeom.tendsto_sum_nat
        (Eventually.of_forall fun m => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
      have hratio : ‖z₀‖ / ‖z‖ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hz0 (by norm_num : (0 : ℝ) < 2)]
        linarith
      calc
        ‖(z ^ (k + N))⁻¹ • a (k + N)‖
            = (‖z‖ ^ (k + N))⁻¹ * ‖a (k + N)‖ := by rw [norm_smul, norm_inv, norm_pow]
        _ ≤ (‖z‖ ^ (k + N))⁻¹ * (M * ‖z₀‖ ^ (k + N)) := by gcongr; exact hcoeff (k + N)
        _ = M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖ * (‖z₀‖ / ‖z‖) ^ k := by
          rw [norm_inv, norm_pow, pow_add, pow_add, mul_inv, div_pow]
          ring
        _ ≤ M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖ * (1 / 2 : ℝ) ^ k := by
          gcongr
    have hconst : (M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖) * (1 - 1 / 2 : ℝ)⁻¹ =
        2 * M * ‖z₀‖ ^ N * ‖(z ^ N)⁻¹‖ := by ring
    rwa [hconst] at hle
  · push Not at hex
    have hbot : Bornology.cobounded 𝕜 = ⊥ := by
      rw [Bornology.cobounded_eq_bot_iff]
      refine ⟨(Metric.isBounded_closedBall (x := (0 : 𝕜)) (r := max R 0)).subset fun z _ => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hex z
    rw [hbot]
    exact isBigO_bot _ _

/-- A convergent power series at `c` is the Poincaré asymptotic expansion of its sum along `𝓝 c`
(DLMF 2.1.8, 2.1.16). -/
theorem _root_.HasFPowerSeriesAt.hasAsymptoticExpansion [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜} (hf : HasFPowerSeriesAt f p c) :
    HasAsymptoticExpansion (𝓝 c) (fun n z => (z - c) ^ n) p.coeff f := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  have h0 : (fun y : 𝕜 => f (c + y) - ∑ n ∈ range N, y ^ n • p.coeff n) =O[𝓝 0]
      fun y : 𝕜 => y ^ N := by
    rw [← isBigO_norm_right]
    refine (hf.isBigO_sub_partialSum_pow N).congr'
      (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · dsimp only
      congr 1
      simp only [FormalMultilinearSeries.partialSum]
      refine sum_congr rfl fun n _ => ?_
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    · dsimp only
      rw [norm_pow]
  have hsub : Tendsto (fun z : 𝕜 => z - c) (𝓝 c) (𝓝 0) := by
    simpa using (continuous_sub_right c).tendsto c
  have hcomp := h0.comp_tendsto hsub
  refine hcomp.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
  simp only [Function.comp_apply, add_sub_cancel]

/-! ### Checks and examples -/

/-- The inverse-power sequence `x ↦ (x ^ n)⁻¹` is not an asymptotic scale along `𝓝[>] (0 : ℝ)`. -/
theorem not_isAsymptoticScale_inv_pow_nhdsGT_zero :
    ¬ IsAsymptoticScale (𝓝[>] (0 : ℝ)) (fun n x => (x ^ n)⁻¹) := by
  intro h
  have h0 := (h.isLittleO 0).bound zero_lt_one
  obtain ⟨x, hxpos, hbd⟩ := ((eventually_mem_nhdsWithin.and
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually
      (Iio_mem_nhds zero_lt_one))).and h0).exists
  have hx0 : 0 < x := hxpos.1
  have hx1 : x < 1 := hxpos.2
  simp only [zero_add, pow_zero, pow_one, inv_one, Real.norm_eq_abs, abs_one, mul_one,
    abs_inv, abs_of_pos hx0] at hbd
  have : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx0, hx1⟩
  linarith

-- Rescaling check: `1` has expansion `(1, 0, …)` in `x⁻ⁿ` and `(1/2, 0, …)` in `2 x⁻ⁿ`,
-- while `(1, 0, …)` does not expand `1` in `2 x⁻ⁿ`.
example :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 1) (fun _ : ℝ => (1 : ℝ)) ∧
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 2⁻¹) (fun _ : ℝ => (1 : ℝ)) ∧
    ¬ HasAsymptoticExpansion atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 1) (fun _ : ℝ => (1 : ℝ)) := by
  have h1 : HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 1) (fun _ : ℝ => (1 : ℝ)) := by
    rw [hasAsymptoticExpansion_iff]
    intro N
    cases N with
    | zero =>
      simpa using (isBigO_refl (fun _ : ℝ => (1 : ℝ)) atTop)
    | succ N =>
      have hsum : ∀ x : ℝ,
          ∑ n ∈ range (N + 1), (x ^ n)⁻¹ * Pi.single (M := fun _ : ℕ => ℝ) 0 1 n = 1 :=
        fun x => by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; simp [Pi.single_eq_of_ne hb]
          · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
      simp only [smul_eq_mul, hsum, sub_self]
      exact isBigO_zero _ _
  have h2 : HasAsymptoticExpansion atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹)
      (Pi.single (M := fun _ : ℕ => ℝ) 0 2⁻¹) (fun _ : ℝ => (1 : ℝ)) := by
    have hr := h1.smul_scale (ψ := fun n (x : ℝ) => 2 * (x ^ n)⁻¹) (κ := fun _ => 2⁻¹)
      (fun n => Eventually.of_forall fun x => by ring)
    refine hr.congr_coeff fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [Pi.single_eq_of_ne hn]
  refine ⟨h1, h2, fun hbad => ?_⟩
  have hscale : IsAsymptoticScale atTop (fun n (x : ℝ) => 2 * (x ^ n)⁻¹) :=
    isAsymptoticScale_inv_pow_atTop.const_mul (fun _ => two_ne_zero)
  have hne : ∀ n, ∃ᶠ x : ℝ in atTop, 2 * (x ^ n)⁻¹ ≠ 0 := fun n =>
    Filter.Eventually.frequently <| (eventually_gt_atTop (0 : ℝ)).mono fun x hx =>
      mul_ne_zero two_ne_zero (inv_ne_zero (pow_ne_zero n hx.ne'))
  have heq := h2.unique hscale hne hbad
  have h0 := congrFun heq 0
  norm_num at h0

-- Unpunctured singleton check: on `𝓝[{c}] c`, uniqueness fails since `(z - c) ^ n = 0`
-- for `n ≥ 1`.
example {𝕜 : Type*} [NormedField 𝕜] (c : 𝕜) (f : 𝕜 → 𝕜) (a : ℕ → 𝕜) (ha0 : a 0 = f c) :
    HasAsymptoticExpansion (𝓝[{c}] c) (fun n z => (z - c) ^ n) a f := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  cases N with
  | zero =>
    refine IsBigO.of_bound ‖f c‖ ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [mem_singleton_iff.mp hz]
    simp
  | succ N =>
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [mem_singleton_iff.mp hz]
    have hsum : ∑ n ∈ range (N + 1), ((c - c) ^ n) • a n = f c := by
      rw [Finset.sum_eq_single 0]
      · simp [ha0]
      · intro b _ hb; simp [zero_pow hb]
      · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos N)) h0
    rw [hsum, sub_self]

-- Geometric series check: `1 / (z - 1) ~ ∑_{s ≥ 1} z⁻ˢ` along `cobounded 𝕜`.
example {𝕜 : Type*} [NormedField 𝕜] :
    HasAsymptoticExpansion (Bornology.cobounded 𝕜) (fun n z => (z ^ n)⁻¹)
      (fun s => if s = 0 then (0 : 𝕜) else 1) (fun z => (z - 1)⁻¹) := by
  refine hasAsymptoticExpansion_of_hasSum (R := 1) fun z hz => ?_
  have hzne : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hz)
  have hnorm : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h; rw [h, norm_one] at hz; exact lt_irrefl _ hz)
  have h2 : (1 : 𝕜) - z⁻¹ ≠ 0 := sub_ne_zero.mpr (by
    intro h
    have := congrArg norm h
    simp only [norm_one, norm_inv] at this
    linarith [inv_lt_one_of_one_lt₀ hz])
  have hgeom : HasSum (fun k : ℕ => (z⁻¹) ^ k) (1 - z⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, ↓reduceIte, smul_zero, sub_zero]
  have hmul : HasSum (fun k : ℕ => z⁻¹ * (z⁻¹) ^ k) (z⁻¹ * (1 - z⁻¹)⁻¹) :=
    hgeom.mul_left z⁻¹
  have hval : z⁻¹ * (1 - z⁻¹)⁻¹ = (z - 1)⁻¹ := by
    field_simp [hzne, h1, h2]
  rw [hval] at hmul
  refine hmul.congr_fun fun k => ?_
  simp [smul_eq_mul, pow_succ', inv_pow, mul_comm]

end Poincare

end Asymptotics
