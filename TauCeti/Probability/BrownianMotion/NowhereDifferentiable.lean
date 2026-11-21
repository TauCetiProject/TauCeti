/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.GridIncrements
public import TauCeti.Probability.BrownianMotion.NormalizedIncrements
public import TauCeti.Probability.Distributions.Gaussian.SmallBall
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.Analysis.Calculus.Deriv.Abs
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Nowhere differentiability and local oscillation of Brownian motion

This file establishes the pathwise local oscillation, nowhere monotonicity, and simultaneous
nowhere differentiability of one-dimensional Brownian motion:

* As `t → +∞`, sample paths of a pre-Brownian motion almost surely oscillate above every level and
  below every level infinitely often.
* At each fixed time `t₀ : ℝ≥0`, the right-hand difference quotients `(B s - B t₀) / (s - t₀)` are
  almost surely unbounded both above and below as `s → t₀⁺` (infinite signed right Dini
  oscillation).
* On one common full-measure event, sample paths are neither monotone nor antitone on any
  nontrivial open interval `(a, b)` (nor on `[a, b]`) with `a < b`.
* On one common full-measure event, the extension `s ↦ B s.toNNReal ω` fails the right-sided
  pointwise Lipschitz bound `(fun s ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[>] t] (· - t)` at every
  `t ≥ 0` and fails the left-sided pointwise Lipschitz bound
  `(fun s ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[<] t] (· - t)` at every `t > 0`; in particular it
  has no right or two-sided derivative on `[0, ∞)`, no left derivative on `(0, ∞)`, and its even
  reflection `s ↦ B |s|.toNNReal ω` is differentiable at no real number `t : ℝ`. (On `(-∞, 0]`,
  `Real.toNNReal` clamps negative arguments to `0`, so `s ↦ B s.toNNReal ω` is constant equal to
  `B 0 ω`.)

All oscillation and nondifferentiability theorems require only the finite-dimensional Gaussian laws
(`IsPreBrownianReal`), with neither path continuity nor a filtration hypothesis, and are inherited
directly by `IsBrownianReal` via structure extension.

## Main statements

* `ProbabilityTheory.IsPreBrownianReal.ae_frequently_gt_atTop` and
  `ProbabilityTheory.IsPreBrownianReal.ae_frequently_lt_atTop` — almost-sure two-sided unbounded
  oscillation as `t → +∞`.
* `ProbabilityTheory.IsPreBrownianReal.ae_frequently_mul_sub_lt_sub_nhdsGT` and
  `ProbabilityTheory.IsPreBrownianReal.ae_frequently_sub_lt_mul_sub_nhdsGT` — infinite upper and
  lower right Dini oscillation at a fixed time `t₀`.
* `ProbabilityTheory.IsPreBrownianReal.ae_not_monotoneOn_Ioo`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_antitoneOn_Ioo`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_monotoneOn_Icc`, and
  `ProbabilityTheory.IsPreBrownianReal.ae_not_antitoneOn_Icc` — simultaneous nowhere monotonicity
  and nowhere antitonicity on `(a, b)` and `[a, b]`.
* `ProbabilityTheory.IsPreBrownianReal.measure_exists_forall_abs_sub_le_le` and
  `ProbabilityTheory.IsPreBrownianReal.ae_eventually_forall_exists_lt_abs_sub` — quantitative
  geometric small-ball decay and almost-sure dyadic rough-path oscillation on triples of
  consecutive increments.
* `ProbabilityTheory.IsPreBrownianReal.ae_not_isBigO_sub_nhdsGT`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_isBigO_sub_nhdsLT`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableWithinAt_Ici`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableWithinAt_Iic`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableAt`, and
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableAt_comp_abs` — simultaneous failure of
  one-sided Lipschitz bounds and one- and two-sided differentiability on `[0, ∞)` and on `ℝ`.

## References

* R. E. A. C. Paley, N. Wiener, A. Zygmund, *Notes on random functions*, Math. Z. **37** (1933),
  647–668.
* A. Dvoretzky, P. Erdős, S. Kakutani, *Nonincrease everywhere of the Brownian motion process*,
  Proc. Fourth Berkeley Symp. Math. Statist. Probab., Vol. II (1961), 103–116.
* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 1.27,
  Remark 1.28, and Theorem 1.30 (pp. 20–22).
* S. P. Lalley, *Brownian Motion*, University of Chicago lecture notes, Proposition 9 (p. 25).
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set TauCeti TauCeti.Probability
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### Super-geometric oscillation at infinity and fixed-time Dini derivatives -/

private def superGrid (m : ℕ) : ℝ≥0 := (2 : ℝ≥0) ^ (m ^ 2)

private theorem strictMono_superGrid : StrictMono superGrid := fun a b hab ↦ by
  unfold superGrid
  exact pow_lt_pow_right₀ (by norm_num) (Nat.pow_lt_pow_left hab two_ne_zero)

private theorem superGrid_gap_ge (m : ℕ) :
    (2 : ℝ) ^ (m ^ 2) * (4 : ℝ) ^ m ≤ (superGrid (m + 1) : ℝ) - superGrid m := by
  have hpow : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
  have hfour : (2 : ℝ) ^ (2 * m + 1) = 2 * (4 : ℝ) ^ m := by
    rw [pow_succ', pow_mul]
    norm_num
  have hge1 : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (m ^ 2) := by positivity
  rw [superGrid, superGrid]
  push_cast
  rw [hpow, pow_add, hfour]
  nlinarith

private theorem two_pow_le_sqrt_superGrid_gap (m : ℕ) :
    (2 : ℝ) ^ m ≤ √((superGrid (m + 1) : ℝ) - superGrid m) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m ^ 2) := one_le_pow₀ (by norm_num)
  have h4 : ((2 : ℝ) ^ m) ^ 2 ≤ (superGrid (m + 1) : ℝ) - superGrid m := by
    have hsq : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hgap := superGrid_gap_ge m
    have : (0 : ℝ) ≤ (4 : ℝ) ^ m := by positivity
    nlinarith
  exact (Real.le_sqrt (by positivity) (by linarith [sq_nonneg ((2 : ℝ) ^ m)])).mpr h4

private theorem ae_eventually_abs_superGrid_le (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
      |B (superGrid m) ω| ≤ √((superGrid (m + 1) : ℝ) - superGrid m) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let s : ℕ → Set Ω := fun m ↦
    {ω | √((superGrid (m + 1) : ℝ) - superGrid m) ≤ |B (superGrid m) ω|}
  have hmeas_le (m : ℕ) : P (s m) ≤ ENNReal.ofReal ((4⁻¹ : ℝ) ^ m) := by
    have hgap_pos : 0 < (superGrid (m + 1) : ℝ) - superGrid m :=
      sub_pos.mpr (strictMono_superGrid (Nat.lt_succ_self m))
    have hc : 0 < √((superGrid (m + 1) : ℝ) - superGrid m) := Real.sqrt_pos.mpr hgap_pos
    have hcheb := meas_ge_le_variance_div_sq
      (hB.isGaussianProcess.hasGaussianLaw_eval (superGrid m)).memLp_two hc
    rw [hB.integral_eval, (hB.hasLaw_eval (superGrid m)).variance_eq,
      variance_id_gaussianReal, Real.sq_sqrt hgap_pos.le] at hcheb
    simp only [sub_zero] at hcheb
    refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ hgap_pos]
    have hgap := superGrid_gap_ge m
    have h4 : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
    have hinv : ((4⁻¹ : ℝ) ^ m) * ((2 : ℝ) ^ (m ^ 2) * (4 : ℝ) ^ m) = (2 : ℝ) ^ (m ^ 2) := by
      rw [inv_pow, mul_comm, mul_assoc, mul_inv_cancel₀ h4.ne', mul_one]
    have : ((4⁻¹ : ℝ) ^ m) * ((superGrid (m + 1) : ℝ) - superGrid m) ≥
        ((4⁻¹ : ℝ) ^ m) * ((2 : ℝ) ^ (m ^ 2) * (4 : ℝ) ^ m) := by
      gcongr
    simp only [superGrid, NNReal.coe_pow, NNReal.coe_ofNat] at this ⊢
    linarith
  have hsum : (∑' m, P (s m)) ≠ ∞ := by
    have htsum : (∑' m, P (s m)) ≤ ∑' m, ENNReal.ofReal ((4⁻¹ : ℝ) ^ m) := tsum_le_tsum hmeas_le
    refine ne_top_of_le_ne_top ?_ htsum
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
      (summable_geometric_of_lt_one (by positivity) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun m hm ↦ le_of_not_ge hm

private theorem ae_frequently_superGrid_sub_gt (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ᶠ m : ℕ in atTop,
      2 * √((superGrid (m + 1) : ℝ) - superGrid m) <
        B (superGrid (m + 1)) ω - B (superGrid m) ω := by
  suffices ∀ m₀ : ℕ, P {ω | ∀ m ≥ m₀,
      B (superGrid (m + 1)) ω - B (superGrid m) ω ≤
        2 * √((superGrid (m + 1) : ℝ) - superGrid m)} = 0 by
    have hae : ∀ᵐ ω ∂P, ∀ m₀ : ℕ, ∃ m ≥ m₀,
        2 * √((superGrid (m + 1) : ℝ) - superGrid m) <
          B (superGrid (m + 1)) ω - B (superGrid m) ω := by
      rw [ae_all_iff]
      intro m₀
      rw [ae_iff]
      convert this m₀ using 2
      ext ω
      simp
    exact hae.mono fun ω hω ↦ Filter.frequently_atTop.mpr hω
  intro m₀
  let A : Set Ω := {ω | ∀ m ≥ m₀,
    B (superGrid (m + 1)) ω - B (superGrid m) ω ≤
      2 * √((superGrid (m + 1) : ℝ) - superGrid m)}
  have hbound (K : ℕ) : P A ≤ gaussianReal 0 1 (Iic (2 : ℝ)) ^ K := by
    let g : Fin (K + 1) → ℝ≥0 := fun i ↦ superGrid (m₀ + i)
    have hg : StrictMono g := fun i j hij ↦
      strictMono_superGrid (Nat.add_lt_add_left hij m₀)
    have hsub : A ⊆ {ω | ∀ i : Fin K, normalizedBrownianIncrements B g ω i ≤ 2} := by
      intro ω hω i
      have hgap : 0 < √((g i.succ : ℝ) - g i.castSucc) :=
        Real.sqrt_pos.mpr (sub_pos.mpr (hg Fin.castSucc_lt_succ))
      rw [normalizedBrownianIncrements_apply, div_le_iff₀ hgap]
      simpa [g, Nat.add_assoc] using hω (m₀ + i) (Nat.le_add_right m₀ i)
    have hmeas : MeasurableSet {y : Fin K → ℝ | ∀ i, y i ≤ 2} :=
      MeasurableSet.univ_pi' (t := fun _ ↦ Iic (2 : ℝ)) fun _ ↦ measurableSet_Iic
    have hpi : (Measure.pi fun _ : Fin K ↦ gaussianReal 0 1) {y | ∀ i, y i ≤ 2} =
        gaussianReal 0 1 (Iic (2 : ℝ)) ^ K := by
      have hset : {y : Fin K → ℝ | ∀ i, y i ≤ 2} = Set.univ.pi fun _ ↦ Iic (2 : ℝ) := by
        ext y
        simp [Pi.le_def]
      rw [hset, Measure.pi_pi]
      simp
    exact (measure_mono hsub).trans_eq
      (((hB.hasLaw_normalizedBrownianIncrements hg).measure_eq hmeas).trans hpi)
  have hlt1 : gaussianReal 0 1 (Iic (2 : ℝ)) < 1 := by
    rw [← ofReal_cdf, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (cdf_gaussianReal_lt_one 0 one_ne_zero 2)
  have htend : Tendsto (fun K : ℕ ↦ gaussianReal 0 1 (Iic (2 : ℝ)) ^ K) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr hlt1
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hbound)

/-- A pre-Brownian motion is almost surely unbounded above as `t → +∞`: on a single full-measure
event, for every level `C : ℝ` there are arbitrarily large times `t` with `C < B t ω`. -/
theorem ae_frequently_gt_atTop (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ᶠ t : ℝ≥0 in atTop, C < B t ω := by
  filter_upwards [hB.ae_eventually_abs_superGrid_le, hB.ae_frequently_superGrid_sub_gt] with ω
    habs hinc C
  rw [Filter.frequently_atTop]
  intro T
  have hev : ∀ᶠ m : ℕ in atTop,
      |B (superGrid m) ω| ≤ √((superGrid (m + 1) : ℝ) - superGrid m) ∧
        C < (2 : ℝ) ^ m ∧ T ≤ superGrid (m + 1) := by
    refine Filter.Eventually.and habs (Filter.Eventually.and ?_ ?_)
    · have hlim : Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt one_lt_two
      exact (tendsto_atTop.mp hlim (C + 1)).mono fun m hm ↦ by linarith
    · refine (eventually_ge_atTop (⌈(T : ℝ)⌉₊ + 1)).mono fun m hm ↦ ?_
      have hT : (T : ℝ) ≤ (superGrid (m + 1) : ℝ) := by
        have h1 : (T : ℝ) ≤ ⌈(T : ℝ)⌉₊ := Nat.le_ceil _
        have h2 : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((m + 1) ^ 2) := by
          exact_mod_cast (Nat.le_self_pow (Nat.succ_ne_zero 1) (m + 1)).trans
            (Nat.lt_two_pow_self.le)
        simp only [superGrid, NNReal.coe_pow, NNReal.coe_ofNat]
        have hm' : (⌈(T : ℝ)⌉₊ : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ_of_le hm
        linarith
      exact_mod_cast hT
  obtain ⟨m, hdiff, habs_m, hC_m, hT_m⟩ := (hinc.and_eventually hev).exists
  refine ⟨superGrid (m + 1), hT_m, ?_⟩
  have hlow : -√((superGrid (m + 1) : ℝ) - superGrid m) ≤ B (superGrid m) ω :=
    neg_le_of_abs_le habs_m
  have hsqrt := two_pow_le_sqrt_superGrid_gap m
  linarith

/-- A pre-Brownian motion is almost surely unbounded below as `t → +∞`: on a single full-measure
event, for every level `C : ℝ` there are arbitrarily large times `t` with `B t ω < C`. -/
theorem ae_frequently_lt_atTop (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ᶠ t : ℝ≥0 in atTop, B t ω < C := by
  filter_upwards [hB.neg.ae_frequently_gt_atTop] with ω hω C
  exact (hω (-C)).mono fun t ht ↦ by
    simp only [Pi.neg_apply] at ht
    linarith

/-- **Fixed-time upper right Dini oscillation of Brownian motion** (Mörters–Peres, Theorem 1.27):
for every fixed `t₀ : ℝ≥0`, almost surely the upper right-hand difference quotients at `t₀` are
unbounded above (`limsup_{s → t₀⁺} (B s - B t₀) / (s - t₀) = +∞`). -/
theorem ae_frequently_mul_sub_lt_sub_nhdsGT (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ᶠ s : ℝ in 𝓝[>] (t₀ : ℝ), C * (s - t₀) < B s.toNNReal ω - B t₀ ω := by
  let φ : ℝ≥0 → ℝ := fun u ↦ ((t₀ + 1 / u : ℝ≥0) : ℝ)
  have hφ : Tendsto φ atTop (𝓝[>] (t₀ : ℝ)) := by
    have hinv : Tendsto (fun u : ℝ≥0 ↦ (u : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_inv_atTop_nhdsGT_zero.mono_right nhdsWithin_le_nhds).comp
        (NNReal.tendsto_coe_atTop.mpr tendsto_id)
    have hnhds : Tendsto φ atTop (𝓝 ((t₀ : ℝ) + 0)) :=
      ((tendsto_const_nhds (x := (t₀ : ℝ))).add hinv).congr fun u ↦ by simp [φ]
    rw [add_zero] at hnhds
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within φ hnhds ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with u hu
    simp [φ, NNReal.coe_pos.mpr hu]
  filter_upwards [(hB.shift t₀).inv.ae_frequently_gt_atTop] with ω hω C
  refine Filter.Tendsto.frequently_map φ hφ (fun u ⟨huC, hu0⟩ ↦ ?_)
    ((hω C).and_eventually (eventually_gt_atTop (0 : ℝ≥0)))
  have hu_pos : (0 : ℝ) < u := NNReal.coe_pos.mpr hu0
  have hs_nn : (φ u).toNNReal = t₀ + 1 / u := Real.toNNReal_coe
  have hsub : φ u - t₀ = 1 / (u : ℝ) := by simp [φ]
  rw [hs_nn, hsub]
  have hmul := mul_lt_mul_of_pos_right huC (one_div_pos.mpr hu_pos)
  have hcancel : (u : ℝ) * (B (t₀ + 1 / u) ω - B t₀ ω) * (1 / (u : ℝ)) =
      B (t₀ + 1 / u) ω - B t₀ ω := by
    field_simp [hu_pos.ne']
  rwa [hcancel] at hmul

/-- **Fixed-time lower right Dini oscillation of Brownian motion** (Mörters–Peres, Theorem 1.27):
for every fixed `t₀ : ℝ≥0`, almost surely the lower right-hand difference quotients at `t₀` are
unbounded below (`liminf_{s → t₀⁺} (B s - B t₀) / (s - t₀) = -∞`). -/
theorem ae_frequently_sub_lt_mul_sub_nhdsGT (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ᶠ s : ℝ in 𝓝[>] (t₀ : ℝ), B s.toNNReal ω - B t₀ ω < C * (s - t₀) := by
  filter_upwards [hB.neg.ae_frequently_mul_sub_lt_sub_nhdsGT t₀] with ω hω C
  exact (hω (-C)).mono fun s hs ↦ by
    simp only [Pi.neg_apply] at hs
    linarith

/-- **Nowhere monotonicity of Brownian motion on open intervals** (Mörters–Peres, Remark 1.28):
on one common full-measure event, sample paths are not monotone on any nontrivial open interval
`(a, b)` (`a < b`). -/
theorem ae_not_monotoneOn_Ioo (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ⦃a b : ℝ≥0⦄, a < b → ¬ MonotoneOn (B · ω) (Ioo a b) := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ,
      ∃ᶠ s : ℝ in 𝓝[>] ((q : ℝ).toNNReal : ℝ),
        B s.toNNReal ω - B (q : ℝ).toNNReal ω < 0 := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hB.ae_frequently_sub_lt_mul_sub_nhdsGT (q : ℝ).toNNReal] with ω hlt
    simpa using hlt 0
  filter_upwards [hrat] with ω hω a b hab hmono
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (NNReal.coe_lt_coe.mpr hab)
  have hq0 : 0 ≤ (q : ℝ) := (NNReal.coe_nonneg a).trans haq.le
  set t₀ : ℝ≥0 := (q : ℝ).toNNReal
  have ht₀_coe : (t₀ : ℝ) = q := Real.coe_toNNReal _ hq0
  have hat₀ : a < t₀ := NNReal.coe_lt_coe.mp (by rwa [ht₀_coe])
  have ht₀b : t₀ < b := NNReal.coe_lt_coe.mp (by rwa [ht₀_coe])
  obtain ⟨s, hs_lt, hs_mem⟩ :=
    ((hω q).and_eventually (Ioo_mem_nhdsGT (NNReal.coe_lt_coe.mpr ht₀b))).exists
  have hs0 : 0 ≤ s := (NNReal.coe_nonneg t₀).trans hs_mem.1.le
  have hs_coe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0
  have hts : t₀ < s.toNNReal := NNReal.coe_lt_coe.mp (by rw [hs_coe]; exact hs_mem.1)
  have hsb : s.toNNReal < b := NNReal.coe_lt_coe.mp (by rw [hs_coe]; exact hs_mem.2)
  have hle := hmono ⟨hat₀, ht₀b⟩ ⟨hat₀.trans hts, hsb⟩ hts.le
  linarith

/-- **Nowhere antitonicity of Brownian motion on open intervals** (Mörters–Peres, Remark 1.28):
on one common full-measure event, sample paths are not antitone on any nontrivial open interval
`(a, b)` (`a < b`). -/
theorem ae_not_antitoneOn_Ioo (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ⦃a b : ℝ≥0⦄, a < b → ¬ AntitoneOn (B · ω) (Ioo a b) :=
  hB.neg.ae_not_monotoneOn_Ioo.mono fun _ hω _ _ hab hanti ↦ hω hab hanti.neg

/-- **Nowhere monotonicity of Brownian motion on closed intervals** (Mörters–Peres, Remark 1.28):
on one common full-measure event, sample paths are not monotone on any nontrivial closed interval
`[a, b]` (`a < b`). -/
theorem ae_not_monotoneOn_Icc (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ⦃a b : ℝ≥0⦄, a < b → ¬ MonotoneOn (B · ω) (Icc a b) :=
  hB.ae_not_monotoneOn_Ioo.mono fun _ hω _ _ hab hmono ↦ hω hab (hmono.mono Ioo_subset_Icc_self)

/-- **Nowhere antitonicity of Brownian motion on closed intervals** (Mörters–Peres, Remark 1.28):
on one common full-measure event, sample paths are not antitone on any nontrivial closed interval
`[a, b]` (`a < b`). -/
theorem ae_not_antitoneOn_Icc (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ⦃a b : ℝ≥0⦄, a < b → ¬ AntitoneOn (B · ω) (Icc a b) :=
  hB.ae_not_antitoneOn_Ioo.mono fun _ hω _ _ hab hanti ↦ hω hab (hanti.mono Ioo_subset_Icc_self)

/-! ### Simultaneous Paley–Wiener–Zygmund nowhere differentiability -/

private theorem measure_forall_abs_sub_le_le (hB : IsPreBrownianReal B P)
    (M : ℝ) (n m : ℕ) :
    P {ω | ∀ j : Fin 3,
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ M / 2 ^ n} ≤
      ENNReal.ofReal (√(2 / π) * (M / √((2 : ℝ) ^ n))) ^ 3 := by
  let g : Fin 4 → ℝ≥0 := fun i ↦ ((m + i : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hpow_pos : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) n
  have hg : StrictMono g := fun i j hij ↦ by
    unfold g
    exact div_lt_div_of_pos_right (Nat.cast_lt.mpr (Nat.add_lt_add_left hij m)) hpow_pos
  have hsub : {ω | ∀ j : Fin 3,
      |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
        B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ M / 2 ^ n} ⊆
      {ω | ∀ j : Fin 3, |normalizedBrownianIncrements B g ω j| ≤ M / √((2 : ℝ) ^ n)} := by
    intro ω hω j
    have hgap : (g j.succ : ℝ) - g j.castSucc = ((2 : ℝ) ^ n)⁻¹ := by
      simp only [g, Fin.val_succ, Fin.val_castSucc, NNReal.coe_div, NNReal.coe_natCast,
        NNReal.coe_pow, NNReal.coe_ofNat]
      push_cast
      field_simp
      ring
    have hsqrt_pos : (0 : ℝ) < √((2 : ℝ) ^ n) := by positivity
    rw [normalizedBrownianIncrements_apply, hgap, Real.sqrt_inv, div_inv_eq_mul, abs_mul,
      abs_of_pos hsqrt_pos]
    have hj := hω j
    simp only [g, Fin.val_succ, Fin.val_castSucc] at hj ⊢
    calc
      |B (((m + (j : ℕ) + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + (j : ℕ) : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| * √((2 : ℝ) ^ n)
        ≤ (M / 2 ^ n) * √((2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_right hj hsqrt_pos.le
      _ = M / √((2 : ℝ) ^ n) := by
          rw [eq_div_iff hsqrt_pos.ne', mul_assoc, ← sq, Real.sq_sqrt (by positivity),
            div_mul_cancel₀ _ (by positivity)]
  refine (measure_mono hsub).trans ?_
  simpa using
    (hB.hasLaw_normalizedBrownianIncrements hg).measure_forall_abs_le_le_of_pi_gaussianReal_zero_one
      (M / √((2 : ℝ) ^ n))

/-- Quantitative Paley–Wiener–Zygmund small-ball union bound: the probability that on `[0, N]` some
window of three consecutive dyadic `2⁻ⁿ`-increments has all three increments bounded by `M / 2ⁿ`
decays geometrically like `N * (√(2 / π) * M)³ * ((√2)⁻¹)ⁿ` (and vanishes when `M < 0`). -/
theorem measure_exists_forall_abs_sub_le_le (hB : IsPreBrownianReal B P) (N : ℕ) (M : ℝ)
    (n : ℕ) :
    P {ω | ∃ m < N * 2 ^ n, ∀ j : Fin 3,
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ M / 2 ^ n} ≤
      ENNReal.ofReal ((N : ℝ) * (√(2 / π) * M) ^ 3 * (√2)⁻¹ ^ n) := by
  rcases lt_or_ge M 0 with hM | hM
  · have hempty : {ω | ∃ m < N * 2 ^ n, ∀ j : Fin 3,
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ M / 2 ^ n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and,
        not_forall, not_le]
      intro m _
      exact ⟨0, (div_neg_of_neg_of_pos hM (by positivity)).trans_le (abs_nonneg _)⟩
    rw [hempty, measure_empty]
    exact bot_le
  let W : ℕ → Set Ω := fun m ↦ {ω | ∀ j : Fin 3,
    |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
      B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ M / 2 ^ n}
  have hunion : {ω | ∃ m < N * 2 ^ n, ∀ j : Fin 3,
      |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
        B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ M / 2 ^ n} =
      ⋃ m ∈ Finset.range (N * 2 ^ n), W m := by
    ext ω
    simp [W]
  rw [hunion]
  calc
    P (⋃ m ∈ Finset.range (N * 2 ^ n), W m)
      ≤ ∑ m ∈ Finset.range (N * 2 ^ n), P (W m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ Finset.range (N * 2 ^ n),
          ENNReal.ofReal (√(2 / π) * (M / √((2 : ℝ) ^ n))) ^ 3 :=
        Finset.sum_le_sum fun m _ ↦ hB.measure_forall_abs_sub_le_le M n m
    _ = ((N * 2 ^ n : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (√(2 / π) * (M / √((2 : ℝ) ^ n))) ^ 3 := by
        simp
    _ = ENNReal.ofReal ((N : ℝ) * (√(2 / π) * M) ^ 3 * (√2)⁻¹ ^ n) := by
        have hr_nn : 0 ≤ √(2 / π) * (M / √((2 : ℝ) ^ n)) := by positivity
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hr_nn,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        have htwo_pow : (2 : ℝ) ^ n = (√2 ^ n) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt zero_le_two]
        have hsqrt_pow : √((2 : ℝ) ^ n) = √2 ^ n := by
          rw [htwo_pow, Real.sqrt_sq (by positivity)]
        have hs_ne : √2 ^ n ≠ 0 := pow_ne_zero n (by positivity)
        push_cast
        rw [hsqrt_pow, htwo_pow, inv_pow]
        field_simp [hs_ne]

/-- Almost surely, for every horizon `N : ℕ` and slope bound `M : ℝ`, at all sufficiently fine
dyadic scales `2⁻ⁿ` every window of three consecutive increments on `[0, N]` contains at least one
increment strictly larger than `M / 2ⁿ`. -/
theorem ae_eventually_forall_exists_lt_abs_sub (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (N : ℕ) (M : ℝ), ∀ᶠ n in atTop, ∀ m < N * 2 ^ n, ∃ j : Fin 3,
      M / 2 ^ n <
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| := by
  have hnat : ∀ᵐ ω ∂P, ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n, ∃ j : Fin 3,
      (M : ℝ) / 2 ^ n <
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| := by
    rw [ae_all_iff]
    intro N
    rw [ae_all_iff]
    intro M
    let E : ℕ → Set Ω := fun n ↦ {ω | ∃ m < N * 2 ^ n, ∀ j : Fin 3,
      |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
        B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ (M : ℝ) / 2 ^ n}
    have hlt1 : (√2 : ℝ)⁻¹ < 1 := by
      refine inv_lt_one_of_one_lt₀ ?_
      rw [Real.lt_sqrt zero_le_one]
      norm_num
    have hsum : (∑' n, P (E n)) ≠ ∞ := by
      have htsum : (∑' n, P (E n)) ≤
          ∑' n, ENNReal.ofReal ((N : ℝ) * (√(2 / π) * (M : ℝ)) ^ 3 * (√2)⁻¹ ^ n) :=
        tsum_le_tsum fun n ↦ hB.measure_exists_forall_abs_sub_le_le N M n
      refine ne_top_of_le_ne_top ?_ htsum
      have hs : Summable fun n : ℕ ↦ (N : ℝ) * (√(2 / π) * (M : ℝ)) ^ 3 * (√2)⁻¹ ^ n :=
        (summable_geometric_of_lt_one (by positivity) hlt1).mul_left _
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    refine hω.mono fun n hn m hm ↦ ?_
    simp only [E, Set.mem_ofPred_eq, not_exists, not_and, not_forall, not_le] at hn
    exact hn m hm
  filter_upwards [hnat] with ω hω N M
  refine (hω N ⌈M⌉₊).mono fun n hn m hm ↦ ?_
  obtain ⟨j, hj⟩ := hn m hm
  exact ⟨j, (div_le_div_of_nonneg_right (Nat.le_ceil M) (by positivity)).trans_lt hj⟩

private theorem ae_eventually_exists_lt_norm_sub_Ioo (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m : ℤ,
      (∀ k : ℕ, k ≤ 3 → ((m + k : ℤ) : ℝ) / 2 ^ n ∈ Ioo (0 : ℝ) N) → ∃ j : Fin 3,
        (M : ℝ) / 2 ^ n <
          ‖B (((m + j + 1 : ℤ) : ℝ) / 2 ^ n).toNNReal ω -
            B (((m + j : ℤ) : ℝ) / 2 ^ n).toNNReal ω‖ := by
  have htoNN (k n : ℕ) : (((k : ℝ) / 2 ^ n).toNNReal) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    simp
  filter_upwards [hB.ae_eventually_forall_exists_lt_abs_sub] with ω hosc N M
  refine (hosc N M).mono fun n hn m hm ↦ ?_
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hm0 := hm 0 (Nat.zero_le 3)
  simp only [Nat.cast_zero, add_zero, mem_Ioo] at hm0
  have hm_pos : (0 : ℝ) < m := (div_pos_iff_of_pos_right hpow_pos).mp hm0.1
  have hm_nonneg : 0 ≤ m := Int.cast_nonneg_iff.mp hm_pos.le
  have htoNat_lt : m.toNat < N * 2 ^ n := by
    have hlt : (m.toNat : ℝ) < ((N * 2 ^ n : ℕ) : ℝ) := by
      have hcast : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm_nonneg
      rw [hcast]
      exact ((div_lt_iff₀ hpow_pos).mp hm0.2).trans_eq (by push_cast; rfl)
    exact Nat.cast_lt.mp hlt
  obtain ⟨j, hj⟩ := hn m.toNat htoNat_lt
  refine ⟨j, ?_⟩
  have ha : ((m + j + 1 : ℤ) : ℝ) = ((m.toNat + j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m + j + 1 = (m.toNat + j + 1 : ℕ))
  have hb : ((m + j : ℤ) : ℝ) = ((m.toNat + j : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m + j = (m.toNat + j : ℕ))
  rw [Real.norm_eq_abs, ha, hb, htoNN, htoNN]
  exact hj

/-- Almost surely, on one common full-measure event, `s ↦ B s.toNNReal ω` fails the right-sided
pointwise Lipschitz bound `(fun s ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[>] t] (· - t)` at every
`t ≥ 0`. -/
theorem ae_not_isBigO_sub_nhdsGT (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ¬ (fun s : ℝ ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[>] t] (· - t) := by
  filter_upwards [hB.ae_eventually_exists_lt_norm_sub_Ioo] with ω hosc t ht
  have htN : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_floor_add_one t
  exact not_isBigO_sub_nhdsGT_of_eventually_exists_lt_norm_sub
    (mem_of_superset (Ioo_mem_nhdsGT htN) (Ioo_subset_Ioo_left ht)) (hosc (⌊t⌋₊ + 1))

/-- Almost surely, on one common full-measure event, `s ↦ B s.toNNReal ω` fails the left-sided
pointwise Lipschitz bound `(fun s ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[<] t] (· - t)` at every
`t > 0`. -/
theorem ae_not_isBigO_sub_nhdsLT (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      ¬ (fun s : ℝ ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[<] t] (· - t) := by
  filter_upwards [hB.ae_eventually_exists_lt_norm_sub_Ioo] with ω hosc t ht
  have htN : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_floor_add_one t
  exact not_isBigO_sub_nhdsLT_of_eventually_exists_lt_norm_sub
    (mem_of_superset (Ioo_mem_nhdsLT ht) (Ioo_subset_Ioo_right htN.le)) (hosc (⌊t⌋₊ + 1))

/-- **Paley–Wiener–Zygmund simultaneous right-sided nowhere differentiability of Brownian motion**
(Mörters–Peres, Theorem 1.30; Lalley, Proposition 9): on one common full-measure event,
`s ↦ B s.toNNReal ω` has no right derivative at any `t ≥ 0` (including `t = 0`). -/
theorem ae_not_differentiableWithinAt_Ici (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Ici t) t := by
  filter_upwards [hB.ae_not_isBigO_sub_nhdsGT] with ω hω t ht hd
  exact hω t ht (hd.isBigO_sub.mono (nhdsWithin_mono _ Ioi_subset_Ici_self))

/-- Almost surely, on one common full-measure event, `s ↦ B s.toNNReal ω` has no left derivative at
any `t > 0`. -/
theorem ae_not_differentiableWithinAt_Iic (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Iic t) t := by
  filter_upwards [hB.ae_not_isBigO_sub_nhdsLT] with ω hω t ht hd
  exact hω t ht (hd.isBigO_sub.mono (nhdsWithin_mono _ Iio_subset_Iic_self))

/-- **Paley–Wiener–Zygmund simultaneous nowhere differentiability of Brownian motion**
(Mörters–Peres, Theorem 1.30; Lalley, Proposition 9): on one common full-measure event,
`s ↦ B s.toNNReal ω` is not differentiable at any `t ≥ 0`. (On `(-∞, 0]`, `Real.toNNReal` clamps
negative arguments to `0`, so the extended function is constant equal to `B 0 ω`.) -/
theorem ae_not_differentiableAt (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t := by
  filter_upwards [hB.ae_not_differentiableWithinAt_Ici] with ω hω t ht hd
  exact hω t ht hd.differentiableWithinAt

/-- Reflecting a pre-Brownian motion across `t = 0` via `s ↦ B |s|.toNNReal ω` yields sample paths
that are almost surely differentiable at **no** real number `t : ℝ`. -/
theorem ae_not_differentiableAt_comp_abs (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B |s|.toNNReal ω) t := by
  filter_upwards [hB.ae_not_differentiableWithinAt_Ici] with ω hnd t hd
  exact hnd |t| (abs_nonneg t)
    (hd.differentiableWithinAt_Ici_of_comp_abs (f := fun s ↦ B s.toNNReal ω))

end ProbabilityTheory.IsPreBrownianReal
