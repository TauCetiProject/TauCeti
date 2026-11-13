/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.GridIncrements
public import TauCeti.Probability.BrownianMotion.NormalizedIncrements
public import TauCeti.Probability.Distributions.Gaussian.SmallBall
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

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
  nontrivial closed interval `[a, b]` with `a < b`.
* On one common full-measure event, the extension `s ↦ B s.toNNReal ω` fails the right-sided
  pointwise Lipschitz bound `(· - B t.toNNReal ω) =O[𝓝[>] t] (· - t)` at every `t ≥ 0` and fails
  the left-sided pointwise Lipschitz bound `(· - B t.toNNReal ω) =O[𝓝[<] t] (· - t)` at every
  `t > 0`; in particular it has no right or two-sided derivative on `[0, ∞)` and no left derivative
  on `(0, ∞)`. (On `(-∞, 0]`, `Real.toNNReal` clamps negative arguments to `0`, so the extended path
  is constant equal to `B 0 ω`.)

All finite-dimensional oscillation and nondifferentiability theorems require only the
finite-dimensional Gaussian laws (`IsPreBrownianReal`), with neither path continuity nor a
filtration hypothesis. `IsBrownianReal` inherits them via structure extension and adds almost-sure
path continuity, including for the reflected two-sided extension `s ↦ B |s|.toNNReal ω` on all of
`ℝ`.

## Main statements

* `ProbabilityTheory.IsPreBrownianReal.ae_frequently_gt_atTop` and
  `ProbabilityTheory.IsPreBrownianReal.ae_frequently_lt_atTop` — almost-sure two-sided unbounded
  oscillation as `t → +∞`.
* `ProbabilityTheory.IsPreBrownianReal.ae_frequently_slope_gt_nhdsGT` and
  `ProbabilityTheory.IsPreBrownianReal.ae_frequently_slope_lt_nhdsGT` — infinite upper and lower
  right Dini oscillation at a fixed time `t₀`.
* `ProbabilityTheory.IsPreBrownianReal.ae_not_monotoneOn_and_not_antitoneOn_Icc` — simultaneous
  nowhere monotonicity on `[0, ∞)`.
* `ProbabilityTheory.IsPreBrownianReal.measure_exists_dyadic_three_increments_le` and
  `ProbabilityTheory.IsPreBrownianReal.ae_eventually_forall_exists_dyadic_three_increment_gt` —
  quantitative geometric small-ball decay and almost-sure dyadic rough-path oscillation on triples
  of consecutive increments.
* `ProbabilityTheory.IsPreBrownianReal.ae_not_isBigO_sub_nhdsGT_and_nhdsLT`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableWithinAt_Ici`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableWithinAt_Iic`,
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableAt`, and
  `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableAt_and_not_differentiableWithinAt_zero`
  — simultaneous failure of one-sided Lipschitz bounds and one- and two-sided differentiability.
* `IsBrownianReal.ae_continuous_and_not_differentiableAt_and_not_differentiableWithinAt_zero` and
  `IsBrownianReal.ae_continuous_abs_and_forall_not_differentiableAt` — almost-sure continuity
  paired with nowhere differentiability on `[0, ∞)` and on all of `ℝ`.

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

private theorem gaussianReal_zero_one_Iic_two_lt_one :
    gaussianReal 0 1 (Iic (2 : ℝ)) < 1 := by
  have hne : gaussianReal 0 1 (Ioi (2 : ℝ)) ≠ 0 := fun h0 ↦ by
    have hvol := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    simp at hvol
  rw [← compl_Iic] at hne
  refine lt_of_le_of_ne prob_le_one fun heq ↦ hne ?_
  rw [prob_compl_eq_one_sub measurableSet_Iic, heq, tsub_self]

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
    have hmeas : MeasurableSet {y : Fin K → ℝ | ∀ i, y i ≤ 2} := by
      have : {y : Fin K → ℝ | ∀ i, y i ≤ 2} = ⋂ i : Fin K, {y | y i ≤ 2} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun i ↦ measurableSet_le (measurable_pi_apply i) measurable_const
    have hpi : (Measure.pi fun _ : Fin K ↦ gaussianReal 0 1) {y | ∀ i, y i ≤ 2} =
        gaussianReal 0 1 (Iic (2 : ℝ)) ^ K := by
      have hset : {y : Fin K → ℝ | ∀ i, y i ≤ 2} = Set.univ.pi fun _ ↦ Iic (2 : ℝ) := by
        ext y
        simp [Pi.le_def]
      rw [hset, Measure.pi_pi]
      simp
    exact (measure_mono hsub).trans_eq
      (((hB.hasLaw_normalizedBrownianIncrements hg).measure_eq hmeas).trans hpi)
  have htend : Tendsto (fun K : ℕ ↦ gaussianReal 0 1 (Iic (2 : ℝ)) ^ K) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr gaussianReal_zero_one_Iic_two_lt_one
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
theorem ae_frequently_slope_gt_nhdsGT (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ᶠ s : ℝ in 𝓝[>] (t₀ : ℝ), C * (s - t₀) < B s.toNNReal ω - B t₀ ω := by
  filter_upwards [(hB.shift t₀).inv.ae_frequently_gt_atTop] with ω hω C
  rw [Filter.Frequently]
  intro hnot
  obtain ⟨b, htb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnot
  have hpos : 0 < b - t₀ := sub_pos.mpr htb
  set U : ℝ≥0 := (1 / (b - t₀)).toNNReal + 1
  obtain ⟨u, huU, huC⟩ := Filter.frequently_atTop.mp (hω C) U
  have hu_pos : (0 : ℝ) < u := by
    have : (1 : ℝ≥0) ≤ u := (le_add_of_nonneg_left (bot_le : (0 : ℝ≥0) ≤ _)).trans huU
    exact lt_of_lt_of_le zero_lt_one (NNReal.coe_le_coe.mpr this)
  have hu_gt : 1 / (b - t₀) < (u : ℝ) := by
    have hle : 1 / (b - t₀) ≤ ((1 / (b - t₀)).toNNReal : ℝ) := Real.le_coe_toNNReal _
    have hU : ((1 / (b - t₀)).toNNReal : ℝ) + 1 ≤ u := by exact_mod_cast huU
    linarith
  set s : ℝ := ((t₀ + 1 / u : ℝ≥0) : ℝ)
  have hs_mem : s ∈ Ioo (t₀ : ℝ) b := by
    have hinv : 1 / (u : ℝ) < b - t₀ := (div_lt_iff₀ hu_pos).mpr
      ((div_lt_iff₀ hpos).mp hu_gt |>.trans_eq (mul_comm _ _))
    simp only [s, NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, mem_Ioo]
    exact ⟨lt_add_of_pos_right _ (one_div_pos.mpr hu_pos), by linarith⟩
  have hs_nn : s.toNNReal = t₀ + 1 / u := Real.toNNReal_coe
  have hsub : s - t₀ = 1 / (u : ℝ) := by
    simp [s, NNReal.coe_add]
  have hgt : C * (s - t₀) < B s.toNNReal ω - B t₀ ω := by
    rw [hs_nn, hsub]
    have hmul := mul_lt_mul_of_pos_right huC (one_div_pos.mpr hu_pos)
    have hcancel : (u : ℝ) * (B (t₀ + 1 / u) ω - B t₀ ω) * (1 / (u : ℝ)) =
        B (t₀ + 1 / u) ω - B t₀ ω := by
      field_simp [hu_pos.ne']
    rwa [hcancel] at hmul
  exact hb hs_mem hgt

/-- **Fixed-time lower right Dini oscillation of Brownian motion** (Mörters–Peres, Theorem 1.27):
for every fixed `t₀ : ℝ≥0`, almost surely the lower right-hand difference quotients at `t₀` are
unbounded below (`liminf_{s → t₀⁺} (B s - B t₀) / (s - t₀) = -∞`). -/
theorem ae_frequently_slope_lt_nhdsGT (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ᶠ s : ℝ in 𝓝[>] (t₀ : ℝ), B s.toNNReal ω - B t₀ ω < C * (s - t₀) := by
  filter_upwards [hB.neg.ae_frequently_slope_gt_nhdsGT t₀] with ω hω C
  exact (hω (-C)).mono fun s hs ↦ by
    simp only [Pi.neg_apply] at hs
    linarith

/-- **Nowhere monotonicity of Brownian motion** (Mörters–Peres, Remark 1.28): on one common
full-measure event, sample paths are neither monotone nor antitone on any nontrivial interval
`[a, b]` (`a < b`). -/
theorem ae_not_monotoneOn_and_not_antitoneOn_Icc (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ⦃a b : ℝ≥0⦄, a < b →
      ¬ MonotoneOn (B · ω) (Icc a b) ∧ ¬ AntitoneOn (B · ω) (Icc a b) := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ,
      (∃ᶠ s : ℝ in 𝓝[>] ((q : ℝ).toNNReal : ℝ),
        0 < B s.toNNReal ω - B (q : ℝ).toNNReal ω) ∧
      (∃ᶠ s : ℝ in 𝓝[>] ((q : ℝ).toNNReal : ℝ),
        B s.toNNReal ω - B (q : ℝ).toNNReal ω < 0) := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hB.ae_frequently_slope_gt_nhdsGT (q : ℝ).toNNReal,
      hB.ae_frequently_slope_lt_nhdsGT (q : ℝ).toNNReal] with ω hgt hlt
    exact ⟨by simpa using hgt 0, by simpa using hlt 0⟩
  filter_upwards [hrat] with ω hω a b hab
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (NNReal.coe_lt_coe.mpr hab)
  have hq0 : 0 ≤ (q : ℝ) := (NNReal.coe_nonneg a).trans haq.le
  set t₀ : ℝ≥0 := (q : ℝ).toNNReal
  have ht₀_coe : (t₀ : ℝ) = q := Real.coe_toNNReal _ hq0
  have hat₀ : a < t₀ := NNReal.coe_lt_coe.mp (by rwa [ht₀_coe])
  have ht₀b : t₀ < b := NNReal.coe_lt_coe.mp (by rwa [ht₀_coe])
  have hIoo : Ioo (t₀ : ℝ) b ∈ 𝓝[>] (t₀ : ℝ) := Ioo_mem_nhdsGT (NNReal.coe_lt_coe.mpr ht₀b)
  obtain ⟨hup, hdn⟩ := hω q
  refine ⟨fun hmono ↦ ?_, fun hanti ↦ ?_⟩
  · obtain ⟨s, hs_lt, hs_mem⟩ := (hdn.and_eventually hIoo).exists
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg t₀).trans hs_mem.1.le
    have hts : t₀ ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).mpr hs_mem.1.le
    have hsb : s.toNNReal ≤ b := (Real.toNNReal_le_iff_le_coe).mpr hs_mem.2.le
    have hle := hmono ⟨hat₀.le, ht₀b.le⟩ ⟨hat₀.le.trans hts, hsb⟩ hts
    linarith
  · obtain ⟨s, hs_gt, hs_mem⟩ := (hup.and_eventually hIoo).exists
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg t₀).trans hs_mem.1.le
    have hts : t₀ ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).mpr hs_mem.1.le
    have hsb : s.toNNReal ≤ b := (Real.toNNReal_le_iff_le_coe).mpr hs_mem.2.le
    have hge := hanti ⟨hat₀.le, ht₀b.le⟩ ⟨hat₀.le.trans hts, hsb⟩ hts
    linarith

/-! ### Simultaneous Paley–Wiener–Zygmund nowhere differentiability -/

private theorem measure_forall_dyadic_three_increments_le (hB : IsPreBrownianReal B P)
    (M n m : ℕ) :
    P {ω | ∀ j : Fin 3,
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ (M : ℝ) / 2 ^ n} ≤
      ENNReal.ofReal (√(2 / π) * ((M : ℝ) / √((2 : ℝ) ^ n))) ^ 3 := by
  let g : Fin 4 → ℝ≥0 := fun i ↦ ((m + i : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hpow_pos : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) n
  have hg : StrictMono g := fun i j hij ↦ by
    unfold g
    exact div_lt_div_of_pos_right (Nat.cast_lt.mpr (Nat.add_lt_add_left hij m)) hpow_pos
  have hsub : {ω | ∀ j : Fin 3,
      |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
        B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ (M : ℝ) / 2 ^ n} ⊆
      {ω | ∀ j : Fin 3, |normalizedBrownianIncrements B g ω j| ≤ (M : ℝ) / √((2 : ℝ) ^ n)} := by
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
        ≤ ((M : ℝ) / 2 ^ n) * √((2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_right hj hsqrt_pos.le
      _ = (M : ℝ) / √((2 : ℝ) ^ n) := by
          rw [eq_div_iff hsqrt_pos.ne', mul_assoc, ← sq, Real.sq_sqrt (by positivity),
            div_mul_cancel₀ _ (by positivity)]
  refine (measure_mono hsub).trans ?_
  simpa using
    (hB.hasLaw_normalizedBrownianIncrements hg).measure_forall_abs_le_of_pi_gaussianReal_zero_one
      ((M : ℝ) / √((2 : ℝ) ^ n))

/-- Quantitative Paley–Wiener–Zygmund small-ball union bound: the probability that on `[0, N]` some
window of three consecutive dyadic `2⁻ⁿ`-increments has all three increments bounded by `M / 2ⁿ`
decays geometrically like `N * (√(2 / π) * M)³ * ((√2)⁻¹)ⁿ`. -/
theorem measure_exists_dyadic_three_increments_le (hB : IsPreBrownianReal B P) (N M n : ℕ) :
    P {ω | ∃ m < N * 2 ^ n, ∀ j : Fin 3,
        |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
          B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ (M : ℝ) / 2 ^ n} ≤
      ENNReal.ofReal ((N : ℝ) * (√(2 / π) * (M : ℝ)) ^ 3 * (√2)⁻¹ ^ n) := by
  let W : ℕ → Set Ω := fun m ↦ {ω | ∀ j : Fin 3,
    |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
      B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ (M : ℝ) / 2 ^ n}
  have hunion : {ω | ∃ m < N * 2 ^ n, ∀ j : Fin 3,
      |B (((m + j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω -
        B (((m + j : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω| ≤ (M : ℝ) / 2 ^ n} =
      ⋃ m ∈ Finset.range (N * 2 ^ n), W m := by
    ext ω
    simp [W]
  rw [hunion]
  calc
    P (⋃ m ∈ Finset.range (N * 2 ^ n), W m)
      ≤ ∑ m ∈ Finset.range (N * 2 ^ n), P (W m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ Finset.range (N * 2 ^ n),
          ENNReal.ofReal (√(2 / π) * ((M : ℝ) / √((2 : ℝ) ^ n))) ^ 3 :=
        Finset.sum_le_sum fun m _ ↦ hB.measure_forall_dyadic_three_increments_le M n m
    _ = ((N * 2 ^ n : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (√(2 / π) * ((M : ℝ) / √((2 : ℝ) ^ n))) ^ 3 := by
        simp
    _ = ENNReal.ofReal ((N : ℝ) * (√(2 / π) * (M : ℝ)) ^ 3 * (√2)⁻¹ ^ n) := by
        have hr_nn : 0 ≤ √(2 / π) * ((M : ℝ) / √((2 : ℝ) ^ n)) := by positivity
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

/-- Almost surely, for every horizon `N : ℕ` and slope bound `M : ℕ`, at all sufficiently fine
dyadic scales `2⁻ⁿ` every window of three consecutive increments on `[0, N]` contains at least one
increment strictly larger than `M / 2ⁿ`. -/
theorem ae_eventually_forall_exists_dyadic_three_increment_gt (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n, ∃ j : Fin 3,
      (M : ℝ) / 2 ^ n <
        |B (((m + j + 1 : ℕ) : ℝ) / 2 ^ n).toNNReal ω -
          B (((m + j : ℕ) : ℝ) / 2 ^ n).toNNReal ω| := by
  have htoNN (k n : ℕ) : (((k : ℝ) / 2 ^ n).toNNReal) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    simp
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
      tsum_le_tsum fun n ↦ hB.measure_exists_dyadic_three_increments_le N M n
    refine ne_top_of_le_ne_top ?_ htsum
    have hs : Summable fun n : ℕ ↦ (N : ℝ) * (√(2 / π) * (M : ℝ)) ^ 3 * (√2)⁻¹ ^ n :=
      (summable_geometric_of_lt_one (by positivity) hlt1).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  refine hω.mono fun n hn m hm ↦ ?_
  simp only [E, Set.mem_ofPred_eq, not_exists, not_and, not_forall, not_le] at hn
  obtain ⟨j, hj⟩ := hn m hm
  exact ⟨j, by simpa only [htoNN] using hj⟩

/-- Almost surely, on one common full-measure event, `s ↦ B s.toNNReal ω` fails the right-sided
pointwise Lipschitz bound `(· - B t.toNNReal ω) =O[𝓝[>] t] (· - t)` at every `t ≥ 0` and fails the
left-sided pointwise Lipschitz bound `(· - B t.toNNReal ω) =O[𝓝[<] t] (· - t)` at every `t > 0`. -/
theorem ae_not_isBigO_sub_nhdsGT_and_nhdsLT (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 ≤ t →
        ¬ (fun s : ℝ ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[>] t] (· - t)) ∧
      (∀ t : ℝ, 0 < t →
        ¬ (fun s : ℝ ↦ B s.toNNReal ω - B t.toNNReal ω) =O[𝓝[<] t] (· - t)) := by
  filter_upwards [hB.ae_eventually_forall_exists_dyadic_three_increment_gt] with ω hosc
  have hosc' : ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n, ∃ j : Fin 3,
      (M : ℝ) / 2 ^ n <
        ‖B (((m + j + 1 : ℕ) : ℝ) / 2 ^ n).toNNReal ω -
          B (((m + j : ℕ) : ℝ) / 2 ^ n).toNNReal ω‖ := by
    simpa only [Real.norm_eq_abs] using hosc
  exact ⟨fun t ht ↦ not_isBigO_sub_nhdsGT_of_dyadic hosc' ht,
    fun t ht ↦ not_isBigO_sub_nhdsLT_of_dyadic hosc' ht⟩

/-- Almost surely, `s ↦ B s.toNNReal ω` has no right derivative at any `t ≥ 0`. -/
theorem ae_not_differentiableWithinAt_Ici (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Ici t) t := by
  filter_upwards [hB.ae_eventually_forall_exists_dyadic_three_increment_gt] with ω hosc t ht
  exact not_differentiableWithinAt_Ici_of_dyadic (by simpa only [Real.norm_eq_abs] using hosc) ht

/-- Almost surely, `s ↦ B s.toNNReal ω` has no left derivative at any `t > 0`. -/
theorem ae_not_differentiableWithinAt_Iic (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Iic t) t := by
  filter_upwards [hB.ae_eventually_forall_exists_dyadic_three_increment_gt] with ω hosc t ht
  exact not_differentiableWithinAt_Iic_of_dyadic (by simpa only [Real.norm_eq_abs] using hosc) ht

/-- Almost surely, `s ↦ B s.toNNReal ω` is not differentiable at any `t ≥ 0`. -/
theorem ae_not_differentiableAt (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t := by
  filter_upwards [hB.ae_not_differentiableWithinAt_Ici] with ω hω t ht hd
  exact hω t ht hd.differentiableWithinAt

/-- **Paley–Wiener–Zygmund simultaneous nowhere differentiability of Brownian motion**
(Mörters–Peres, Theorem 1.30; Lalley, Proposition 9): one common full-measure event excludes
two-sided derivatives at every positive time and excludes the right derivative at zero.
(The extension by `Real.toNNReal` clamps negative arguments to `0`, so the extended function is
constant on `(-∞, 0]`.) -/
theorem ae_not_differentiableAt_and_not_differentiableWithinAt_zero
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 < t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t) ∧
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Ici 0) 0 := by
  filter_upwards [hB.ae_not_differentiableWithinAt_Ici] with ω hω
  exact ⟨fun t ht hd ↦ hω t ht.le hd.differentiableWithinAt, hω 0 le_rfl⟩

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Almost every sample path of a Brownian motion `B`, extended to `ℝ` via `Real.toNNReal`, is
continuous on `ℝ`, differentiable at no positive time, and not right-differentiable at `0`. -/
theorem ae_continuous_and_not_differentiableAt_and_not_differentiableWithinAt_zero
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P,
      Continuous (fun s : ℝ ↦ B s.toNNReal ω) ∧
        (∀ t : ℝ, 0 < t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t) ∧
        ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Ici 0) 0 := by
  filter_upwards [hB.cont, hB.ae_not_differentiableAt_and_not_differentiableWithinAt_zero] with ω
    hc hnd
  exact ⟨hc.comp continuous_real_toNNReal, hnd⟩

/-- Reflecting a Brownian motion across `t = 0` via `s ↦ B |s|.toNNReal ω` yields sample paths that
are almost surely continuous on all of `ℝ` and differentiable at **no** real number `t : ℝ`. -/
theorem ae_continuous_abs_and_forall_not_differentiableAt (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P,
      Continuous (fun s : ℝ ↦ B |s|.toNNReal ω) ∧
        ∀ t : ℝ, ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B |s|.toNNReal ω) t := by
  filter_upwards [hB.cont, hB.ae_not_differentiableWithinAt_Ici] with ω hc hnd
  refine ⟨hc.comp (continuous_real_toNNReal.comp continuous_abs), fun t hd ↦ ?_⟩
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · have heq : (fun s : ℝ ↦ B |s|.toNNReal ω) =ᶠ[𝓝 t] fun s : ℝ ↦ B s.toNNReal ω := by
      filter_upwards [Ioi_mem_nhds ht] with s (hs : 0 < s)
      rw [abs_of_pos hs]
    exact hnd t ht.le (hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt
  · have hwithin : DifferentiableWithinAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) (Ici 0) 0 :=
      hd.differentiableWithinAt.congr (fun s hs ↦ by rw [abs_of_nonneg hs]) (by simp)
    exact hnd 0 le_rfl hwithin
  · have hd_neg : DifferentiableAt ℝ (fun s : ℝ ↦ B |-s|.toNNReal ω) (-t) :=
      DifferentiableAt.comp (-t) (by simpa only [id_eq, neg_neg] using hd)
        differentiableAt_id.fun_neg
    have hpos : 0 < -t := neg_pos.mpr ht
    have heq : (fun s : ℝ ↦ B |-s|.toNNReal ω) =ᶠ[𝓝 (-t)] fun s : ℝ ↦ B s.toNNReal ω := by
      filter_upwards [Ioi_mem_nhds hpos] with s (hs : 0 < s)
      rw [abs_neg, abs_of_pos hs]
    exact hnd (-t) hpos.le (hd_neg.congr_of_eventuallyEq heq.symm).differentiableWithinAt

end ProbabilityTheory.IsBrownianReal
