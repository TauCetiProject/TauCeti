/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.Matrix.HardThreshold
public import TauCeti.Probability.Moments.CenteredTruncation
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Summable
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.MeasureTheory.Integral.Bochner.Markov
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.IdentDistrib
import TauCeti.Probability.Independence.Basic

/-!
# Operator-norm truncation of rectangular data matrices

Let `x` be an array, indexed by `ℕ × ℕ`, of entries with a common law `ν` that are independent
within each row and within each column, and let `Xₙ` be its top-left `p(n) × n` corner, where
`p(n) ≤ K n` eventually. Cut off the entries at the unnormalized level `n^a`. If `ν` has a finite
absolute moment of order `m` and `2 < q (m a - 1)`, then
almost surely every row and every column of `Xₙ` eventually has fewer than `q` entries above the
cutoff, by the union bound `TauCeti.Probability.measure_exists_le_card_filter_lt_norm_le` over
`q`-element sets of positions and Borel–Cantelli. If `ν` has a
finite fourth moment, the largest entry of `Xₙ` is almost surely `o(√n)`, without any
independence.

For complex entries with a finite fourth moment and `a > 1/4`, the finite Schur test combines
these two facts: the discarded part of `Xₙ`, its entrywise hard threshold at `n^a`, has
operator norm `o(√n)` almost surely. When `ν` is centred, the mean subtracted in recentring
the retained entries contributes `o(√n)` as well. Hence `Xₙ` and the matrix of centered
truncations of its entries at `n^a` differ by `o(√n)` in operator norm almost surely. The
centered truncations are bounded and centred, so this reduces operator-norm bounds for `Xₙ / √n`,
and with them the upper edge of the sample covariance spectrum, to bounded centred entries.

## Main results

The results about the corners are filed under `TauCeti.Probability.SampleCovariance`.

* `SampleCovariance.ae_eventually_card_filter_lt_norm_lt`: almost surely, every row and every
  column of the corners eventually has fewer than `q` entries above `n^a`.
* `SampleCovariance.ae_eventually_norm_le_mul_sqrt`: almost surely, the largest entry of the
  corners is eventually below `ε √n` for every `ε > 0`.
* `SampleCovariance.ae_tendsto_l2_opNorm_hardThreshold_div_sqrt`: the discarded part has
  operator norm `o(√n)` almost surely.
* `SampleCovariance.ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt`: the corners and
  their centered truncations differ by `o(√n)` in operator norm almost surely.

## References

* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988).
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.2.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability.SampleCovariance

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section Count

variable [SeminormedAddGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {x : ℕ × ℕ → Ω → E} {ν : Measure E} {p : ℕ → ℕ}

/-- In the `p(n) × n` corner of an array with common law `ν`, independent within each row and
within each column, the measure of the set where some row or some column has at least `q` entries
above a cutoff `R > 0` is at most `(p(n) n^q + n p(n)^q) τ^q`, where `τ` is the `m`-th absolute
moment of `ν` divided by `R ^ m`. -/
private theorem measure_exists_row_or_col_le_card_filter_le (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) {m : ℕ} (hm : Integrable (fun z ↦ ‖z‖ ^ m) ν)
    (n q : ℕ) {R : ℝ} (hR : 0 < R) :
    P ({ω | ∃ i : Fin (p n), q ≤ (Finset.univ.filter fun j : Fin n ↦ R < ‖x (i, j) ω‖).card} ∪
      {ω | ∃ j : Fin n, q ≤ (Finset.univ.filter fun i : Fin (p n) ↦ R < ‖x (i, j) ω‖).card}) ≤
      (p n * n ^ q + n * p n ^ q) * ENNReal.ofReal ((∫ z, ‖z‖ ^ m ∂ν) / R ^ m) ^ q := by
  -- Each entry exceeds the cutoff with probability at most the Markov bound for `ν`.
  have htail (ij : ℕ × ℕ) :
      P {ω | R < ‖x ij ω‖} ≤ ENNReal.ofReal ((∫ z, ‖z‖ ^ m ∂ν) / R ^ m) := by
    rw [(hx ij).measure_eq (p := fun z ↦ R < ‖z‖)
      (measurableSet_lt measurable_const continuous_norm.measurable)]
    exact meas_norm_gt_le_integral_norm_pow_div_pow (Z := fun z ↦ z) m hm hR
  have hrow := measure_exists_le_card_filter_lt_norm_le
    (Y := fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j))
    (fun i ↦ (hrow i).precomp Fin.val_injective) R (fun _ _ ↦ htail _)
    (fun _ ↦ (Fintype.card_fin n).le) q
  have hcol := measure_exists_le_card_filter_lt_norm_le
    (Y := fun (j : Fin n) (i : Fin (p n)) ↦ x (i, j))
    (fun j ↦ (hcol j).precomp Fin.val_injective) R (fun _ _ ↦ htail _)
    (fun _ ↦ (Fintype.card_fin (p n)).le) q
  simp only [Fintype.card_fin] at hrow hcol
  calc
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hrow hcol)
    _ = _ := by ring

/-- The real inequality behind the summable bound for row and column counts: if `0 ≤ P' ≤ K N`
with `N > 0`, then `(P' N^q + N P'^q) (C / N^(a m))^q ≤ (K + K^q) C^q N^(q + 1 - a m q)`. -/
private theorem corner_count_bound_le {N P' K C a : ℝ} {m q : ℕ} (hN : 0 < N) (hP₀ : 0 ≤ P')
    (hP : P' ≤ K * N) (hC : 0 ≤ C) :
    (P' * N ^ q + N * P' ^ q) * (C / (N ^ a) ^ m) ^ q ≤
      (K + K ^ q) * C ^ q * N ^ ((q : ℝ) + 1 - a * m * q) := by
  have h₁ : P' * N ^ q ≤ K * N ^ (q + 1) := by
    calc P' * N ^ q ≤ K * N * N ^ q := by gcongr
      _ = K * N ^ (q + 1) := by ring
  have h₂ : N * P' ^ q ≤ K ^ q * N ^ (q + 1) := by
    calc N * P' ^ q ≤ N * (K * N) ^ q := by gcongr
      _ = K ^ q * N ^ (q + 1) := by ring
  calc
    _ ≤ (K * N ^ (q + 1) + K ^ q * N ^ (q + 1)) * (C / (N ^ a) ^ m) ^ q := by gcongr
    _ = (K + K ^ q) * (N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q) := by ring
    _ = _ := by
      rw [pow_add_one_mul_div_rpow_pow_pow hN]
      ring

/-- **Row and column counts of large entries.** Let the array have entries with a common law `ν`
of finite `m`-th absolute moment, independent within each row and within each column, and let
`p(n) ≤ K n` eventually. If
`2 < q * (m * a - 1)`, then almost surely, eventually every row and every column of the
`p(n) × n` corner has fewer than `q` entries of norm above `n ^ a`. -/
theorem ae_eventually_card_filter_lt_norm_lt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) {m : ℕ} (hm : Integrable (fun z ↦ ‖z‖ ^ m) ν)
    {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) {a : ℝ} {q : ℕ} (hq : 2 < q * (m * a - 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ i : Fin (p n), (Finset.univ.filter fun j : Fin n ↦
        (n : ℝ) ^ a < ‖x (i, j) ω‖).card < q) ∧
      ∀ j : Fin n, (Finset.univ.filter fun i : Fin (p n) ↦
        (n : ℝ) ^ a < ‖x (i, j) ω‖).card < q := by
  let C := ∫ z, ‖z‖ ^ m ∂ν
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ by positivity
  have hb : ∑' n : ℕ, ENNReal.ofReal ((K + K ^ q) * C ^ q * (n : ℝ) ^ ((q : ℝ) + 1 - a * m * q))
      < ∞ :=
    ((Real.summable_nat_rpow.2 (by nlinarith)).mul_left _).tsum_ofReal_lt_top
  have hbound : ∀ᶠ n in atTop,
      P ({ω | ∃ i : Fin (p n), q ≤ (Finset.univ.filter fun j : Fin n ↦
          (n : ℝ) ^ a < ‖x (i, j) ω‖).card} ∪
        {ω | ∃ j : Fin n, q ≤ (Finset.univ.filter fun i : Fin (p n) ↦
          (n : ℝ) ^ a < ‖x (i, j) ω‖).card}) ≤
        ENNReal.ofReal ((K + K ^ q) * C ^ q * (n : ℝ) ^ ((q : ℝ) + 1 - a * m * q)) := by
    filter_upwards [hp, eventually_gt_atTop 0] with n hpn hn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    refine (measure_exists_row_or_col_le_card_filter_le hx hrow hcol hm n q
      (Real.rpow_pos_of_pos hN a)).trans ?_
    calc
      _ = ENNReal.ofReal ((p n * n ^ q + n * p n ^ q) *
          ((∫ z, ‖z‖ ^ m ∂ν) / ((n : ℝ) ^ a) ^ m) ^ q) := by
        -- Move `ENNReal.ofReal` through the nonnegative sums, products and powers.
        simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add,
          ENNReal.ofReal_pow, ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (corner_count_bound_le hN (Nat.cast_nonneg _) hpn hC)
  filter_upwards [TauCeti.MeasureTheory.ae_eventually_notMem_of_eventually_measure_le hb hbound]
    with ω hω
  filter_upwards [hω] with n hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_le] at hn
  exact hn

end Count

section Maximum

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {x : ℕ × ℕ → Ω → E} {ν : Measure E} {p : ℕ → ℕ}

/-- **Largest entry of the corners.** If the entries of the array share a law `ν` with finite
fourth moment and `p(n) ≤ K n` eventually, then almost surely, for every `ε > 0`, every entry of
the `p(n) × n` corner eventually has norm at most `ε √n`. Independence is unnecessary. -/
theorem ae_eventually_norm_le_mul_sqrt (hx : ∀ ij, HasLaw (x ij) ν P) (h4 : MemLp id 4 ν)
    {K : ℝ} (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (i : Fin (p n)) (j : Fin n),
      ‖x (i, j) ω‖ ≤ ε * √n := by
  let L : ℝ := |K| + 1
  have hL : 0 < L := by positivity
  have hs : Tendsto (fun n : ℕ ↦ √(L * n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop hL)
  -- Enumerate the array along `Nat.pair`; the corner lies in the first `max (p n) n ^ 2` terms.
  have hm : ∀ᶠ n in atTop, ((max (p n) n ^ 2 : ℕ) : ℝ) ≤ √(L * n) ^ 4 := by
    filter_upwards [hp] with n hn
    have hmax : (max (p n) n : ℝ) ≤ L * n := by
      refine max_le (hn.trans ?_) ?_ <;> nlinarith [le_abs_self K, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    push_cast
    exact pow_le_pow_left₀ (by positivity) hmax 2
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib (p := 4)
    (X := fun k ↦ x (Nat.unpair k)) (fun k ↦ (hx _).identDistrib HasLaw.id) h4 hs
    (by simpa only [NNReal.coe_ofNat, ← Real.rpow_natCast, Nat.cast_ofNat] using hm)]
    with ω hω ε hε
  filter_upwards [hω (ε / √L) (by positivity)] with n hn i j
  have hk : Nat.pair i j < max (p n) n ^ 2 :=
    (Nat.pair_lt_max_add_one_sq i j).trans_le (Nat.pow_le_pow_left (by omega) 2)
  have h := hn _ hk
  rw [Nat.unpair_pair] at h
  refine h.trans_eq ?_
  have : 0 < √L := Real.sqrt_pos.2 hL
  rw [Real.sqrt_mul hL.le]
  field_simp

end Maximum

section OperatorNorm

variable {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} {p : ℕ → ℕ}

/-- Entrywise, a corner minus the matrix of centered truncations of its entries at `n ^ a` is the
hard threshold of the corner at `n ^ a` plus the constant matrix of the common truncated mean. -/
private theorem of_sub_of_centeredTruncation_eq (hx : ∀ ij, HasLaw (x ij) ν P) (n : ℕ) (a : ℝ)
    (ω : Ω) :
    (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω) -
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
          centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω) =
      (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).hardThreshold ((n : ℝ) ^ a) +
        Matrix.of fun _ _ ↦ ∫ z, {z : ℂ | ‖id z‖ ≤ (n : ℝ) ^ a}.indicator id z ∂ν := by
  ext i j
  have hc := ((hx (i, j)).identDistrib HasLaw.id).integral_indicator_setOf_norm_le_eq
    ((n : ℝ) ^ a)
  simp only [Matrix.sub_apply, Matrix.add_apply, of_apply, hardThreshold_apply,
    centeredTruncation_def, NNReal.coe_rpow, NNReal.coe_natCast, hc]
  by_cases h : ‖x (i, j) ω‖ ≤ (n : ℝ) ^ a
  · simp [h, not_lt.2 h]
  · simp [h, lt_of_not_ge h]

/-- **The discarded part of the corners.** Let the array have complex entries with a common law
`ν` of finite fourth moment, independent within each row and within each column, and let
`p(n) ≤ K n` eventually. For `a > 1/4`, the
entrywise hard threshold at `n ^ a` of the `p(n) × n` corner, the matrix of its entries of norm
above `n ^ a`, has operator norm `o(√n)` almost surely. -/
theorem ae_tendsto_l2_opNorm_hardThreshold_div_sqrt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) (h4 : MemLp id 4 ν) {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ‖(Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).hardThreshold ((n : ℝ) ^ a)‖ /
        √n) atTop (𝓝 0) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / (4 * a - 1))
  have hq' : 2 < q * (((4 : ℕ) : ℝ) * a - 1) := by
    push_cast
    exact (div_lt_iff₀ (by linarith)).1 hq
  filter_upwards [ae_eventually_card_filter_lt_norm_lt hx hrow hcol
      (h4.integrable_norm_pow (p := 4) (by norm_num)) hp hq',
    ae_eventually_norm_le_mul_sqrt hx h4 hp] with ω hcount hmax
  refine tendsto_order.2 ⟨fun r hr ↦ .of_forall fun n ↦ hr.trans_le (by positivity), fun r hr ↦ ?_⟩
  have hε : 0 < r / (q + 1 : ℝ) := by positivity
  filter_upwards [hcount, hmax _ hε, eventually_gt_atTop 0] with n ⟨hrow, hcol⟩ hentry hn
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [div_lt_iff₀ hsqrt]
  refine ((Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).l2_opNorm_hardThreshold_le _
    (M := r / (q + 1) * √n) (by positivity) (fun i ↦ (hrow i).le) (fun j ↦ (hcol j).le)
    (fun i j _ ↦ by simpa only [of_apply] using hentry i j)).trans_lt ?_
  calc
    (q : ℝ) * (r / (q + 1) * √n) < (q + 1) * (r / (q + 1) * √n) := by gcongr; linarith
    _ = r * √n := by field_simp

/-- **Operator-norm truncation of the corners.** Let the array have complex entries with a common
centred law `ν` of finite fourth moment, independent within each row and within each column, and
let `p(n) ≤ K n` eventually. For
`a > 1/4`, the `p(n) × n` corner and the matrix of centered truncations of its entries at
`n ^ a` differ by `o(√n)` in operator norm almost surely. -/
theorem ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) (h4 : MemLp id 4 ν)
    (hmean : ∫ z, z ∂ν = 0) {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ ‖(Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω) -
      Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
        centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω‖ / √n) atTop (𝓝 0) := by
  -- The common mean of the truncated entries at size `n`.
  let c (n : ℕ) : ℂ := ∫ z, {z : ℂ | ‖id z‖ ≤ (n : ℝ) ^ a}.indicator id z ∂ν
  -- The constant matrix of the means has operator norm at most `√(p n) * ‖c n‖ * √n`.
  have hconst (n : ℕ) :
      ‖(Matrix.of fun (_ : Fin (p n)) (_ : Fin n) ↦ c n)‖ / √n ≤ √(p n) * ‖c n‖ := by
    refine div_le_of_le_mul₀ (Real.sqrt_nonneg _) (by positivity) ?_
    refine (Matrix.l2_opNorm_le_sqrt_mul_of_row_col_sum_le
      (Matrix.of fun (_ : Fin (p n)) (_ : Fin n) ↦ c n) (r := n * ‖c n‖) (c := p n * ‖c n‖)
      (fun _ ↦ by simp) (fun _ ↦ by simp)).trans_eq ?_
    rw [show (n : ℝ) * ‖c n‖ * (p n * ‖c n‖) = (√(p n) * ‖c n‖ * √n) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      ring, Real.sqrt_sq (by positivity)]
  -- `√(p n) / (n ^ a) ^ 3 → 0`, comparing `p n` with `(|K| + 1) n`.
  have hquot : Tendsto (fun n ↦ √(p n) / ((n : ℝ) ^ a) ^ 3) atTop (𝓝 0) := by
    have hlim := ((tendsto_sqrt_div_rpow_pow_atTop_nhds_zero (a := a) (k := 3)
      (by push_cast; linarith)).comp tendsto_natCast_atTop_atTop).const_mul √(|K| + 1)
    rw [mul_zero] at hlim
    refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_ hlim
    filter_upwards [hp] with n hn
    dsimp only [Function.comp_apply]
    rw [← mul_div_assoc, ← Real.sqrt_mul (by positivity)]
    gcongr
    exact hn.trans (by nlinarith [le_abs_self K, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  -- The means vanish fast enough, by the fourth moment.
  have hc : Tendsto (fun n ↦ √(p n) * ‖c n‖) atTop (𝓝 0) :=
    h4.tendsto_mul_norm_integral_indicator_setOf_norm_le_nhds_zero (k := 3) hmean hquot
  filter_upwards [ae_tendsto_l2_opNorm_hardThreshold_div_sqrt hx hrow hcol h4 hp ha]
    with ω hω
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) (by simpa using hω.add hc)
  rw [of_sub_of_centeredTruncation_eq hx]
  calc
    _ ≤ (‖(Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).hardThreshold ((n : ℝ) ^ a)‖ +
        ‖(Matrix.of fun (_ : Fin (p n)) (_ : Fin n) ↦ c n)‖) / √n :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add le_rfl (hconst n)

end OperatorNorm

end TauCeti.Probability.SampleCovariance
