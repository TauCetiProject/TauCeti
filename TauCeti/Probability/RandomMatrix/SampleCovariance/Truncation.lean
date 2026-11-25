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
`q`-element sets of positions and Borel–Cantelli. For the rows alone, independence within each
row suffices, and the row length may be any `ℓ(n) ≤ K n`. If `ν` has a
finite fourth moment, the largest entry of `Xₙ` is almost surely `o(√n)`, without any
independence; if `ν` has a finite second moment, it is almost surely `o(n)`.

For complex entries with a finite fourth moment and `a > 1/4`, the finite Schur test combines
these two facts: the discarded part of `Xₙ`, its entrywise hard threshold at `n^a`, has
operator norm `o(√n)` almost surely. When `ν` is centred, the mean subtracted in recentring
the retained entries contributes `o(√n)` as well. Hence `Xₙ` and the matrix of centered
truncations of its entries at `n^a` differ by `o(√n)` in operator norm almost surely. The
centered truncations are bounded and centred, so this reduces operator-norm bounds for `Xₙ / √n`,
and with them the upper edge of the sample covariance spectrum, to bounded centred entries.

## Main results

The results about the corners are filed under `TauCeti.Probability.SampleCovariance`.

* `SampleCovariance.ae_eventually_forall_card_filter_lt_norm_lt`: almost surely, every row of the
  `r(n) × ℓ(n)` corners eventually has fewer than `q` entries above `n^a`.
* `SampleCovariance.ae_eventually_card_filter_lt_norm_lt`: almost surely, every row and every
  column of the corners eventually has fewer than `q` entries above `n^a`.
* `SampleCovariance.ae_eventually_norm_le_mul_sqrt`: almost surely, the largest entry of the
  corners is eventually below `ε √n` for every `ε > 0`.
* `SampleCovariance.ae_eventually_norm_le_mul`: under a second moment, almost surely the largest
  entry of the corners is eventually below `ε n` for every `ε > 0`.
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

variable [SeminormedAddGroup E] [MeasurableSpace E] {x : ℕ × ℕ → Ω → E} {ν : Measure E}
  {p : ℕ → ℕ}

/-- The real inequality behind the summable bound for row counts: if `0 ≤ R ≤ K N` and
`0 ≤ L ≤ K N` with `N > 0`, then `R L^q (C / N^(a m))^q ≤ K^(q + 1) C^q N^(q + 1 - a m q)`. -/
private theorem row_count_bound_le {N R L K C a : ℝ} {m q : ℕ} (hN : 0 < N) (hR₀ : 0 ≤ R)
    (hR : R ≤ K * N) (hL₀ : 0 ≤ L) (hL : L ≤ K * N) (hC : 0 ≤ C) :
    R * L ^ q * (C / (N ^ a) ^ m) ^ q ≤ K ^ (q + 1) * C ^ q * N ^ ((q : ℝ) + 1 - a * m * q) := by
  have hKN : 0 ≤ K * N := hR₀.trans hR
  calc
    _ ≤ K * N * (K * N) ^ q * (C / (N ^ a) ^ m) ^ q := by gcongr
    _ = K ^ (q + 1) * (N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q) := by ring
    _ = _ := by
      rw [pow_add_one_mul_div_rpow_pow_pow hN]
      ring

/-- **Row counts of large entries.** Let the array have entries with a common law `ν` of finite
`m`-th absolute moment, independent within each row, and let `r(n), ℓ(n) ≤ K n` eventually. If
`2 < q * (m * a - 1)`, then almost surely, eventually every row of the `r(n) × ℓ(n)` corner has
fewer than `q` entries of norm above `n ^ a`. Distinct rows may be dependent. -/
theorem ae_eventually_forall_card_filter_lt_norm_lt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P) {m : ℕ} (hm : Integrable (fun z ↦ ‖z‖ ^ m) ν)
    {r ℓ : ℕ → ℕ} {K : ℝ} (hr : ∀ᶠ n in atTop, (r n : ℝ) ≤ K * n)
    (hℓ : ∀ᶠ n in atTop, (ℓ n : ℝ) ≤ K * n) {a : ℝ} {q : ℕ} (hq : 2 < q * (m * a - 1)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i : Fin (r n),
      (Finset.univ.filter fun j : Fin (ℓ n) ↦ (n : ℝ) ^ a < ‖x (i, j) ω‖).card < q := by
  -- Count in the real array of norms; the norm is a.e. measurable as the `m`-th root of `‖·‖ ^ m`.
  have hm₀ : m ≠ 0 := by
    rintro rfl
    push_cast at hq
    nlinarith [(q.cast_nonneg : (0 : ℝ) ≤ q)]
  have hnorm : AEMeasurable (fun z : E ↦ ‖z‖) ν :=
    (hm.aemeasurable.pow_const (m⁻¹ : ℝ)).congr
      (.of_forall fun z ↦ Real.pow_rpow_inv_natCast (norm_nonneg z) hm₀)
  have hm' : Integrable (fun t : ℝ ↦ ‖t‖ ^ m) (ν.map fun z ↦ ‖z‖) := by
    rw [integrable_map_measure (by fun_prop) hnorm]
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_norm] using hm
  have hrow' (i : ℕ) : iIndepFun (fun j ω ↦ ‖x (i, j) ω‖) P :=
    (hrow i).comp₀ (fun _ z ↦ ‖z‖) (fun _ ↦ (hx _).aemeasurable) fun _ ↦ by rwa [(hx _).map_eq]
  let C := ∫ t, ‖t‖ ^ m ∂(ν.map fun z ↦ ‖z‖)
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ by positivity
  have hb : ∑' n : ℕ, ENNReal.ofReal (K ^ (q + 1) * C ^ q * (n : ℝ) ^ ((q : ℝ) + 1 - a * m * q))
      < ∞ :=
    ((Real.summable_nat_rpow.2 (by nlinarith)).mul_left _).tsum_ofReal_lt_top
  -- Each entry exceeds a positive cutoff `R` with probability at most the Markov bound for the
  -- law of its norm.
  have htail (ij : ℕ × ℕ) {R : ℝ} (hR : 0 < R) :
      P {ω | R < ‖‖x ij ω‖‖} ≤ ENNReal.ofReal (C / R ^ m) := by
    rw [((hasLaw_map hnorm).fun_comp (hx ij)).measure_eq (p := fun t ↦ R < ‖t‖)
      (measurableSet_lt measurable_const continuous_norm.measurable)]
    exact meas_norm_gt_le_integral_norm_pow_div_pow (Z := fun t ↦ t) m hm' hR
  have hbound : ∀ᶠ n in atTop,
      P {ω | ∃ i : Fin (r n), q ≤ (Finset.univ.filter fun j : Fin (ℓ n) ↦
          (n : ℝ) ^ a < ‖x (i, j) ω‖).card} ≤
        ENNReal.ofReal (K ^ (q + 1) * C ^ q * (n : ℝ) ^ ((q : ℝ) + 1 - a * m * q)) := by
    filter_upwards [hr, hℓ, eventually_gt_atTop 0] with n hrn hℓn hn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    have hcount := measure_exists_le_card_filter_lt_norm_le
      (Y := fun (i : Fin (r n)) (j : Fin (ℓ n)) ω ↦ ‖x (i, j) ω‖)
      (fun i ↦ (hrow' i).precomp Fin.val_injective) _
      (fun _ _ ↦ htail _ (Real.rpow_pos_of_pos hN a)) (fun _ ↦ (Fintype.card_fin (ℓ n)).le) q
    simp only [Fintype.card_fin, Real.norm_eq_abs, abs_norm] at hcount
    refine hcount.trans ?_
    calc
      _ = ENNReal.ofReal (r n * ℓ n ^ q * (C / ((n : ℝ) ^ a) ^ m) ^ q) := by
        -- Move `ENNReal.ofReal` through the nonnegative products and powers.
        simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
          ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (row_count_bound_le hN (Nat.cast_nonneg _) hrn (Nat.cast_nonneg _) hℓn hC)
  filter_upwards [TauCeti.MeasureTheory.ae_eventually_notMem_of_eventually_measure_le hb hbound]
    with ω hω
  filter_upwards [hω] with n hn
  simpa only [mem_ofPred_eq, not_exists, not_le] using hn

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
  -- Both dimensions are at most `max K 1 * n`; the columns are the rows of the transpose.
  have hp' : ∀ᶠ n in atTop, (p n : ℝ) ≤ max K 1 * n :=
    hp.mono fun n hn ↦ hn.trans (by gcongr; exact le_max_left _ _)
  have hn : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ max K 1 * n :=
    .of_forall fun n ↦ le_mul_of_one_le_left n.cast_nonneg (le_max_right _ _)
  filter_upwards [ae_eventually_forall_card_filter_lt_norm_lt (ℓ := fun n ↦ n) hx hrow hm hp' hn hq,
    ae_eventually_forall_card_filter_lt_norm_lt (x := fun ij ↦ x ij.swap) (r := fun n ↦ n)
      (fun _ ↦ hx _) hcol hm hn hp' hq] with ω hω₁ hω₂
  filter_upwards [hω₁, hω₂] with n h₁ h₂ using ⟨h₁, h₂⟩

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

section SecondMoment

variable [SeminormedAddGroup E] [MeasurableSpace E] {x : ℕ × ℕ → Ω → E} {ν : Measure E}
  {p : ℕ → ℕ}

/-- **Largest entry of the corners under a second moment.** If the entries of the array share a
law `ν` with finite second moment and `p(n) ≤ K n` eventually, then almost surely, for every
`ε > 0`, every entry of the `p(n) × n` corner eventually has norm at most `ε n`. Independence is
unnecessary. -/
theorem ae_eventually_norm_le_mul (hx : ∀ ij, HasLaw (x ij) ν P)
    (h2 : Integrable (fun z ↦ ‖z‖ ^ 2) ν) {K : ℝ} (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (i : Fin (p n)) (j : Fin n),
      ‖x (i, j) ω‖ ≤ ε * n := by
  -- The norm is a.e. measurable as the square root of `‖·‖ ^ 2`, and the square roots
  -- `‖x‖ ^ (1 / 2)` of the norms have a finite fourth moment.
  have hnorm : AEMeasurable (fun z : E ↦ ‖z‖) ν :=
    h2.aemeasurable.sqrt.congr (.of_forall fun z ↦ Real.sqrt_sq (norm_nonneg z))
  let f : E → ℝ := fun z ↦ ‖z‖ ^ (2⁻¹ : ℝ)
  have hf : AEMeasurable f ν := hnorm.pow_const _
  have h4 : MemLp id 4 (ν.map f) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hf]
    have h := ((memLp_two_iff_integrable_sq hnorm.aestronglyMeasurable).2 h2).norm_rpow_div 2⁻¹
    have h4 : (2 : ℝ≥0∞) / 2⁻¹ = 4 := by
      rw [div_eq_mul_inv, inv_inv]
      norm_num
    rw [h4] at h
    simpa [f] using h
  filter_upwards [ae_eventually_norm_le_mul_sqrt
    (fun ij ↦ (hasLaw_map hf).fun_comp (hx ij)) h4 hp] with ω hω ε hε
  filter_upwards [hω (√ε) (Real.sqrt_pos.2 hε)] with n hn i j
  have hle : ‖x (i, j) ω‖ ^ (2⁻¹ : ℝ) ≤ √ε * √n := by
    simpa [f, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hn i j
  calc
    ‖x (i, j) ω‖ = (‖x (i, j) ω‖ ^ (2⁻¹ : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    _ ≤ (√ε * √n) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    _ = ε * n := by rw [mul_pow, Real.sq_sqrt hε.le, Real.sq_sqrt n.cast_nonneg]

end SecondMoment

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
