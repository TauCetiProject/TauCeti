/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.Truncation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.Moments.Bernstein

/-!
# A uniform strong law for the rows of double arrays

Let `ξ` be a real array, indexed by `ℕ × ℕ`, whose entries have a common law `μ` with finite
second moment and are independent within each row. Bai and Yin's strong law for double arrays
says that the row averages of the top-left corners converge to the mean uniformly over the rows,
as long as the number of rows grows at most linearly in the row length: almost surely
`max_{i < r(n)} |ℓ(n)⁻¹ ∑_{j < ℓ(n)} ξᵢⱼ - E ξ| → 0` when `ℓ(n) → ∞` and `r(n) ≤ K ℓ(n)`.
Distinct rows may be dependent.

For the squared norms of the entries of a data array with finite fourth moment, this gives the
uniform behaviour of the squared row and column norms of the normalized `p(n) × n` corners
`Xₙ / √n` when `p(n) / n → y > 0`: almost surely they tend to `E‖x‖²` and to `y E‖x‖²`,
uniformly over the rows and over the columns. These are the degree bounds in Bai and Yin's
analysis of the smallest eigenvalue of the sample covariance matrix `Xₙ Xₙᴴ / n`.

The proof cuts the centred entries off at `n^(3/4)`. The centred truncations are bounded by
`2 n^(3/4)`, so Bernstein's inequality bounds each row sum by `ε n` outside an event of
probability `2 exp(-c n^(1/4))`, which stays summable after the union bound over the rows. Above
the cutoff, almost surely every row eventually has at most four entries
(`SampleCovariance.ae_eventually_forall_card_filter_lt_norm_lt`), each of size `o(n)`
(`SampleCovariance.ae_eventually_norm_le_mul`), and the mean removed by the truncation is at most
`E ξ² / n^(3/4)`. Bai and Yin prove their lemma for
general exponents with moment bounds on dyadic blocks instead.

## Main results

The results are filed under `TauCeti.Probability.SampleCovariance`, next to the other estimates
on the corners of data arrays.

* `SampleCovariance.ae_eventually_forall_abs_sum_div_sub_integral_le`: the uniform strong law for
  the rows of a double array.
* `SampleCovariance.ae_eventually_forall_abs_sum_norm_sq_div_sub_integral_le`: the squared row
  norms of the normalized corners tend to `E‖x‖²`, uniformly over the rows.
* `SampleCovariance.ae_eventually_forall_abs_sum_norm_sq_div_sub_mul_integral_le`: the squared
  column norms of the normalized corners tend to `y E‖x‖²`, uniformly over the columns.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294, Lemma 2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability.SampleCovariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section StrongLaw

variable {ξ : ℕ × ℕ → Ω → ℝ} {μ : Measure ℝ}

/-- Bernstein's inequality for one row of centred truncations at `n ^ (3 / 4)`: the row sum
reaches `ε n` with probability at most `2 exp(-c n^(1/4))`, where `c = ε² / (2 (E ξ² + ε))`. -/
private theorem measureReal_le_abs_sum_centeredTruncation_le (hξ : ∀ ij, HasLaw (ξ ij) μ P)
    (hrow : ∀ i, iIndepFun (fun j ↦ ξ (i, j)) P) (h2 : MemLp id 2 μ) {ε : ℝ} (hε : 0 < ε)
    (n i : ℕ) :
    P.real {ω | ε * n ≤
        |∑ j : Fin n, centeredTruncation id μ ((n : ℝ≥0) ^ (3 / 4 : ℝ)) (ξ (i, j) ω)|} ≤
      2 * exp (-(ε ^ 2 / (2 * ((∫ z, ‖z‖ ^ 2 ∂μ) + ε)) * (n : ℝ) ^ (1 / 4 : ℝ))) := by
  have : IsProbabilityMeasure P := (hrow 0).isProbabilityMeasure
  have : IsProbabilityMeasure μ := (hξ (0, 0)).isProbabilityMeasure_iff.1 this
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero, neg_zero,
      Real.exp_zero, mul_one]
    exact measureReal_le_one.trans one_le_two
  set σ := ∫ z, ‖z‖ ^ 2 ∂μ
  have hσ : 0 ≤ σ := integral_nonneg fun _ ↦ by positivity
  set g := centeredTruncation id μ ((n : ℝ≥0) ^ (3 / 4 : ℝ))
  have hg : Measurable g := measurable_id.centeredTruncation _
  have hb (z : ℝ) : |g z| ≤ 2 * (n : ℝ) ^ (3 / 4 : ℝ) := by
    simpa [g] using norm_centeredTruncation_le (X := id) (P := μ) ((n : ℝ≥0) ^ (3 / 4 : ℝ)) z
  have hsq (j : Fin n) : ∫ ω, g (ξ (i, j) ω) ^ 2 ∂P ≤ σ :=
    calc
      ∫ ω, g (ξ (i, j) ω) ^ 2 ∂P = ∫ z, ‖g z‖ ^ 2 ∂μ := by
        simpa only [Function.comp_apply, Real.norm_eq_abs, sq_abs] using
          (hξ (i, j)).integral_comp (f := fun z ↦ g z ^ 2) (hg.pow_const 2).aestronglyMeasurable
      _ ≤ σ := h2.integral_norm_centeredTruncation_sq_le _
  have hind : iIndepFun (fun (j : Fin n) ↦ g ∘ ξ (i, j)) P :=
    ((hrow i).precomp Fin.val_injective).comp (fun _ ↦ g) fun _ ↦ hg
  refine (hind.measureReal_abs_sum_ge_le_of_abs_le
    (s := Finset.univ) (fun j _ ↦ hg.comp_aemeasurable (hξ _).aemeasurable)
    (fun j _ ↦ ((hξ (i, j)).integral_comp hg.aestronglyMeasurable).trans
      (aestronglyMeasurable_id.integral_centeredTruncation _))
    (fun j _ ↦ .of_forall fun ω ↦ hb _) (by positivity)).trans ?_
  -- Write `n = t ^ 4` with `t = n ^ (1 / 4) ≥ 1`; the exponent is then at least `c t`.
  set t := (n : ℝ) ^ (1 / 4 : ℝ) with ht_def
  have ht : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hn4 : (n : ℝ) = t ^ 4 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg]
    norm_num
  have hn3 : (n : ℝ) ^ (3 / 4 : ℝ) = t ^ 3 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg]
    norm_num
  -- The variance proxy, written as Bernstein's inequality composes the truncation with `ξ`.
  set v := ∑ j : Fin n, ∫ ω, (g ∘ ξ (i, j)) ω ^ 2 ∂P
  have hv₀ : 0 ≤ v := Finset.sum_nonneg fun j _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have hv : t * v ≤ t ^ 8 * σ :=
    calc
      t * v ≤ t * (t ^ 4 * σ) := by
        refine mul_le_mul_of_nonneg_left ?_ (one_pos.trans_le ht).le
        refine (Finset.sum_le_card_nsmul _ _ σ fun j _ ↦ hsq j).trans_eq ?_
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn4]
      _ = t ^ 5 * σ := by ring
      _ ≤ t ^ 8 * σ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (by norm_num)) hσ
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) zero_le_two
  rw [neg_div, neg_le_neg_iff, hn3, hn4, div_mul_eq_mul_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg ε), pow_pos hε 3,
    mul_pos (pow_pos hε 3) (pow_pos (one_pos.trans_le ht) 8)]

/-- The centred truncations at `n ^ (3 / 4)` have row sums of size `o(n)`: almost surely,
eventually every row of the `p(n) × n` corner has `|∑ⱼ| < ε n`. The Bernstein bound
`2 exp(-c n^(1/4))` for each row stays summable after the union bound over `p(n) ≤ K n`
rows. -/
private theorem ae_eventually_forall_abs_sum_centeredTruncation_lt
    (hξ : ∀ ij, HasLaw (ξ ij) μ P) (hrow : ∀ i, iIndepFun (fun j ↦ ξ (i, j)) P)
    (h2 : MemLp id 2 μ) {p : ℕ → ℕ} {K : ℝ} (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i : Fin (p n),
      |∑ j : Fin n, centeredTruncation id μ ((n : ℝ≥0) ^ (3 / 4 : ℝ)) (ξ (i, j) ω)| < ε * n := by
  have : IsProbabilityMeasure P := (hrow 0).isProbabilityMeasure
  set c := ε ^ 2 / (2 * ((∫ z, ‖z‖ ^ 2 ∂μ) + ε))
  have hc : 0 < c := by positivity
  have hlim : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (12 : ℝ) *
      exp (-c * (n : ℝ) ^ (1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 12 c hc).comp
      ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
  -- After the union bound over the rows, the bound is eventually at most `2 K / n ^ 2`.
  have hbound : ∀ᶠ n in atTop, P {ω | ∃ i : Fin (p n), ε * n ≤
        |∑ j : Fin n, centeredTruncation id μ ((n : ℝ≥0) ^ (3 / 4 : ℝ)) (ξ (i, j) ω)|} ≤
      ENNReal.ofReal (2 * K * ((n : ℝ) ^ 2)⁻¹) := by
    filter_upwards [hp, eventually_gt_atTop 0, hlim.eventually (gt_mem_nhds one_pos)]
      with n hpn hn hexp
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    have hK : 0 ≤ K := (mul_nonneg_iff_of_pos_right hN).1 ((Nat.cast_nonneg _).trans hpn)
    set e := exp (-(c * (n : ℝ) ^ (1 / 4 : ℝ)))
    have he : (n : ℝ) * e ≤ ((n : ℝ) ^ 2)⁻¹ := by
      have h3 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (12 : ℝ) = (n : ℝ) ^ 3 := by
        rw [← Real.rpow_mul hN.le, ← Real.rpow_natCast]
        norm_num
      rw [h3, neg_mul] at hexp
      have hne : (n : ℝ) * e = (n : ℝ) ^ 3 * e * ((n : ℝ) ^ 2)⁻¹ := by field_simp
      rw [hne]
      exact mul_le_of_le_one_left (by positivity) hexp.le
    rw [ofPred_exists]
    refine (measure_iUnion_fintype_le P _).trans ?_
    calc
      _ ≤ ∑ _i : Fin (p n), ENNReal.ofReal (2 * e) := by
        gcongr with i
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal
          (measureReal_le_abs_sum_centeredTruncation_le hξ hrow h2 hε n i)
      _ = ENNReal.ofReal (p n * (2 * e)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc
          _ ≤ K * n * (2 * e) := by gcongr
          _ = 2 * K * (n * e) := by ring
          _ ≤ _ := by gcongr
  have hsum : ∑' n : ℕ, ENNReal.ofReal (2 * K * ((n : ℝ) ^ 2)⁻¹) < ∞ :=
    ((Real.summable_nat_pow_inv.2 one_lt_two).mul_left (2 * K)).tsum_ofReal_lt_top
  filter_upwards [TauCeti.MeasureTheory.ae_eventually_notMem_of_eventually_measure_le hsum hbound]
    with ω hω
  filter_upwards [hω] with n hn i
  simp only [not_exists, not_le] at hn
  exact hn i

/-- A row of reals splits at a cutoff `R` into its centred truncations, their common mean and its
entries above `R`. If the truncations sum to at most `a` in absolute value, the truncated mean is
at most `b`, and at most four entries exceed `R`, each at most `c`, then the row sums to at most
`a + n b + 4 c` in absolute value. -/
private theorem abs_sum_le_add_mul_add {n : ℕ} (z : Fin n → ℝ) (R : ℝ≥0)
    {a b c : ℝ} (ha : |∑ j, centeredTruncation id μ R (z j)| ≤ a)
    (hb : |∫ w, {w : ℝ | ‖id w‖ ≤ R}.indicator id w ∂μ| ≤ b)
    (hcard : (Finset.univ.filter fun j ↦ (R : ℝ) < ‖z j‖).card ≤ 4) (hc : ∀ j, |z j| ≤ c)
    (hc₀ : 0 ≤ c) :
    |∑ j, z j| ≤ a + n * b + 4 * c := by
  set m := ∫ w, {w : ℝ | ‖id w‖ ≤ R}.indicator id w ∂μ
  have hsplit (w : ℝ) :
      w = centeredTruncation id μ R w + m + {w : ℝ | (R : ℝ) < ‖w‖}.indicator id w := by
    by_cases hw : |w| ≤ R
    · simp [centeredTruncation_def, m, indicator_apply, hw, not_lt.2 hw]
    · simp [centeredTruncation_def, m, indicator_apply, hw, lt_of_not_ge hw]
  have hfilter : ∑ j, |{w : ℝ | (R : ℝ) < ‖w‖}.indicator id (z j)| =
      ∑ j ∈ Finset.univ.filter fun j ↦ (R : ℝ) < ‖z j‖,
        |{w : ℝ | (R : ℝ) < ‖w‖}.indicator id (z j)| := by
    refine (Finset.sum_filter_of_ne fun j _ h ↦ ?_).symm
    by_contra hj
    exact h (by rw [indicator_of_notMem (by exact hj), abs_zero])
  have htail : |∑ j, {w : ℝ | (R : ℝ) < ‖w‖}.indicator id (z j)| ≤ 4 * c := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (hfilter.trans_le ?_)
    refine (Finset.sum_le_card_nsmul _ _ c fun j _ ↦ ?_).trans ?_
    · refine le_trans ?_ (hc j)
      simpa only [Real.norm_eq_abs, id] using
        norm_indicator_le_norm_self (s := {w : ℝ | (R : ℝ) < ‖w‖}) id (z j)
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc₀
  calc
    |∑ j, z j| = |∑ j, centeredTruncation id μ R (z j) + n * m +
        ∑ j, {w : ℝ | (R : ℝ) < ‖w‖}.indicator id (z j)| := by
      rw [Finset.sum_congr rfl fun j _ ↦ hsplit (z j), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ ≤ a + n * b + 4 * c := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ha ?_)) htail)
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left hb n.cast_nonneg

/-- Bai and Yin's strong law for centred entries and rows of length `n`: almost surely, for every
`ε > 0`, eventually every row of the `p(n) × n` corner has `|∑ⱼ ξᵢⱼ| ≤ ε n`. -/
private theorem ae_eventually_forall_abs_sum_le_mul_of_integral_eq_zero
    (hξ : ∀ ij, HasLaw (ξ ij) μ P) (hrow : ∀ i, iIndepFun (fun j ↦ ξ (i, j)) P)
    (h2 : MemLp id 2 μ) (hmean : ∫ z, z ∂μ = 0) {p : ℕ → ℕ} {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ i : Fin (p n),
      |∑ j : Fin n, ξ (i, j) ω| ≤ ε * n := by
  let σ := ∫ z, ‖z‖ ^ 2 ∂μ
  -- Rows eventually have at most four entries above `n ^ (3 / 4)`.
  have hK : ∀ᶠ n in atTop, (p n : ℝ) ≤ max K 1 * n :=
    hp.mono fun n hn ↦ hn.trans (by gcongr; exact le_max_left _ _)
  have hn : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ max K 1 * n :=
    .of_forall fun n ↦ le_mul_of_one_le_left n.cast_nonneg (le_max_right _ _)
  have h2' := h2.integrable_norm_pow two_ne_zero
  have hcount := ae_eventually_forall_card_filter_lt_norm_lt (ℓ := fun n ↦ n) (a := 3 / 4)
    (q := 5) hξ hrow h2' hK hn (by norm_num)
  -- The truncated means at `R` are at most `σ / R`, which tends to zero along `R = n ^ (3 / 4)`.
  have hmean' (R : ℝ) (hR : 0 < R) :
      |∫ z, {z : ℝ | ‖id z‖ ≤ R}.indicator id z ∂μ| ≤ σ / R := by
    have h := MemLp.norm_integral_indicator_setOf_norm_le_le_of_integral_eq_zero (f := id)
      (k := 1) (by convert h2) hmean hR
    rw [Real.norm_eq_abs, pow_one] at h
    exact h
  have htrunc : Tendsto (fun n : ℕ ↦ σ / (n : ℝ) ^ (3 / 4 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
  have hbdd : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n in atTop, ∀ i : Fin (p n),
      |∑ j : Fin n, centeredTruncation id μ ((n : ℝ≥0) ^ (3 / 4 : ℝ)) (ξ (i, j) ω)| <
        1 / (k + 1) * n :=
    ae_all_iff.2 fun k ↦
      ae_eventually_forall_abs_sum_centeredTruncation_lt hξ hrow h2 hp (by positivity)
  filter_upwards [hcount, ae_eventually_norm_le_mul hξ h2' hp, hbdd]
    with ω hω₁ hω₂ hω₃ ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  filter_upwards [hω₁, hω₂ (ε / 12) (by positivity), hω₃ k,
    htrunc.eventually (ge_mem_nhds (show (0 : ℝ) < ε / 3 by positivity)),
    eventually_gt_atTop 0] with n hcn hmn hbn hσn hn₀ i
  have hR : (((n : ℝ≥0) ^ (3 / 4 : ℝ) : ℝ≥0) : ℝ) = (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [NNReal.coe_rpow, NNReal.coe_natCast]
  have hR₀ : (0 : ℝ) < (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hn₀) _
  refine (abs_sum_le_add_mul_add (fun j ↦ ξ (i, j) ω) ((n : ℝ≥0) ^ (3 / 4 : ℝ)) (hbn i).le
    (hR ▸ (hmean' _ hR₀).trans hσn) (hR ▸ Nat.le_of_lt_succ (hcn i))
    (fun j ↦ by simpa only [Real.norm_eq_abs] using hmn i j) (by positivity)).trans ?_
  calc
    1 / (k + 1) * n + n * (ε / 3) + 4 * (ε / 12 * n) ≤
        ε / 3 * n + n * (ε / 3) + 4 * (ε / 12 * n) := by gcongr
    _ = ε * n := by ring

/-- **Bai and Yin's strong law for double arrays.** Let the real array `ξ` have entries with a
common law `μ` of finite second moment, independent within each row, and let `ℓ(n) → ∞` and
`r(n) ≤ K ℓ(n)` eventually. Then almost surely, for every `ε > 0`, eventually every row of the
`r(n) × ℓ(n)` corner has its average within `ε` of the mean of `μ`. Distinct rows may be
dependent. -/
theorem ae_eventually_forall_abs_sum_div_sub_integral_le (hξ : ∀ ij, HasLaw (ξ ij) μ P)
    (hrow : ∀ i, iIndepFun (fun j ↦ ξ (i, j)) P) (h2 : MemLp id 2 μ) {r ℓ : ℕ → ℕ} {K : ℝ}
    (hℓ : Tendsto ℓ atTop atTop) (hr : ∀ᶠ n in atTop, (r n : ℝ) ≤ K * ℓ n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ i : Fin (r n),
      |(∑ j : Fin (ℓ n), ξ (i, j) ω) / ℓ n - ∫ z, z ∂μ| ≤ ε := by
  have : IsProbabilityMeasure P := (hrow 0).isProbabilityMeasure
  have : IsProbabilityMeasure μ := (hξ (0, 0)).isProbabilityMeasure_iff.1 this
  set a := ∫ z, z ∂μ
  -- Centre the entries.
  have hs : Measurable fun z : ℝ ↦ z - a := measurable_sub_const a
  have hζ (ij : ℕ × ℕ) : HasLaw (fun ω ↦ ξ ij ω - a) (μ.map fun z ↦ z - a) P :=
    (hasLaw_map hs.aemeasurable).fun_comp (hξ ij)
  have hζrow (i : ℕ) : iIndepFun (fun j ω ↦ ξ (i, j) ω - a) P :=
    (hrow i).comp (fun _ z ↦ z - a) fun _ ↦ hs
  have hζ2 : MemLp id 2 (μ.map fun z ↦ z - a) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hs.aemeasurable]
    exact h2.sub (memLp_const a)
  have hζmean : ∫ z, z ∂(μ.map fun z ↦ z - a) = 0 := by
    rw [integral_map hs.aemeasurable (by fun_prop),
      integral_sub (f := fun z ↦ z) (h2.integrable one_le_two) (integrable_const a)]
    simp [a]
  -- Rows of length `m` in a corner with `⌊|K| m⌋₊` rows.
  have hcan := ae_eventually_forall_abs_sum_le_mul_of_integral_eq_zero (p := fun m ↦ ⌊|K| * m⌋₊)
    (K := |K|) hζ hζrow hζ2 hζmean (.of_forall fun m ↦ Nat.floor_le (by positivity))
  filter_upwards [hcan] with ω hω ε hε
  filter_upwards [hℓ.eventually (hω ε hε), hr, hℓ.eventually (eventually_gt_atTop 0)]
    with n hn hrn hℓn i
  have hi : (i : ℕ) < ⌊|K| * ℓ n⌋₊ :=
    i.isLt.trans_le (Nat.le_floor (hrn.trans (by gcongr; exact le_abs_self K)))
  have hL : (0 : ℝ) < ℓ n := by exact_mod_cast hℓn
  have hsum : (∑ j : Fin (ℓ n), ξ (i, j) ω) / ℓ n - a =
      (∑ j : Fin (ℓ n), (ξ (i, j) ω - a)) / ℓ n := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [hsum, abs_div, Nat.abs_cast, div_le_iff₀ hL]
  exact hn ⟨i, hi⟩

end StrongLaw

section Norms

variable {E : Type*} [SeminormedAddGroup E] [MeasurableSpace E] {x : ℕ × ℕ → Ω → E}
  {ν : Measure E}

/-- **Squared row norms.** Let the array have entries with a common law `ν` of finite fourth
moment, independent within each row, and let `ℓ(n) → ∞` and `r(n) ≤ K ℓ(n)` eventually. Then
almost surely, for every `ε > 0`, eventually every row of the `r(n) × ℓ(n)` corner has mean
squared norm `ℓ(n)⁻¹ ∑ⱼ ‖xᵢⱼ‖²` within `ε` of `∫ ‖z‖ ^ 2 ∂ν`. For `ℓ(n) = n` these are the
squared row norms of the normalized corners `Xₙ / √n`. -/
theorem ae_eventually_forall_abs_sum_norm_sq_div_sub_integral_le (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P) (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν)
    {r ℓ : ℕ → ℕ} {K : ℝ} (hℓ : Tendsto ℓ atTop atTop) (hr : ∀ᶠ n in atTop, (r n : ℝ) ≤ K * ℓ n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ i : Fin (r n),
      |(∑ j : Fin (ℓ n), ‖x (i, j) ω‖ ^ 2) / ℓ n - ∫ z, ‖z‖ ^ 2 ∂ν| ≤ ε := by
  -- The squared norm is a.e. measurable as the square root of `‖·‖ ^ 4`.
  have hf : AEMeasurable (fun z : E ↦ ‖z‖ ^ 2) ν :=
    h4.aemeasurable.sqrt.congr (.of_forall fun z ↦ by
      dsimp only
      rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)])
  -- The squared norms have the law `ν.map (‖·‖ ^ 2)`, with finite second moment.
  have h2 : MemLp id 2 (ν.map fun z ↦ ‖z‖ ^ 2) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hf, Function.id_comp,
      memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
    simpa only [← pow_mul] using h4
  have hmean : ∫ z, z ∂(ν.map fun z ↦ ‖z‖ ^ 2) = ∫ z, ‖z‖ ^ 2 ∂ν :=
    integral_map hf (by fun_prop)
  rw [← hmean]
  exact ae_eventually_forall_abs_sum_div_sub_integral_le (ξ := fun ij ω ↦ ‖x ij ω‖ ^ 2)
    (fun ij ↦ (hasLaw_map hf).fun_comp (hx ij))
    (fun i ↦ (hrow i).comp₀ (fun _ z ↦ ‖z‖ ^ 2) (fun _ ↦ (hx _).aemeasurable) fun _ ↦ by
      rwa [(hx _).map_eq]) h2 hℓ hr

/-- **Squared column norms of the corners.** Let the array have entries with a common law `ν` of
finite fourth moment, independent within each column, and let `p(n) / n → y > 0`. Then almost
surely, for every `ε > 0`, eventually every column of the normalized `p(n) × n` corner `Xₙ / √n`
has squared norm `n⁻¹ ∑ᵢ ‖xᵢⱼ‖²` within `ε` of `y ∫ ‖z‖ ^ 2 ∂ν`. -/
theorem ae_eventually_forall_abs_sum_norm_sq_div_sub_mul_integral_le
    (hx : ∀ ij, HasLaw (x ij) ν P) (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P)
    (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν) {p : ℕ → ℕ} {y : ℝ} (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y)) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ j : Fin n,
      |(∑ i : Fin (p n), ‖x (i, j) ω‖ ^ 2) / n - y * ∫ z, ‖z‖ ^ 2 ∂ν| ≤ ε := by
  set m := ∫ z, ‖z‖ ^ 2 ∂ν
  -- Eventually `p(n) ≥ y n / 2`, so the columns are the rows of a corner of the transpose.
  have hhalf : ∀ᶠ n : ℕ in atTop, y / 2 * n ≤ p n := by
    filter_upwards [hp.eventually (le_mem_nhds (half_lt_self hy)), eventually_gt_atTop 0]
      with n hn hn₀
    exact (le_div_iff₀ (by exact_mod_cast hn₀)).1 hn
  have hpℓ : Tendsto p atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono' atTop hhalf ?_)
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hy)
  have hnp : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ 2 / y * p n :=
    hhalf.mono fun n hn ↦ by
      rw [div_mul_eq_mul_div, le_div_iff₀ hy]
      linarith
  have hrows := ae_eventually_forall_abs_sum_norm_sq_div_sub_integral_le (r := fun n ↦ n)
    (x := fun ij ↦ x ij.swap) (fun _ ↦ hx _) hcol h4 hpℓ hnp
  filter_upwards [hrows] with ω hω ε hε
  -- Rescale the column averages by `p(n) / n → y`.
  set δ := min 1 (ε / (2 * y))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hη : 0 < ε / (2 * (|m| + 1)) := by positivity
  filter_upwards [hω δ hδ, Metric.tendsto_nhds.1 hp _ hη, hpℓ.eventually (eventually_gt_atTop 0)]
    with n hn hpn hp₀ j
  set A := (∑ i : Fin (p n), ‖x (i, j) ω‖ ^ 2) / p n
  have hA : |A - m| ≤ δ := hn j
  have hAbs : |A| ≤ |m| + 1 := by
    have := abs_sub_abs_le_abs_sub A m
    linarith [min_le_left 1 (ε / (2 * y))]
  have hsplit : (∑ i : Fin (p n), ‖x (i, j) ω‖ ^ 2) / n - y * m =
      ((p n : ℝ) / n - y) * A + y * (A - m) := by
    have : (p n : ℝ) ≠ 0 := by exact_mod_cast hp₀.ne'
    simp only [A]
    field_simp
    ring
  rw [hsplit]
  calc
    _ ≤ |(p n : ℝ) / n - y| * |A| + y * |A - m| := by
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_mul, abs_mul, abs_of_pos hy]
    _ ≤ ε / (2 * (|m| + 1)) * (|m| + 1) + y * (ε / (2 * y)) := by
      gcongr
      · exact (Real.dist_eq _ _ ▸ hpn).le
      · exact hA.trans (min_le_right _ _)
    _ = ε := by field_simp; ring

end Norms

end TauCeti.Probability.SampleCovariance
