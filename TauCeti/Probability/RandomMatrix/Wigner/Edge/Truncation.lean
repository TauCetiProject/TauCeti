/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Probability.RandomMatrix.Wigner.CornerAverage
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Probability.Moments.MaximalEntry
import TauCeti.Probability.Moments.Chebyshev
import TauCeti.Probability.RandomMatrix.Centering
import TauCeti.Analysis.Matrix.HardThreshold
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Cast

/-!
# Operator-norm truncation of Wigner corners

A finite fourth moment makes the largest normalized off-diagonal entry tend to zero
almost surely. Above a cutoff of order `n^a` in the unnormalized matrix, with
`5/12 < a`, the discarded entries eventually have degree at most two in every row.
Thus their operator norm vanishes. The mean subtracted in recentering also contributes
a vanishing operator norm, and the real diagonal can be removed under its finite
second moment. For `a < 1/2` the retained normalized entries are polynomially small,
as needed for growing trace moments.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), Theorems 2.3.23–2.3.24.
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.12.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix ProbabilityTheory Set
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {X : Ω → ℂ}

/-- The largest absolute entry of the zero-diagonal normalized Wigner corners vanishes
almost surely under a common finite fourth moment. Independence is unnecessary. -/
theorem ae_eventually_norm_wignerMatrix_zero_apply_le [IsProbabilityMeasure P]
    (hid : ∀ ij, IdentDistrib (ξ ij) X P P) (hX : MemLp X 4 P) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin (n + 1), ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖ ≤ ε := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hm : ∀ᶠ n : ℕ in atTop, ((n + 1).choose 2 : ℝ) ≤ Real.sqrt (n + 1 : ℕ) ^ 4 :=
    .of_forall fun n ↦ by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _),
        Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib
    (fun k ↦ hid (strictUpperEquivNat.symm k)) hX hs hm] with ω hω
  intro ε hε
  filter_upwards [hω ε hε] with n hn i j
  have hscale (ij : StrictUpper) (hij : ij.val.2 < n + 1) :
      (Real.sqrt (n + 1 : ℕ))⁻¹ * ‖ξ ij ω‖ ≤ ε := by
    have h := hn _ ((strictUpperEquivNat_lt_choose_iff ij _).2 hij)
    rw [Equiv.symm_apply_apply] at h
    rw [inv_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.2 (by positivity)), mul_comm]
    simpa only [mul_comm ε] using h
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · simpa only [wignerMatrix_apply_of_lt _ _ _ hij, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hscale ⟨(i.val, j.val), hij⟩ j.isLt
  · obtain rfl := Fin.ext hij
    simpa using hε.le
  · simpa only [wignerMatrix_apply_of_gt _ _ _ hij, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_star] using
      hscale ⟨(j.val, i.val), hij⟩ i.isLt

/-- Removing the diagonal changes the normalized operator norm by a quantity tending
to zero almost surely under a common finite second moment. -/
theorem ae_tendsto_norm_wignerMatrix_sub_zero_diagonal [IsProbabilityMeasure P]
    (hid : ∀ i, IdentDistrib (η i) (η 0) P P) (hη : MemLp (η 0) 2 P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hm : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) ≤ Real.sqrt (n + 1 : ℕ) ^ 2 :=
    .of_forall fun n ↦ (Real.sq_sqrt (Nat.cast_nonneg (n + 1))).ge
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib hid
    hη hs hm] with ω hω
  refine Metric.tendsto_atTop.2 fun ε hε ↦ eventually_atTop.1 ?_
  filter_upwards [hω (ε / 2) (half_pos hε)] with n hn
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _),
    wignerMatrix_eq_add_diagonal ξ η, add_sub_cancel_left, l2_opNorm_diagonal]
  refine ((pi_norm_le_iff_of_nonneg (half_pos hε).le).2 fun i ↦ ?_).trans_lt (half_lt_self hε)
  rw [Complex.norm_real, norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
  exact hn _ i.isLt

private theorem measure_norm_wignerMatrix_zero_apply_gt {n : ℕ}
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P P)
    {i j : Fin n} (hij : i ≠ j) (R : ℝ) :
    P {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖} =
      P {ω | R < ‖X ω‖} := by
  have hn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt i.isLt))
  have hcancel (x : ℂ) : R / Real.sqrt n < (Real.sqrt n)⁻¹ * ‖x‖ ↔ R < ‖x‖ := by
    rw [inv_mul_eq_div, div_lt_div_iff_of_pos_right hn]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hn.le, hcancel]
    exact ((hid ⟨(i.val, j.val), h⟩ j.isLt).comp measurable_norm).measure_mem_eq measurableSet_Ioi
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hn.le, norm_star, hcancel]
    exact ((hid ⟨(j.val, i.val), h⟩ i.isLt).comp measurable_norm).measure_mem_eq measurableSet_Ioi

private theorem measure_three_large_wigner_entries {n : ℕ}
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P P)
    (i : Fin n) (j : Fin 3 → Fin n) (hinj : Function.Injective j)
    (hne : ∀ k, i ≠ j k) (R : ℝ) :
    P (⋂ k, {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i (j k)‖}) =
      P {ω | R < ‖X ω‖} ^ 3 := by
  have hedge : Function.Injective (fun k ↦ s(i, j k)) := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hinj h.2
    · exact (hne b h.1).elim
  have hind' := iIndepFun_wignerMatrix_apply_of_ne (η := fun _ _ ↦ 0)
    (fun _ ↦ i) j hne hedge hind
  calc
    _ = ∏ k, P {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i (j k)‖} :=
      hind'.meas_iInter (fun _ ↦ ⟨{z : ℂ | R / Real.sqrt n < ‖z‖},
        measurableSet_lt measurable_const measurable_norm, rfl⟩)
    _ = _ := by
      simp only [measure_norm_wignerMatrix_zero_apply_gt hid (hne _), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

/-- The probability that some row has at least three entries above the normalized cutoff
is at most `n^4` times the cube of the common unnormalized tail probability. -/
theorem measure_exists_three_large_wigner_entries_le {n : ℕ}
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P P)
    {R : ℝ} (hR : 0 ≤ R) :
    P {ω | ∃ i : Fin n, 2 < (Finset.univ.filter fun j ↦
      R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖).card} ≤
        (n : ℝ≥0∞) ^ 4 * P {ω | R < ‖X ω‖} ^ 3 := by
  classical
  let E (p : Fin n × (Fin 3 → Fin n)) : Set Ω :=
    if Function.Injective p.2 ∧ ∀ k, p.1 ≠ p.2 k then
      ⋂ k, {ω | R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω p.1 (p.2 k)‖}
    else ∅
  have hcover : {ω | ∃ i : Fin n, 2 < (Finset.univ.filter fun j ↦
      R / Real.sqrt n < ‖wignerMatrix ξ (fun _ _ ↦ 0) n ω i j‖).card} ⊆ ⋃ p, E p := by
    rintro ω ⟨i, hi⟩
    obtain ⟨t, hsub, hcard⟩ := Finset.exists_subset_card_eq hi
    let e := (Fintype.equivFinOfCardEq (Fintype.card_coe t ▸ hcard)).symm
    let j : Fin 3 → Fin n := Subtype.val ∘ e
    have hj (k) := (Finset.mem_filter.1 (hsub (e k).property)).2
    have hne (k) : i ≠ j k := by
      intro h
      have hk := hj k
      rw [show (e k).val = j k from rfl, ← h] at hk
      simp only [wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, norm_zero] at hk
      exact (not_lt_of_ge (div_nonneg hR (Real.sqrt_nonneg _))) hk
    have hv : Function.Injective j ∧ ∀ k, i ≠ j k := ⟨Subtype.val_injective.comp e.injective, hne⟩
    exact mem_iUnion.2 ⟨(i, j), by
      simpa only [E, ite_eq_left hv, mem_iInter, mem_ofPred_eq, j, Function.comp_apply] using hj⟩
  calc
    _ ≤ ∑ p, P (E p) := (measure_mono hcover).trans (measure_iUnion_fintype_le P E)
    _ ≤ ∑ _p : Fin n × (Fin 3 → Fin n), P {ω | R < ‖X ω‖} ^ 3 := by
      refine Finset.sum_le_sum fun p _ ↦ ?_
      dsimp only [E]
      split_ifs with h
      · exact (measure_three_large_wigner_entries hind hid p.1 p.2 h.1 h.2 _).le
      · rw [measure_empty]
        exact bot_le
    _ = _ := by simp [pow_succ, mul_comm, mul_assoc]

private theorem measure_exists_three_large_wigner_entries_rpow_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 4 P) (a : ℝ) (n : ℕ) :
    P {ω | ∃ i : Fin (n + 1), 2 < (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card} ≤
      ENNReal.ofReal ((∫ ω, ‖X ω‖ ^ 4 ∂P) ^ 3 * ((n + 1 : ℕ) : ℝ) ^ (4 - 12 * a)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let C : ℝ := ∫ ω, ‖X ω‖ ^ 4 ∂P
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ by positivity
  let N : ℝ := (n + 1 : ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hr : 0 < N ^ a := Real.rpow_pos_of_pos hN _
  have htail : P {ω | N ^ a < ‖X ω‖} ≤ ENNReal.ofReal (C / (N ^ a) ^ 4) := by
    have hsq : Integrable (fun ω ↦ ‖(‖X ω‖ ^ 2 : ℝ)‖ ^ 2) P := by
      simpa only [Real.norm_of_nonneg (sq_nonneg _), ← pow_mul] using
        (hX.integrable_norm_pow (by decide))
    have hsub : {ω | N ^ a < ‖X ω‖} ⊆ {ω | (N ^ a) ^ 2 ≤ ‖(‖X ω‖ ^ 2 : ℝ)‖} := by
      intro ω hω
      simp only [mem_ofPred_eq, Real.norm_of_nonneg (sq_nonneg _)] at hω ⊢
      exact pow_le_pow_left₀ hr.le hω.le _
    refine (measure_mono hsub).trans ?_
    simpa only [Real.norm_of_nonneg (sq_nonneg _), ← pow_mul, C] using
      meas_ge_le_integral_norm_sq_div_sq hsq (sq_pos_of_pos hr)
  have hpow : N ^ 4 * (C / (N ^ a) ^ 4) ^ 3 = C ^ 3 * N ^ (4 - 12 * a) := by
    rw [div_pow, ← pow_mul, ← Real.rpow_mul_natCast hN.le, mul_div_left_comm,
      ← Real.rpow_natCast N 4, ← Real.rpow_sub hN]
    congr 2
    norm_num
    ring
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ 4 * P {ω | N ^ a < ‖X ω‖} ^ 3 :=
      measure_exists_three_large_wigner_entries_le (hind.precomp Subtype.val_injective)
        (fun ij _ ↦ hid ij) hr.le
    _ ≤ ENNReal.ofReal (N ^ 4 * (C / (N ^ a) ^ 4) ^ 3) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_pow (div_nonneg hC (by positivity))]
      gcongr
    _ = _ := congrArg ENNReal.ofReal hpow

private theorem ae_eventually_card_large_wigner_entries_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 4 P) {a : ℝ} (ha : 5 / 12 < a) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (n + 1), (Finset.univ.filter fun j ↦
      ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
        ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card ≤ 2 := by
  let C : ℝ := ∫ ω, ‖X ω‖ ^ 4 ∂P
  let E (n : ℕ) := {ω | ∃ i : Fin (n + 1), 2 < (Finset.univ.filter fun j ↦
    ((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ) <
      ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖).card}
  let b (n : ℕ) := C ^ 3 * ((n + 1 : ℕ) : ℝ) ^ (4 - 12 * a)
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ (4 - 12 * a)) :=
    (Real.summable_nat_rpow (p := 4 - 12 * a)).2 (by linarith)
  have hb : Summable b := ((summable_nat_add_iff 1).2 hsum).mul_left (C ^ 3)
  have hbound (n : ℕ) : P (E n) ≤ ENNReal.ofReal (b n) := by
    exact measure_exists_three_large_wigner_entries_rpow_le hind hid hX a n
  have hfinite : (∑' n, P (E n)) < ∞ := (tsum_le_tsum hbound).trans_lt hb.tsum_ofReal_lt_top
  exact (ae_eventually_notMem hfinite.ne).mono fun ω hω ↦
    hω.mono fun n hn i ↦ le_of_not_gt fun hi ↦ hn ⟨i, hi⟩

omit [MeasurableSpace Ω] in
private theorem wignerMatrix_sub_indicator_eq_hardThreshold {n : ℕ} (hn : 0 < n)
    (r : ℝ≥0) (ω : Ω) :
    wignerMatrix ξ (fun _ _ ↦ 0) n ω -
      wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ r}.indicator (ξ ij)) (fun _ _ ↦ 0) n ω =
    (wignerMatrix ξ (fun _ _ ↦ 0) n ω).hardThreshold (r / Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have ht (x : ℂ) :
      (r : ℝ) / Real.sqrt n < (Real.sqrt n)⁻¹ * ‖x‖ ↔ (r : ℝ) < ‖x‖ := by
    rw [inv_mul_eq_div, div_lt_div_iff_of_pos_right hs]
  ext i j
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · simp only [Matrix.sub_apply, Matrix.hardThreshold_apply, wignerMatrix_apply_of_lt _ _ _ hij,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le, ht, indicator,
      mem_ofPred_eq]
    by_cases h : ‖ξ ⟨(i.val, j.val), hij⟩ ω‖ ≤ r
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  · obtain rfl := Fin.ext hij
    simp
  · simp only [Matrix.sub_apply, Matrix.hardThreshold_apply, wignerMatrix_apply_of_gt _ _ _ hij,
      norm_mul, norm_inv, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le, ht,
      indicator, mem_ofPred_eq]
    by_cases h : ‖ξ ⟨(j.val, i.val), hij⟩ ω‖ ≤ r
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]

omit [MeasurableSpace Ω] in
private theorem norm_hermitianOffDiagonal_inv_sqrt_smul_le {n : ℕ} (hn : 0 < n) (c : ℂ) :
    ‖hermitianOffDiagonal ((Real.sqrt n)⁻¹ • c) n‖ ≤ Real.sqrt n * ‖c‖ := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  apply (isHermitian_hermitianOffDiagonal _ _).l2_opNorm_le_of_row_sum_le (by positivity)
  intro i
  calc
    _ ≤ ∑ _j : Fin n, ‖(Real.sqrt n)⁻¹ • c‖ :=
      Finset.sum_le_sum fun j _ ↦ norm_hermitianOffDiagonal_apply_le _ _ i j
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc]
      congr 1
      exact (mul_inv_eq_iff_eq_mul₀ hs.ne').2 (by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)])

private theorem ae_tendsto_norm_wignerMatrix_hardThreshold
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 4 P) {a : ℝ} (ha : 5 / 12 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).hardThreshold
      (((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ))‖) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  filter_upwards [ae_eventually_card_large_wigner_entries_le hind hid hX ha,
    ae_eventually_norm_wignerMatrix_zero_apply_le hid hX] with ω hsparse hmax
  apply tendsto_order.2
  refine ⟨fun r hr ↦ .of_forall fun n ↦ hr.trans_le (norm_nonneg _), fun r hr ↦ ?_⟩
  filter_upwards [hsparse, hmax (r / 3) (by positivity)] with n hn hentry
  let A := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  let t := (((n + 1 : ℕ) : ℝ) ^ a / Real.sqrt (n + 1 : ℕ))
  refine ((wignerMatrix_isHermitian _ _ ω _).hardThreshold t |>.l2_opNorm_le_of_row_sum_le
    (r := 2 * (r / 3)) (by positivity) fun i ↦ ?_).trans_lt (by linarith)
  have hsum : (∑ j, ‖A.hardThreshold t i j‖) ≤
      ∑ j ∈ Finset.univ.filter (fun j ↦ t < ‖A i j‖), r / 3 := by
    simp_rw [Matrix.hardThreshold_apply, apply_ite norm, norm_zero, ← Finset.sum_filter]
    exact Finset.sum_le_sum fun j _ ↦ hentry i j
  refine hsum.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn i) (by positivity)

private theorem tendsto_wigner_truncation_mean (hX : MemLp X 4 P) [IsFiniteMeasure P]
    (hmean : ∫ ω, X ω ∂P = 0) {a : ℝ} (ha : 5 / 12 < a) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ) *
      ‖∫ ω, {ω' | ‖X ω'‖ ≤ ((n + 1 : ℕ) : ℝ) ^ a}.indicator X ω ∂P‖) atTop (𝓝 0) := by
  let C := ∫ ω, ‖X ω‖ ^ 4 ∂P
  have hlim : Tendsto (fun n : ℕ ↦ C * ((n + 1 : ℕ) : ℝ) ^ (1 / 2 - 3 * a)) atTop (𝓝 0) :=
    by
      simpa only [mul_zero, neg_sub, Function.comp_apply] using
        ((tendsto_rpow_neg_atTop (by linarith : 0 < 3 * a - 1 / 2)).comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_mul C
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hlim
  let N : ℝ := (n + 1 : ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  calc
    _ ≤ Real.sqrt N * (C / (N ^ a) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (hX.norm_integral_indicator_norm_le_of_integral_eq_zero hmean (Real.rpow_pos_of_pos hN _))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hN.le, mul_div_left_comm, ← Real.rpow_sub hN]
      congr 2
      norm_num
      ring

/-- The original Wigner corners and their zero-diagonal centered truncations at radius
`n^a` differ by a vanishing operator norm almost surely. Only the upper coordinates
need to be independent, and no independence between the diagonal and upper coordinates
is needed. -/
theorem ae_tendsto_norm_wignerMatrix_sub_centeredTruncation
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P P) (hX : MemLp X 4 P)
    (hmean : ∫ ω, X ω ∂P = 0) (hd : ∀ i, IdentDistrib (η i) (η 0) P P) (hη : MemLp (η 0) 2 P)
    {a : ℝ} (ha : 5 / 12 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω‖) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  filter_upwards [ae_tendsto_norm_wignerMatrix_hardThreshold hind hid hX ha,
    ae_tendsto_norm_wignerMatrix_sub_zero_diagonal (ξ := ξ) hd hη] with ω htail hdiag
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa only [add_zero] using
      ((hdiag.add htail).add (tendsto_wigner_truncation_mean hX hmean ha)))
  let R : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩
  let Z := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  let T := wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) (n + 1) ω
  let B := wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) (fun _ _ ↦ 0) (n + 1) ω
  let c := ∫ ω', {ω'' | ‖X ω''‖ ≤ R}.indicator X ω' ∂P
  have hTB : T - B = hermitianOffDiagonal ((Real.sqrt (n + 1 : ℕ))⁻¹ • c) (n + 1) := by
    have hcenter : (fun ij ω' ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij) ω' - c) =
        (fun ij ↦ centeredTruncation (ξ ij) P R) := by
      funext ij
      rw [centeredTruncation_def, (hid ij).integral_indicator_setOf_norm_le_eq]
    have h : T = wignerMatrix (fun ij ω' ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij) ω' - c)
        (fun _ _ ↦ 0) (n + 1) ω + hermitianOffDiagonal ((Real.sqrt (n + 1 : ℕ))⁻¹ • c) (n + 1) :=
      wignerMatrix_eq_center_add_hermitianOffDiagonal
        (fun ij ↦ {x | ‖ξ ij x‖ ≤ R}.indicator (ξ ij)) (fun _ _ ↦ 0) c (n + 1) ω
    rw [hcenter] at h
    exact sub_eq_iff_eq_add.2 (h.trans (add_comm _ _))
  have hZT := wignerMatrix_sub_indicator_eq_hardThreshold (ξ := ξ) (Nat.succ_pos n) R ω
  calc
    _ ≤ ‖wignerMatrix ξ η (n + 1) ω - Z‖ + ‖Z - T‖ + ‖T - B‖ := by
      exact (norm_sub_le_norm_sub_add_norm_sub _ T _).trans
        (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ Z _) _)
    _ ≤ _ := by
      have h1 : ‖Z - T‖ = ‖Z.hardThreshold ((R : ℝ) / Real.sqrt (n + 1 : ℕ))‖ :=
        congrArg norm hZT
      have h2 : ‖T - B‖ ≤ Real.sqrt (n + 1 : ℕ) * ‖c‖ := by
        rw [hTB]
        exact norm_hermitianOffDiagonal_inv_sqrt_smul_le (Nat.succ_pos n) c
      exact add_le_add (add_le_add_right h1.le _) h2

/-- For a centered truncated Wigner corner, the absolute entry moment of order
`k+2` is bounded by the original second moment divided by the dimension, times
the `k`-th power of the normalized cutoff bound. This estimate is uniform over
the corner and allows the order to grow with the dimension. -/
theorem integral_norm_wignerMatrix_centeredTruncation_apply_pow_le
    [IsProbabilityMeasure P] (hid : ∀ ij, IdentDistrib (ξ ij) X P P)
    (hX : MemLp X 2 P) (R : ℝ≥0) {n : ℕ} (i j : Fin n) (k : ℕ) :
    ∫ ω, ‖wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R)
      (fun _ _ ↦ 0) n ω i j‖ ^ (k + 2) ∂P ≤
      (2 * (R : ℝ) / Real.sqrt n) ^ k * ((∫ ω, ‖X ω‖ ^ 2 ∂P) / n) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.zero_lt_of_lt i.isLt)
  have hs := Real.sqrt_pos.2 hn
  have hmoment (ij : StrictUpper) :
      (∫ ω, ((Real.sqrt n)⁻¹ * ‖centeredTruncation (ξ ij) P R ω‖) ^ (k + 2) ∂P) ≤
        (2 * (R : ℝ) / Real.sqrt n) ^ k * ((∫ ω, ‖X ω‖ ^ 2 ∂P) / n) := by
    have h0 := ((hid ij).symm.memLp_snd hX).integral_norm_centeredTruncation_pow_le R k
    have hid₂ : (∫ ω, ‖ξ ij ω‖ ^ 2 ∂P) = ∫ ω, ‖X ω‖ ^ 2 ∂P :=
      ((hid ij).comp (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2))).integral_eq
    rw [hid₂] at h0
    simp_rw [mul_pow]
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left h0 (by positivity)).trans_eq ?_
    rw [pow_add, inv_pow, inv_pow, Real.sq_sqrt hn.le, div_pow]
    ring
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · simpa only [wignerMatrix_apply_of_lt _ _ _ hij, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hs.le] using hmoment ⟨(i.val, j.val), hij⟩
  · obtain rfl := Fin.ext hij
    simp only [wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, norm_zero,
      zero_pow (Nat.succ_ne_zero (k + 1)), integral_zero]
    exact mul_nonneg (by positivity) (div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) hn.le)
  · simpa only [wignerMatrix_apply_of_gt _ _ _ hij, norm_mul, norm_inv, norm_star,
      Complex.norm_real, Real.norm_of_nonneg hs.le] using hmoment ⟨(j.val, i.val), hij⟩

end TauCeti.Probability
