/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.Complex.Polynomial.Fejer
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# Fejér's disc-algebra power series diverging at `1`

Superposing disjointly shifted Fejér polynomials (`TauCeti.fejerPoly`) with geometric weights
`(1 / 2) ^ k` and rapidly growing degrees `m_k = 2 ^ ((k + 1) * 2 ^ k)` produces a function `P`
in the disc algebra (continuous on `closedBall 0 1`, holomorphic on `ball 0 1`) whose Taylor
coefficients `c : ℕ → ℝ` satisfy `|c n| ≤ 1` and `c n → 0`, while the partial sums
`∑ n ∈ range N, c n` at `w = 1` are unbounded above
(`TauCeti.exists_continuousOn_closedBall_hasSum_unbounded_sum_range`).

## Main declarations

* `TauCeti.exists_continuousOn_closedBall_hasSum_unbounded_sum_range`: Fejér's disc-algebra power
  series with real coefficients tending to `0` and unbounded partial sums at `1`.

## References

* L. Fejér, *Sur les singularités de la série de Fourier des fonctions continues*, Ann. Sci.
  École Norm. Sup. (3) 28 (1911), 63–104.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Ch. II, §2.
* A. Zygmund, *Trigonometric Series*, 3rd ed., Vol. I, Ch. VIII, §1.
-/

public section

open Filter Finset Metric Complex
open scoped Topology Real

namespace TauCeti

/-- Rapidly growing degree schedule `2 ^ ((k + 1) * 2 ^ k)` chosen so that
`(2⁻¹) ^ k * harmonic (fejerDeg k) ≥ (k + 1) * log 2 → ∞`. -/
private def fejerDeg (k : ℕ) : ℕ :=
  2 ^ ((k + 1) * 2 ^ k)

/-- Starting index of the `k`-th disjoint Fejér block of length `2 * fejerDeg k + 1`. -/
private def fejerStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => fejerStart k + (2 * fejerDeg k + 1)

private theorem fejerStart_strictMono : StrictMono fejerStart :=
  strictMono_nat_of_lt_succ fun k ↦ by
    simp only [fejerStart]
    omega

/-- Block index `k` of `n` in Fejér's superposed series: the unique `k` with
`fejerStart k ≤ n < fejerStart (k + 1)`. -/
private def fejerBlock (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k ↦ fejerStart k ≤ n) n

private theorem fejerBlock_eq_of_mem_Ico {k n : ℕ}
    (h1 : fejerStart k ≤ n) (h2 : n < fejerStart (k + 1)) :
    fejerBlock n = k := by
  rw [fejerBlock, Nat.findGreatest_eq_iff]
  refine ⟨(fejerStart_strictMono.id_le k).trans h1, fun _ ↦ h1, fun j hkj _ hj ↦ ?_⟩
  have : fejerStart (k + 1) ≤ fejerStart j :=
    fejerStart_strictMono.monotone (Nat.succ_le_of_lt hkj)
  omega

private theorem tendsto_fejerBlock_atTop : Tendsto fejerBlock atTop atTop :=
  tendsto_atTop.mpr fun K ↦ eventually_atTop.mpr
    ⟨fejerStart K, fun _ hn ↦ Nat.le_findGreatest ((fejerStart_strictMono.id_le K).trans hn) hn⟩

/-- The `n`-th Taylor coefficient of Fejér's superposed series: on the unique block
`[fejerStart k, fejerStart (k + 1))` containing `n`, it equals
`(2⁻¹) ^ k * fejerPolyCoeff (fejerDeg k) (n - fejerStart k)`. -/
private noncomputable def fejerSeriesCoeff (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ fejerBlock n *
    fejerPolyCoeff (fejerDeg (fejerBlock n)) (n - fejerStart (fejerBlock n))

private theorem fejerSeriesCoeff_eq_of_mem_Ico {k n : ℕ}
    (h1 : fejerStart k ≤ n) (h2 : n < fejerStart (k + 1)) :
    fejerSeriesCoeff n = (2 : ℝ)⁻¹ ^ k * fejerPolyCoeff (fejerDeg k) (n - fejerStart k) := by
  simp only [fejerSeriesCoeff, fejerBlock_eq_of_mem_Ico h1 h2]

private theorem abs_fejerSeriesCoeff_le_one (n : ℕ) : |fejerSeriesCoeff n| ≤ 1 := by
  rw [fejerSeriesCoeff, abs_mul, abs_of_nonneg (by positivity)]
  have hpow : (2 : ℝ)⁻¹ ^ fejerBlock n ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  exact (mul_le_mul hpow (abs_fejerPolyCoeff_le_one _ _) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

private theorem tendsto_fejerSeriesCoeff_zero :
    Tendsto fejerSeriesCoeff atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n ↦ ?_)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (2 : ℝ)⁻¹ < 1)).comp
      tendsto_fejerBlock_atTop)
  rw [Real.norm_eq_abs, fejerSeriesCoeff, abs_mul, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (abs_fejerPolyCoeff_le_one _ _) (by positivity)).trans_eq
    (mul_one _)

private theorem sum_Ico_fejerStart_add_mul {α : Type*} [CommSemiring α] [Algebra ℝ α]
    (k L : ℕ) (hL : L ≤ 2 * fejerDeg k + 1) (g : ℕ → α) :
    ∑ n ∈ Ico (fejerStart k) (fejerStart k + L), algebraMap ℝ α (fejerSeriesCoeff n) * g n =
      algebraMap ℝ α ((2 : ℝ)⁻¹ ^ k) *
        ∑ r ∈ range L, algebraMap ℝ α (fejerPolyCoeff (fejerDeg k) r) * g (fejerStart k + r) := by
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  have hr' : r < L := mem_range.mp hr
  have h1 : fejerStart k ≤ fejerStart k + r := Nat.le_add_right _ _
  have h2 : fejerStart k + r < fejerStart (k + 1) := by
    simp only [fejerStart]
    omega
  rw [fejerSeriesCoeff_eq_of_mem_Ico h1 h2, Nat.add_sub_cancel_left, map_mul, mul_assoc]

private theorem sum_Ico_fejerSeriesCoeff_mul_pow (k : ℕ) (w : ℂ) :
    ∑ n ∈ Ico (fejerStart k) (fejerStart (k + 1)), (fejerSeriesCoeff n : ℂ) * w ^ n =
      ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w := by
  have h := sum_Ico_fejerStart_add_mul (α := ℂ) k (2 * fejerDeg k + 1) le_rfl (fun n ↦ w ^ n)
  simp only [Complex.coe_algebraMap, ofReal_pow] at h
  rw [fejerStart, h, fejerPoly_eq_sum_range, mul_assoc]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [pow_add]
  ring

private theorem sum_range_fejerStart_mul_pow (K : ℕ) (w : ℂ) :
    ∑ n ∈ range (fejerStart K), (fejerSeriesCoeff n : ℂ) * w ^ n =
      ∑ k ∈ range K, ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w := by
  set F : ℕ → ℂ := fun k ↦ ∑ n ∈ range (fejerStart k), (fejerSeriesCoeff n : ℂ) * w ^ n
  have hblock (k : ℕ) :
      ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w = F (k + 1) - F k := by
    rw [← sum_Ico_fejerSeriesCoeff_mul_pow,
      Finset.sum_Ico_eq_sub _ (fejerStart_strictMono (Nat.lt_succ_self k)).le]
  simp_rw [hblock, sum_range_sub]
  simp [F, fejerStart]

private theorem sum_range_fejerStart_add_fejerDeg (K : ℕ) :
    ((K + 1 : ℝ) * Real.log 2) ≤ ∑ n ∈ range (fejerStart K + fejerDeg K), fejerSeriesCoeff n := by
  -- The preceding complete blocks sum to `0`.
  have hprev : ∑ n ∈ range (fejerStart K), fejerSeriesCoeff n = 0 := by
    apply ofReal_injective
    have h := sum_range_fejerStart_mul_pow K 1
    simp only [one_pow, mul_one, fejerPoly_one, mul_zero, sum_const_zero] at h
    simpa [ofReal_sum] using h
  -- The initial half of block `K` contributes `(2⁻¹) ^ K * harmonic (fejerDeg K)`.
  have hsplit : ∑ n ∈ range (fejerStart K + fejerDeg K), fejerSeriesCoeff n =
      (∑ n ∈ range (fejerStart K), fejerSeriesCoeff n) +
      ∑ n ∈ Ico (fejerStart K) (fejerStart K + fejerDeg K), fejerSeriesCoeff n :=
    (sum_range_add_sum_Ico _ (Nat.le_add_right _ _)).symm
  have hhalf : ∑ n ∈ Ico (fejerStart K) (fejerStart K + fejerDeg K), fejerSeriesCoeff n =
      (2 : ℝ)⁻¹ ^ K * (harmonic (fejerDeg K) : ℝ) := by
    simpa [sum_range_fejerPolyCoeff] using
      sum_Ico_fejerStart_add_mul (α := ℝ) K (fejerDeg K) (by omega) (fun _ ↦ (1 : ℝ))
  rw [hsplit, hprev, zero_add, hhalf]
  have hlog : ((K + 1 : ℝ) * (2 : ℝ) ^ K) * Real.log 2 = Real.log (fejerDeg K : ℝ) := by
    rw [fejerDeg, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    ring
  have hharm : Real.log (fejerDeg K : ℝ) ≤ (harmonic (fejerDeg K) : ℝ) := by
    simpa [Nat.floor_natCast] using log_le_harmonic_floor (fejerDeg K : ℝ) (Nat.cast_nonneg _)
  calc (K + 1 : ℝ) * Real.log 2
      = (2 : ℝ)⁻¹ ^ K * (((K + 1 : ℝ) * (2 : ℝ) ^ K) * Real.log 2) := by
        rw [inv_pow]
        field_simp
    _ = (2 : ℝ)⁻¹ ^ K * Real.log (fejerDeg K : ℝ) := by rw [hlog]
    _ ≤ (2 : ℝ)⁻¹ ^ K * (harmonic (fejerDeg K) : ℝ) := by gcongr

private theorem hasSum_fejerSeriesCoeff_mul_pow {w : ℂ} (hw : ‖w‖ < 1)
    (hsumm_f : Summable fun k ↦
      ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w) :
    HasSum (fun n ↦ (fejerSeriesCoeff n : ℂ) * w ^ n)
      (∑' k, ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w) := by
  have hsumm : Summable fun n ↦ (fejerSeriesCoeff n : ℂ) * w ^ n :=
    TauCeti.summable_mul_pow_of_norm_le
      (fun n ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using abs_fejerSeriesCoeff_le_one n)
      hw
  have hlim1 : Tendsto (fun K ↦ ∑ n ∈ range (fejerStart K), (fejerSeriesCoeff n : ℂ) * w ^ n)
      atTop (𝓝 (∑' n, (fejerSeriesCoeff n : ℂ) * w ^ n)) :=
    hsumm.hasSum.tendsto_sum_nat.comp fejerStart_strictMono.tendsto_atTop
  have hlim2 : Tendsto (fun K ↦ ∑ n ∈ range (fejerStart K), (fejerSeriesCoeff n : ℂ) * w ^ n)
      atTop (𝓝 (∑' k, ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w)) := by
    simp_rw [sum_range_fejerStart_mul_pow]
    exact hsumm_f.hasSum.tendsto_sum_nat
  exact (tendsto_nhds_unique hlim1 hlim2) ▸ hsumm.hasSum

/-- **Fejér's disc-algebra counterexample (1911).** There exist real coefficients `c : ℕ → ℝ`
bounded by `1` and tending to `0`, and a function `P : ℂ → ℂ` continuous on the closed unit disc
and holomorphic on the open unit disc, such that `∑' n, (c n : ℂ) * w ^ n = P w` for `‖w‖ < 1`,
yet the partial sums `∑ n ∈ range N, c n` at `w = 1` are unbounded above (and hence fail to
converge). -/
theorem exists_continuousOn_closedBall_hasSum_unbounded_sum_range :
    ∃ (c : ℕ → ℝ) (P : ℂ → ℂ),
      (∀ n, |c n| ≤ 1) ∧
      Tendsto c atTop (𝓝 0) ∧
      ContinuousOn P (closedBall 0 1) ∧
      DifferentiableOn ℂ P (ball 0 1) ∧
      (∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n ↦ (c n : ℂ) * w ^ n) (P w)) ∧
      (∀ B : ℝ, ∃ N : ℕ, B ≤ ∑ n ∈ range N, c n) := by
  set f : ℕ → ℂ → ℂ := fun k w ↦
    ((2 : ℝ)⁻¹ ^ k : ℂ) * w ^ fejerStart k * fejerPoly (fejerDeg k) w
  set P : ℂ → ℂ := fun w ↦ ∑' k, f k w
  set u : ℕ → ℝ := fun k ↦ (2 * (1 + 2 * π)) * (2 : ℝ)⁻¹ ^ k
  have hu : Summable u :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left _
  have hbound : ∀ k (w : ℂ), w ∈ closedBall (0 : ℂ) 1 → ‖f k w‖ ≤ u k := by
    intro k w hw
    rw [mem_closedBall_zero_iff] at hw
    simp only [f, u, norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
    calc (2 : ℝ)⁻¹ ^ k * ‖w‖ ^ fejerStart k * ‖fejerPoly (fejerDeg k) w‖
        ≤ (2 : ℝ)⁻¹ ^ k * 1 * (2 * (1 + 2 * π)) := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg w) hw
          · exact norm_fejerPoly_le_of_norm_le_one _ hw
      _ = (2 * (1 + 2 * π)) * (2 : ℝ)⁻¹ ^ k := by ring
  have hdiff_term : ∀ k, Differentiable ℂ (f k) := fun k ↦
    ((differentiable_const _).mul (differentiable_pow _)).mul (differentiable_fejerPoly _)
  refine ⟨fejerSeriesCoeff, P, abs_fejerSeriesCoeff_le_one, tendsto_fejerSeriesCoeff_zero, ?_, ?_,
    ?_, ?_⟩
  · exact continuousOn_tsum (fun k ↦ (hdiff_term k).continuous.continuousOn) hu hbound
  · exact differentiableOn_tsum_of_summable_norm hu (fun k ↦ (hdiff_term k).differentiableOn)
      isOpen_ball fun k w hw ↦ hbound k w (ball_subset_closedBall hw)
  · intro w hw
    exact hasSum_fejerSeriesCoeff_mul_pow hw
      (Summable.of_norm_bounded hu fun k ↦ hbound k w (mem_closedBall_zero_iff.mpr hw.le))
  · intro B
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    obtain ⟨K, hK⟩ := exists_nat_gt (B / Real.log 2)
    refine ⟨fejerStart K + fejerDeg K, ?_⟩
    have hB : B ≤ (K + 1 : ℝ) * Real.log 2 := by
      have : B / Real.log 2 ≤ (K : ℝ) + 1 := by linarith
      exact (div_le_iff₀ hlog2).mp this
    exact hB.trans (sum_range_fejerStart_add_fejerDeg K)

end TauCeti
