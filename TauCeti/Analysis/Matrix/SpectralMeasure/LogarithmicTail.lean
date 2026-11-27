/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues

import TauCeti.Analysis.Matrix.SingularValues.RowDistance
import TauCeti.Analysis.Real.Sqrt

/-!
# Logarithmic tails of singular-value measures

The logarithmic integral near zero is controlled by splitting the singular values in increasing
order at a cutoff rank. The smallest values contribute at most the fraction below that rank
times the negative logarithm of the least singular value. For the rest, a lower bound linear in
the rank gives uniform control near zero. Bounds on row distances of rectangular submatrices
supply the linear lower bound.

The resulting tail estimate is the small-singular-value input to logarithmic convergence in
Girko's hermitization.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), §4.2.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.8.3.
-/

public section

open Filter MeasureTheory Set Submodule TauCeti.Probability
open scoped ENNReal Topology

namespace Matrix

-- The quarter-power bound retains a factor that vanishes with the cutoff and leaves
-- the reciprocal square root of the rank profile, whose averages are bounded.
private theorem logTail_term_le {a x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    (Ioo 0 a).indicator (fun t ↦ max 0 (-Real.log t)) x ≤
      4 * Real.sqrt (Real.sqrt a) / Real.sqrt y := by
  by_cases hx : x ∈ Ioo 0 a
  · rw [indicator_of_mem hx]
    apply max_le (by positivity)
    have hxq := Real.neg_inv_le_log (Real.sqrt_nonneg (Real.sqrt x))
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx.1.le] at hxq
    have hxpos := Real.sqrt_pos.2 hx.1
    have hq := Real.sqrt_pos.2 hxpos
    calc
      _ ≤ 4 * (Real.sqrt (Real.sqrt x))⁻¹ := by linarith only [hxq]
      _ = 4 * Real.sqrt (Real.sqrt x) / Real.sqrt x := by
        rw [mul_div_assoc]
        congr 1
        field_simp [hq.ne', hxpos.ne']
        nlinarith only [Real.sq_sqrt (Real.sqrt_nonneg x)]
      _ ≤ 4 * Real.sqrt (Real.sqrt a) / Real.sqrt y :=
        div_le_div₀ (by positivity) (by gcongr; exact hx.2.le) (by positivity)
          (Real.sqrt_le_sqrt hxy)
  · rw [indicator_of_notMem hx]
    positivity

private theorem sum_inv_sqrt_rank_profile_le (N : ℕ) (c : ℝ) :
    (∑ i : Fin N, (Real.sqrt (c * ((i : ℝ) + 1) / N))⁻¹) ≤ 2 * N / Real.sqrt c := by
  have hsum : (∑ i : Fin N, (Real.sqrt ((i : ℝ) + 1))⁻¹) ≤ 2 * Real.sqrt N := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (Real.sqrt ((i : ℝ) + 1))⁻¹)]
    exact TauCeti.sum_range_inv_sqrt_add_one_le N
  have hterm (i : Fin N) : (Real.sqrt (c * ((i : ℝ) + 1) / N))⁻¹ =
      (Real.sqrt N / Real.sqrt c) * (Real.sqrt ((i : ℝ) + 1))⁻¹ := by
    rw [Real.sqrt_div' _ (Nat.cast_nonneg N), Real.sqrt_mul' c (by positivity),
      inv_div, ← div_eq_mul_inv, div_div]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
  calc
    _ = 2 * (Real.sqrt N) ^ 2 / Real.sqrt c := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

private theorem sum_logTail_le {N r : ℕ} {σ : Fin N → ℝ}
    {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hsmall : ∀ i : Fin N, (i : ℕ) < r → b ≤ σ i)
    (hlarge : ∀ i : Fin N, r ≤ (i : ℕ) → c * ((i : ℝ) + 1) / N ≤ σ i) :
    (∑ i, (Ioo 0 a).indicator (fun t ↦ max 0 (-Real.log t)) (σ i)) ≤
      r * max 0 (-Real.log b) + (8 * Real.sqrt (Real.sqrt a) / Real.sqrt c) * N := by
  classical
  let s := Finset.univ.filter (fun i : Fin N ↦ (i : ℕ) < r)
  have hcard : s.card ≤ r := by
    rw [← Finset.card_range r]
    apply Finset.card_le_card_of_injOn Fin.val (fun i hi ↦ ?_) Fin.val_injective.injOn
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  let g := (Ioo 0 a).indicator (fun t ↦ max 0 (-Real.log t))
  let C := 4 * Real.sqrt (Real.sqrt a)
  have hC : 0 ≤ C := by positivity
  have hterm (i : Fin N) : g (σ i) ≤
      (s : Set (Fin N)).indicator (fun _ ↦ max 0 (-Real.log b)) i +
        C * (Real.sqrt (c * ((i : ℝ) + 1) / N))⁻¹ := by
    by_cases hi : (i : ℕ) < r
    · have hmem : i ∈ (s : Set (Fin N)) := by simp [s, hi]
      rw [indicator_of_mem hmem]
      apply le_add_of_le_of_nonneg _ (by positivity)
      dsimp [g]
      by_cases ha : σ i ∈ Ioo 0 a
      · rw [indicator_of_mem ha]
        exact max_le_max_left 0 (neg_le_neg (Real.log_le_log hb (hsmall i hi)))
      · rw [indicator_of_notMem ha]
        exact le_max_left _ _
    · have hmem : i ∉ (s : Set (Fin N)) := by simp [s, hi]
      rw [indicator_of_notMem hmem, zero_add, ← div_eq_mul_inv]
      have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
      exact logTail_term_le (by positivity) (hlarge i (le_of_not_gt hi))
  calc
    _ ≤ ∑ i : Fin N, ((s : Set (Fin N)).indicator (fun _ ↦ max 0 (-Real.log b)) i +
        C * (Real.sqrt (c * ((i : ℝ) + 1) / N))⁻¹) := Finset.sum_le_sum fun i _ ↦ hterm i
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_indicator_subset (fun _ ↦ max 0 (-Real.log b))
        (Finset.subset_univ _),
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      refine add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (le_max_left _ _)) ?_
      refine (mul_le_mul_of_nonneg_left (sum_inv_sqrt_rank_profile_le N c) hC).trans_eq ?_
      dsimp [C]
      ring

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Bound the logarithmic integral on `(0, a)` using a positive lower bound `b` for the
first `r` singular values and a linear lower bound for the rest, counted from the smallest
singular value. The error from the linear part decays as `a^(1/4)`. -/
theorem lintegral_neg_log_singularValueMeasure_le {m : Type*} [Fintype m] {N : ℕ} [NeZero N]
    (A : Matrix m (Fin N) 𝕜) {r : ℕ} {a b c : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hmin : ∀ i : Fin N, (i : ℕ) < r → b ≤ (toEuclideanLin A).singularValues i.rev)
    (hlinear : ∀ i : Fin N, r ≤ (i : ℕ) →
      c * ((i : ℝ) + 1) / N ≤ (toEuclideanLin A).singularValues i.rev) :
    ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x) ∂(A.singularValueMeasure : Measure ℝ) ≤
      ENNReal.ofReal ((r : ℝ) / N * max 0 (-Real.log b) +
        8 * Real.sqrt (Real.sqrt a) / Real.sqrt c) := by
  let g := (Ioo 0 a).indicator (fun t ↦ max 0 (-Real.log t))
  have hg (x : ℝ) : (Ioo 0 a).indicator (fun t ↦ ENNReal.ofReal (-Real.log t)) x =
      ENNReal.ofReal (g x) := by
    by_cases hx : x ∈ Ioo 0 a <;> simp [g, hx]
  have hf : Measurable (fun x : ℝ ↦ ENNReal.ofReal (-Real.log x)) := by fun_prop
  rw [← lintegral_indicator measurableSet_Ioo, singularValueMeasure_def,
    lintegral_empiricalMeasureOfFintype (hf.indicator measurableSet_Ioo)]
  let f (i : ℕ) := ENNReal.ofReal (g ((toEuclideanLin A).singularValues i))
  have hsum : (∑ i : Fin (Fintype.card (Fin N)), f i) = ∑ i : Fin N, f i := by
    rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f, Fintype.card_fin]
  simp only [hg, Fintype.card_fin]
  rw [hsum, ← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, f]
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by
    apply indicator_nonneg
    exact fun x _ ↦ le_max_left 0 (-Real.log x)), ← ENNReal.ofReal_natCast N,
    ← ENNReal.ofReal_inv_of_pos hN, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_mul_eq_div, div_le_iff₀ hN]
  refine (sum_logTail_le (a := a) hb hc hmin hlinear).trans_eq ?_
  rw [add_mul]
  congr 1
  rw [mul_right_comm, div_mul_cancel₀ _ hN.ne']

/-- A linear bound on the intermediate singular values and a vanishing normalized logarithmic
contribution from the exceptional smallest ones give vanishing logarithmic tails at zero. -/
theorem log_tail_zero_of_singularValues_lower_bounds
    (A : ∀ n : ℕ, Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) {r : ℕ → ℕ} {b : ℕ → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hbudget : Tendsto (fun n ↦ (r n : ℝ) / (n + 1) * max 0 (-Real.log (b n))) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, 0 < b n ∧ b n ≤ (toEuclideanLin (A n)).singularValues n ∧
      ∀ i : Fin (n + 1), r n ≤ (i : ℕ) → c * ((i : ℝ) + 1) / (n + 1) ≤
        (toEuclideanLin (A n)).singularValues i.rev) :
    ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ), ∀ᶠ n in atTop,
      ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x)
        ∂((A n).singularValueMeasure : Measure ℝ) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let δ := ε * Real.sqrt c / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨(δ ^ 2) ^ 2, by positivity, ?_⟩
  have hcutoff : 8 * Real.sqrt (Real.sqrt ((δ ^ 2) ^ 2)) / Real.sqrt c = ε / 2 := by
    rw [Real.sqrt_sq (sq_nonneg δ), Real.sqrt_sq hδ.le]
    dsimp [δ]
    field_simp
    ring
  filter_upwards [hbound, hbudget.eventually_le_const (half_pos hε)] with n hn hb
  refine (lintegral_neg_log_singularValueMeasure_le (A n) (r := r n) hn.1 hc ?_ ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · intro i _
    have hi : (i.rev : ℕ) ≤ n := Nat.lt_succ_iff.mp i.rev.isLt
    exact hn.2.1.trans ((toEuclideanLin (A n)).singularValues_antitone hi)
  · simpa only [Nat.cast_succ] using hn.2.2
  · rw [hcutoff, Nat.cast_succ]
    linarith only [hb]

/-- Suppose the least singular value is at least `(n + 1)^(-B)` and, after removing `k` rows
for each `r n ≤ k ≤ n / 2`, the remaining rows are at distance at least `c √((k + 1) / (n + 1))`
from the spans of the other remaining rows. If `r n log(n + 1) / (n + 1)` tends to zero,
the logarithmic tails of the singular-value measures vanish at zero. -/
theorem log_tail_zero_of_row_distances
    (A : ∀ n : ℕ, Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) {r : ℕ → ℕ} {B c : ℝ} (hc : 0 < c)
    (hcut : Tendsto (fun n ↦ (r n : ℝ) / (n + 1) * Real.log (n + 1)) atTop (𝓝 0))
    (hmin : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ (-B) ≤ (toEuclideanLin (A n)).singularValues n)
    (hrow : ∀ᶠ n in atTop, ∀ k : ℕ, r n ≤ k → k ≤ n / 2 →
      ∃ e : Fin (n + 1 - k) ↪ Fin (n + 1), ∀ j,
        c * Real.sqrt (((k : ℝ) + 1) / (n + 1)) ≤ Metric.infDist (WithLp.toLp 2 (A n (e j)))
          (span 𝕜 ((fun l ↦ WithLp.toLp 2 (A n (e l))) '' {j}ᶜ) :
            Set (EuclideanSpace 𝕜 (Fin (n + 1))))) :
    ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ), ∀ᶠ n in atTop,
      ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x)
        ∂((A n).singularValueMeasure : Measure ℝ) ≤ ENNReal.ofReal ε := by
  refine log_tail_zero_of_singularValues_lower_bounds A (r := fun n ↦ 2 * r n)
    (b := fun n ↦ ((n : ℝ) + 1) ^ (-B)) (half_pos hc) ?_ ?_
  · refine ((tendsto_const_nhds (x := 2 * max 0 B)).mul hcut).congr' (Eventually.of_forall ?_)
      |>.trans (by simp)
    intro n
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hmax := max_mul_of_nonneg (0 : ℝ) B hlog
    simp only [zero_mul] at hmax
    rw [Real.log_rpow (by positivity), neg_mul, neg_neg, ← hmax]
    push_cast
    ring
  · filter_upwards [hmin, hrow] with n hn hrows
    refine ⟨Real.rpow_pos_of_pos (by positivity) _, hn, fun i hi ↦ ?_⟩
    obtain ⟨e, he⟩ := hrows ((i : ℕ) / 2) (by omega) (by have := i.isLt; omega)
    have h := le_singularValues_rev_of_le_infDist_row_span (A n) i e
      (by simpa only [Nat.cast_succ] using he)
    simpa only [Nat.cast_succ, div_mul_eq_mul_div, div_div] using h

end Matrix
