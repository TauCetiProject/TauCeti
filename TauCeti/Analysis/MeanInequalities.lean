/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# Mean inequalities

This file collects classical inequalities complementing `Mathlib.Analysis.MeanInequalities`.

For nonnegative weights `w i` summing to `1`, the weighted geometric mean
`G(a) = ∏ i, a i ^ w i` of a nonnegative family is superadditive:

`G(a) + G(b) ≤ G(a + b)`.

Since `G` is also positively homogeneous, this says that the weighted geometric mean is concave on
the nonnegative orthant. Applied to the eigenvalues of a positive semidefinite matrix `M` with
equal weights, it gives `1 + det M ^ (1 / n) ≤ det (1 + M) ^ (1 / n)`, the core of Minkowski's
determinant inequality (`Matrix.PosSemidef.det_rpow_add_det_rpow_le`).

The proof divides by `a i + b i` and applies the inequality of arithmetic and geometric means
`Real.geom_mean_le_arith_mean_weighted` to the two normalized families, whose weighted means add
up to at most `1`.

Minkowski's inequality also holds for unconditional sums of `ℝ≥0∞`-valued families over an
arbitrary index type, with no summability hypotheses: infinite sums and infinite terms are allowed.
Mathlib states it for finite sums (`ENNReal.Lp_add_le`) and for summable `ℝ≥0`-valued families
(`NNReal.Lp_add_le_tsum`); the `ℝ≥0∞` form follows from the finite one by taking the supremum over
finite partial sums. It is the counting-measure case of `ENNReal.lintegral_Lp_add_le`, stated
without measure theory. It gives the triangle inequality for gauges defined as `ℓᵖ` sums in `ℝ≥0∞`,
such as the Hilbert–Schmidt energy of an operator. Hölder's inequality holds for such sums in the
same way, extending `ENNReal.inner_le_Lp_mul_Lq` and `NNReal.inner_le_Lp_mul_Lq_tsum`. The `ℓᵖ`
norm of such a family is antitone in the exponent, which gives the inclusions between Schatten
classes of operators.

Finally, the two-point weighted AM-GM inequality is restated after normalizing by positive scalars
`a` and `b`: `A ^ (1 - θ) * B ^ θ ≤ ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ)`,
strictly when `0 < θ < 1` and `A / a ≠ B / b`. This is the form used to compare volumes of
hyperplane sections in the Kneser–Süss equality argument for Brunn–Minkowski.

## Main statements

* `Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`: the weighted geometric mean is superadditive.
* `Real.geom_mean_le_arith_mean2_weighted_div_mul`,
  `Real.geom_mean_lt_arith_mean2_weighted_div_mul`: two-point weighted AM-GM after normalizing
  by positive scalars, with the strict form.
* `ENNReal.Lp_add_le_tsum`: Minkowski's inequality for unconditional sums in `ℝ≥0∞`.
* `ENNReal.inner_le_Lp_mul_Lq_tsum`: Hölder's inequality for unconditional sums in `ℝ≥0∞`.
* `ENNReal.Lq_le_Lp_tsum`: the `ℓᵖ` norm of an `ℝ≥0∞`-valued family is antitone in `p`.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press
  1952, Chapter II.
-/

public section

namespace Real

/-- **Superadditivity of the weighted geometric mean.** For nonnegative weights `w i` summing to
`1` and nonnegative families `a` and `b`,
`∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i`. -/
theorem prod_rpow_add_prod_rpow_le_prod_add_rpow {ι : Type*} (s : Finset ι) {w a b : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∏ i ∈ s, a i ^ w i + ∏ i ∈ s, b i ^ w i ≤ ∏ i ∈ s, (a i + b i) ^ w i := by
  have hc (i) (hi : i ∈ s) : 0 ≤ a i + b i := add_nonneg (ha i hi) (hb i hi)
  -- Factor `a i = (a i / (a i + b i)) * (a i + b i)`, and likewise for `b`; this holds even when
  -- `a i + b i = 0`, since then `a i = b i = 0`.
  have hfactor {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hfc : ∀ i ∈ s, f i ≤ a i + b i) :
      ∏ i ∈ s, f i ^ w i =
        (∏ i ∈ s, (f i / (a i + b i)) ^ w i) * ∏ i ∈ s, (a i + b i) ^ w i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [← mul_rpow (div_nonneg (hf i hi) (hc i hi)) (hc i hi),
      div_mul_cancel_of_imp fun h => le_antisymm (h ▸ hfc i hi) (hf i hi)]
  rw [hfactor ha fun i hi => le_add_of_nonneg_right (hb i hi),
    hfactor hb fun i hi => le_add_of_nonneg_left (ha i hi), ← add_mul]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun i hi => rpow_nonneg (hc i hi) _) ?_
  -- The two normalized families have weighted arithmetic means adding up to at most `1`.
  calc ∏ i ∈ s, (a i / (a i + b i)) ^ w i + ∏ i ∈ s, (b i / (a i + b i)) ^ w i
      ≤ ∑ i ∈ s, w i * (a i / (a i + b i)) + ∑ i ∈ s, w i * (b i / (a i + b i)) :=
        add_le_add
          (geom_mean_le_arith_mean_weighted s w _ hw hw' fun i hi => div_nonneg (ha i hi) (hc i hi))
          (geom_mean_le_arith_mean_weighted s w _ hw hw' fun i hi => div_nonneg (hb i hi) (hc i hi))
    _ = ∑ i ∈ s, w i * ((a i + b i) / (a i + b i)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [add_div, mul_add]
    _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum fun i hi =>
        mul_le_of_le_one_right (hw i hi) (div_self_le_one _)
    _ = 1 := hw'

/-- Splitting a weighted geometric mean through positive normalizers `a` and `b`:
`A ^ (1 - θ) * B ^ θ = (A / a) ^ (1 - θ) * (B / b) ^ θ * (a ^ (1 - θ) * b ^ θ)`. -/
theorem rpow_one_sub_mul_rpow_eq_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a)
    (hb : 0 < b) :
    A ^ (1 - θ) * B ^ θ = (A / a) ^ (1 - θ) * (B / b) ^ θ * (a ^ (1 - θ) * b ^ θ) := by
  rw [mul_mul_mul_comm, ← mul_rpow (div_nonneg hA ha.le) ha.le,
    ← mul_rpow (div_nonneg hB hb.le) hb.le, div_mul_cancel₀ A ha.ne', div_mul_cancel₀ B hb.ne']

/-- **Normalized weighted AM-GM.** For positive normalizers `a` and `b`, the weighted geometric
mean of `A` and `B` is at most the weighted arithmetic mean of `A / a` and `B / b` times the
weighted geometric mean of `a` and `b`. -/
theorem geom_mean_le_arith_mean2_weighted_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    A ^ (1 - θ) * B ^ θ ≤ ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ) := by
  rw [rpow_one_sub_mul_rpow_eq_div_mul hA hB ha hb]
  exact mul_le_mul_of_nonneg_right (geom_mean_le_arith_mean2_weighted (by linarith) hθ₀
    (div_nonneg hA ha.le) (div_nonneg hB hb.le) (by ring))
    (mul_nonneg (rpow_nonneg ha.le _) (rpow_nonneg hb.le _))

/-- The strict form of `Real.geom_mean_le_arith_mean2_weighted_div_mul` for `0 < θ < 1` and
`A / a ≠ B / b`. -/
theorem geom_mean_lt_arith_mean2_weighted_div_mul {A B a b θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hne : A / a ≠ B / b) :
    A ^ (1 - θ) * B ^ θ < ((1 - θ) * (A / a) + θ * (B / b)) * (a ^ (1 - θ) * b ^ θ) := by
  rw [rpow_one_sub_mul_rpow_eq_div_mul hA hB ha hb]
  exact mul_lt_mul_of_pos_right ((geom_mean_lt_arith_mean2_weighted_iff_of_pos
    (by linarith) hθ₀ (div_nonneg hA ha.le) (div_nonneg hB hb.le) (by ring)).2 hne)
    (mul_pos (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _))

end Real

namespace ENNReal

open scoped ENNReal

/-- **Minkowski's inequality** for unconditional sums in `ℝ≥0∞`: for `1 ≤ p`,
`(∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)`.
No summability hypotheses are needed; both sides may be infinite. -/
theorem Lp_add_le_tsum {ι : Type*} (f g : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  -- Bound each finite partial sum by the finite Minkowski inequality.
  rw [one_div, rpow_inv_le_iff hp0, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  rw [← rpow_inv_le_iff hp0, ← one_div]
  grw [Lp_add_le s f g hp, ENNReal.sum_le_tsum s, ENNReal.sum_le_tsum (f := fun i ↦ g i ^ p) s]

/-- **Hölder's inequality** for unconditional sums in `ℝ≥0∞`: for conjugate exponents `p` and `q`,
`∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)`.
No summability hypotheses are needed; both sides may be infinite. -/
theorem inner_le_Lp_mul_Lq_tsum {ι : Type*} (f g : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  -- Bound each finite partial sum by the finite Hölder inequality.
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ (inner_le_Lp_mul_Lq s f g hpq).trans ?_
  gcongr
  · exact one_div_nonneg.2 hpq.nonneg
  · exact ENNReal.sum_le_tsum s
  · exact one_div_nonneg.2 hpq.symm.nonneg
  · exact ENNReal.sum_le_tsum s

/-- The `ℓᵖ` norms of an `ℝ≥0∞`-valued family decrease as the exponent grows: for `0 < p ≤ q`,
`(∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p)`. No summability hypotheses are needed;
both sides may be infinite. This is the unconditional-sum form of `ENNReal.rpow_add_rpow_le`. -/
theorem Lq_le_Lp_tsum {ι : Type*} (f : ι → ℝ≥0∞) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p) := by
  set S := (∑' i, f i ^ p) ^ (1 / p) with hS
  have hpq' : 0 ≤ q - p := sub_nonneg.2 hpq
  -- Each term is at most the `ℓᵖ` norm `S`, so `f i ^ q ≤ f i ^ p * S ^ (q - p)`.
  have hfS (i : ι) : f i ≤ S := by
    rw [hS, one_div, le_rpow_inv_iff hp]
    exact ENNReal.le_tsum (f := fun i ↦ f i ^ p) i
  have hSp : S ^ p = ∑' i, f i ^ p := by rw [hS, one_div, rpow_inv_rpow hp.ne']
  rw [one_div, rpow_inv_le_iff (hp.trans_le hpq)]
  calc ∑' i, f i ^ q = ∑' i, f i ^ p * f i ^ (q - p) := by
        simp_rw [← rpow_add_of_nonneg _ _ hp.le hpq', add_sub_cancel]
    _ ≤ ∑' i, f i ^ p * S ^ (q - p) := by gcongr with i; exact hfS i
    _ = S ^ q := by
        rw [ENNReal.tsum_mul_right, ← hSp, ← rpow_add_of_nonneg _ _ hp.le hpq', add_sub_cancel]

end ENNReal
