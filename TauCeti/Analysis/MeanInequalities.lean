/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# Superadditivity of the weighted geometric mean

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

## Main statements

* `Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`: the weighted geometric mean is superadditive.

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

end Real
