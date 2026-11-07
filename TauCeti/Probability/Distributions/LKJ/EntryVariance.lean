/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LKJ.CoordinateIntegral
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.Beta.Symmetric
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Entry variances in the independent partial-correlation construction

For `η > 0`, independent centered symmetric Beta partial correlations with the column shapes
`lkjPartialCorrelationShape p η` give a correlation Gram matrix whose off-diagonal entries
have second moment and variance `1 / (2 * η + p - 1)`.

The calculation uses the triangular factor: its entries in any fixed column below the
diagonal have second moment `1 / (2 * η + p - 1)`, while distinct column contributions to
an off-diagonal Gram entry are orthogonal in the integral. The residual-factor moments
telescope, and the final sum includes the diagonal triangular contribution.

## Main results

* `integrable_sq_partialCorrelationGram` gives second-moment integrability for every entry.
* `integral_sq_partialCorrelationGram` gives the off-diagonal entry second moments.
* `variance_partialCorrelationGram` gives the corresponding variances.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

private abbrev coordinateLaw (η : ℝ) (ij : strictLowerTriangle p) : Measure ℝ :=
  (betaMeasure (lkjPartialCorrelationShape p η ij)
    (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)

private abbrev coordinateProduct (p : ℕ) (η : ℝ) :=
  Measure.pi (coordinateLaw (p := p) η)

private theorem coordinate_probability (hη : 0 < η) (ij : strictLowerTriangle p) :
    IsProbabilityMeasure (coordinateLaw η ij) := by
  let _ := isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
    (lkjPartialCorrelationShape_pos hη ij)
  infer_instance

private theorem coordinate_ae_abs_le_one (ij : strictLowerTriangle p) :
    ∀ᵐ x ∂coordinateLaw η ij, |x| ≤ 1 := by
  apply (ae_map_iff (by fun_prop) (by measurability)).2
  filter_upwards [ae_mem_Ioo_betaMeasure
    (lkjPartialCorrelationShape p η ij) (lkjPartialCorrelationShape p η ij)] with x hx
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

-- Each factor isolates one partial-correlation coordinate in a triangular entry.
private def entryFactor (i k : Fin p) (ij : strictLowerTriangle p) (x : ℝ) : ℝ :=
  (if ij.1.1 = i ∧ ij.1.2 = k then x else 1) *
    (if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - x ^ 2) else 1)

private theorem abs_entryFactor_le_one (i k : Fin p) (ij : strictLowerTriangle p)
    {x : ℝ} (hx : |x| ≤ 1) : |entryFactor i k ij x| ≤ 1 := by
  have hs : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hx)
  have hs' : Real.sqrt (1 - x ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg x]
  unfold entryFactor
  split_ifs <;> simp_all [abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem prod_entryFactor (z : strictLowerTriangle p → ℝ) (i k : Fin p)
    (hk : k ≤ i) :
    (∏ ij, entryFactor i k ij (z ij)) = partialCorrelationCholesky z i k := by
  simp only [entryFactor, Finset.prod_mul_distrib]
  have hr : (∏ ij : strictLowerTriangle p,
      if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - z ij ^ 2) else 1) =
      ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < k,
        Real.sqrt (1 - z ij ^ 2) := by rw [Finset.prod_filter]
  rw [hr]
  rcases hk.eq_or_lt with he | hk
  · subst k
    rw [partialCorrelationCholesky_apply_self]
    have hnone : ∀ ij : strictLowerTriangle p, ¬(ij.1.1 = i ∧ ij.1.2 = i) := by
      intro ij h
      have := ij.2
      simp_all
    simp only [hnone, ↓reduceIte, Finset.prod_const_one, one_mul]
    congr 1
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    exact fun h ↦ h ▸ ij.2
  · rw [partialCorrelationCholesky_apply_of_gt z hk]
    congr 1
    have heq (ij : strictLowerTriangle p) :
        (ij.1.1 = i ∧ ij.1.2 = k) ↔ ij = ⟨(i, k), hk⟩ := by
      simp only [Subtype.ext_iff, Prod.ext_iff]
    simp_rw [heq]
    simp

private theorem entryFactor_of_other_row (i k : Fin p) (ij : strictLowerTriangle p)
    (hi : ij.1.1 ≠ i) (x : ℝ) : entryFactor i k ij x = 1 := by
  simp [entryFactor, hi]

private theorem integral_entryFactor_sq (hη : 0 < η) (i k : Fin p)
    (ij : strictLowerTriangle p) :
    ∫ x, entryFactor i k ij x ^ 2 ∂coordinateLaw η ij =
      (if ij.1.1 = i ∧ ij.1.2 = k then
        1 / (2 * lkjPartialCorrelationShape p η ij + 1) else 1) *
      (if ij.1.1 = i ∧ ij.1.2 < k then
        (2 * lkjPartialCorrelationShape p η ij) /
          (2 * lkjPartialCorrelationShape p η ij + 1) else 1) := by
  let a := lkjPartialCorrelationShape p η ij
  have ha : 0 < a := lkjPartialCorrelationShape_pos hη ij
  let _ := coordinate_probability hη ij
  have hsq : ∫ x, x ^ 2 ∂coordinateLaw η ij = 1 / (2 * a + 1) := by
    have h := integral_id_betaMeasure (by norm_num : (0 : ℝ) < 1 / 2) ha
    rw [← betaMeasure_map_centered_sq ha,
      integral_map (by fun_prop) (by fun_prop)] at h
    rw [integral_map (by fun_prop) (by fun_prop)]
    convert h using 1
    field_simp
    ring
  have hint : Integrable (fun x : ℝ ↦ x ^ 2) (coordinateLaw η ij) :=
    ((integrable_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff (r := 0) ha 2).2
      (by simpa using ha)).congr (by simp)
  by_cases hr : ij.1.1 = i
  · by_cases he : ij.1.2 = k
    · simpa [entryFactor, hr, he, a] using hsq
    · by_cases hl : ij.1.2 < k
      · simp only [entryFactor, hr, true_and, he, ↓reduceIte, hl, one_mul]
        rw [integral_congr_ae ((coordinate_ae_abs_le_one (η := η) ij).mono
          fun x hx ↦ Real.sq_sqrt (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hx))),
          integral_sub (integrable_const 1) hint, integral_const, hsq]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        dsimp only [a] at ha ⊢
        field_simp [(by positivity : 2 * lkjPartialCorrelationShape p η ij + 1 ≠ 0)]
        ring
      · simp [entryFactor, hr, he, hl]
  · simp [entryFactor, hr]

private theorem twice_shape_add_one (ij : strictLowerTriangle p) :
    2 * lkjPartialCorrelationShape p η ij + 1 =
      2 * η + p - 1 - ij.1.2.val := by
  have h : (p - 1 - ij.1.2.val : ℕ) + ij.1.2.val + 1 = p := by
    have := ij.2
    have := ij.1.1.isLt
    omega
  have hr : ((p - 1 - ij.1.2.val : ℕ) : ℝ) + ij.1.2.val + 1 = p := by
    exact_mod_cast h
  rw [lkjPartialCorrelationShape_def]
  linarith

private theorem residual_moment_product (hη : 0 < η) (i k : Fin p) (hk : k ≤ i) :
    (∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < k,
      (2 * lkjPartialCorrelationShape p η ij) /
        (2 * lkjPartialCorrelationShape p η ij + 1)) =
      (2 * η + p - 1 - k.val) / (2 * η + p - 1) := by
  let D := 2 * η + p - 1
  have hD : 0 < D := by
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    dsimp only [D]
    linarith
  have hprefix : ∀ n ≤ i.val,
      (∏ j ∈ Finset.range n, (D - j - 1) / (D - j)) = (D - n) / D := by
    intro n hn
    induction n with
    | zero => simp [hD.ne']
    | succ n ih =>
      rw [Finset.prod_range_succ, ih (by omega)]
      have hd : D - n ≠ 0 := by
        have hi : (i.val : ℝ) + 1 ≤ p := by
          exact_mod_cast (Nat.succ_le_of_lt i.isLt)
        have hn' : (n : ℝ) ≤ i.val := by exact_mod_cast (by omega : n ≤ i.val)
        dsimp only [D]
        linarith
      push_cast
      field_simp
      ring
  rw [← hprefix k.val (by exact_mod_cast hk)]
  apply Finset.prod_bij (fun ij _ ↦ ij.1.2.val)
  · intro ij hij
    simpa using (Finset.mem_filter.mp hij).2.2
  · intro ij hij lm hlm he
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp hij).2.1.trans (Finset.mem_filter.mp hlm).2.1.symm
    · exact Fin.ext he
  · intro n hn
    have hnk : n < k.val := Finset.mem_range.mp hn
    let j : Fin p := ⟨n, hnk.trans k.isLt⟩
    refine ⟨⟨(i, j), ?_⟩, ?_, rfl⟩
    · exact (Fin.mk_lt_mk.mpr hnk).trans_le hk
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hnk⟩
  · intro ij hij
    have ht := twice_shape_add_one (η := η) ij
    have hn : 2 * lkjPartialCorrelationShape p η ij = D - ij.1.2.val - 1 := by
      dsimp only [D]
      linarith
    rw [ht, hn]

private theorem integral_cholesky_sq (hη : 0 < η) (i k : Fin p) (hk : k ≤ i) :
    ∫ z, partialCorrelationCholesky z i k ^ 2 ∂coordinateProduct p η =
      if k < i then 1 / (2 * η + p - 1)
      else (2 * η + p - 1 - i.val) / (2 * η + p - 1) := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  have hp : (∫ z, partialCorrelationCholesky z i k ^ 2 ∂coordinateProduct p η) =
      ∏ ij, ∫ x, entryFactor i k ij x ^ 2 ∂coordinateLaw η ij := by
    rw [← integral_fintype_prod_eq_prod (fun ij x ↦ entryFactor i k ij x ^ 2)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ by
      simp only
      rw [Finset.prod_pow, prod_entryFactor z i k hk]
  rw [hp]
  simp_rw [integral_entryFactor_sq hη]
  rw [Finset.prod_mul_distrib]
  have hr : (∏ ij : strictLowerTriangle p,
      if ij.1.1 = i ∧ ij.1.2 < k then
        (2 * lkjPartialCorrelationShape p η ij) /
          (2 * lkjPartialCorrelationShape p η ij + 1) else 1) =
      (2 * η + p - 1 - k.val) / (2 * η + p - 1) := by
    rw [← Finset.prod_filter, residual_moment_product hη i k hk]
  rw [hr]
  by_cases hki : k < i
  · simp only [hki, ↓reduceIte]
    have heq (ij : strictLowerTriangle p) :
        (ij.1.1 = i ∧ ij.1.2 = k) ↔ ij = ⟨(i, k), hki⟩ := by
      simp only [Subtype.ext_iff, Prod.ext_iff]
    simp_rw [heq]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [twice_shape_add_one]
    have hd : 2 * η + p - 1 - k.val ≠ 0 := by
      have := lkjPartialCorrelationShape_pos hη ⟨(i, k), hki⟩
      rw [← twice_shape_add_one ⟨(i, k), hki⟩]
      positivity
    field_simp
  · have he : k = i := le_antisymm hk (le_of_not_gt hki)
    subst k
    have hnone : ∀ ij : strictLowerTriangle p, ¬(ij.1.1 = i ∧ ij.1.2 = i) := by
      intro ij h
      have := ij.2
      simp_all
    simp [hnone]

private theorem integral_cholesky_sq_mul_sq (hη : 0 < η) {i j : Fin p} (hij : i ≠ j)
    (k : Fin p) (hki : k ≤ i) (hkj : k ≤ j) :
    (∫ z, partialCorrelationCholesky z i k ^ 2 * partialCorrelationCholesky z j k ^ 2
      ∂coordinateProduct p η) =
      (∫ z, partialCorrelationCholesky z i k ^ 2 ∂coordinateProduct p η) *
        (∫ z, partialCorrelationCholesky z j k ^ 2 ∂coordinateProduct p η) := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  have he (z : strictLowerTriangle p → ℝ) :
      partialCorrelationCholesky z i k ^ 2 * partialCorrelationCholesky z j k ^ 2 =
        ∏ ij, entryFactor i k ij (z ij) ^ 2 * entryFactor j k ij (z ij) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
      prod_entryFactor z i k hki, prod_entryFactor z j k hkj]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod
    (fun ij x ↦ entryFactor i k ij x ^ 2 * entryFactor j k ij x ^ 2)]
  have hf (ij : strictLowerTriangle p) :
      (∫ x, entryFactor i k ij x ^ 2 * entryFactor j k ij x ^ 2 ∂coordinateLaw η ij) =
        (∫ x, entryFactor i k ij x ^ 2 ∂coordinateLaw η ij) *
          (∫ x, entryFactor j k ij x ^ 2 ∂coordinateLaw η ij) := by
    by_cases hi : ij.1.1 = i
    · have hj : ij.1.1 ≠ j := hi ▸ hij
      simp [entryFactor_of_other_row j k ij hj]
    · simp [entryFactor_of_other_row i k ij hi]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, ← integral_fintype_prod_eq_prod,
    ← integral_fintype_prod_eq_prod]
  congr 1 <;> apply integral_congr_ae <;>
    exact Filter.Eventually.of_forall fun z ↦ by
      simp only [Finset.prod_pow, prod_entryFactor z i k hki, prod_entryFactor z j k hkj]

private theorem integral_cholesky_mul_zero (hη : 0 < η) {i j : Fin p} (hji : j < i)
    (k : Fin p) (hkj : k ≤ j) :
    ∫ z, partialCorrelationCholesky z i k * partialCorrelationCholesky z j k
      ∂coordinateProduct p η = 0 := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  have hki : k < i := hkj.trans_lt hji
  have he (z : strictLowerTriangle p → ℝ) :
      partialCorrelationCholesky z i k * partialCorrelationCholesky z j k =
        ∏ ij, entryFactor i k ij (z ij) * entryFactor j k ij (z ij) := by
    rw [Finset.prod_mul_distrib, prod_entryFactor z i k hki.le, prod_entryFactor z j k hkj]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod
    (fun ij x ↦ entryFactor i k ij x * entryFactor j k ij x)]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨(i, k), hki⟩ : strictLowerTriangle p))
  simp only [entryFactor, hji.ne', true_and, and_self, lt_self_iff_false, ↓reduceIte,
    mul_one, false_and]
  simpa using integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    (r := 0) (lkjPartialCorrelationShape_pos hη ⟨(i, k), hki⟩)
    (by simpa using lkjPartialCorrelationShape_pos hη ⟨(i, k), hki⟩) 1

private theorem integral_cholesky_cross_zero (hη : 0 < η) {i j k l : Fin p}
    (hji : j < i) (hkl : k < l) (hlj : l ≤ j) :
    ∫ z, (partialCorrelationCholesky z i k * partialCorrelationCholesky z j k) *
      (partialCorrelationCholesky z i l * partialCorrelationCholesky z j l)
      ∂coordinateProduct p η = 0 := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  have hki : k < i := hkl.trans_le (hlj.trans hji.le)
  have he (z : strictLowerTriangle p → ℝ) :
      (partialCorrelationCholesky z i k * partialCorrelationCholesky z j k) *
        (partialCorrelationCholesky z i l * partialCorrelationCholesky z j l) =
        ∏ ij, (entryFactor i k ij (z ij) * entryFactor j k ij (z ij)) *
          (entryFactor i l ij (z ij) * entryFactor j l ij (z ij)) := by
    simp only [Finset.prod_mul_distrib]
    rw [prod_entryFactor z i k hki.le, prod_entryFactor z j k (hkl.le.trans hlj),
      prod_entryFactor z i l (hlj.trans hji.le), prod_entryFactor z j l hlj]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun ij x ↦
    (entryFactor i k ij x * entryFactor j k ij x) *
      (entryFactor i l ij x * entryFactor j l ij x))]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨(i, k), hki⟩ : strictLowerTriangle p))
  simp only [entryFactor, hji.ne', hkl.ne, hkl, true_and, and_self, lt_self_iff_false,
    ↓reduceIte, mul_one, false_and, one_mul]
  simpa only [pow_one, Real.sqrt_eq_rpow, Nat.not_even_one, ↓reduceIte] using
    integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
      (r := 1 / 2) (lkjPartialCorrelationShape_pos hη ⟨(i, k), hki⟩)
      (by have := lkjPartialCorrelationShape_pos hη ⟨(i, k), hki⟩; positivity) 1

private theorem memLp_cholesky_entry (hη : 0 < η) (i k : Fin p) (q : ENNReal) :
    MemLp (fun z ↦ partialCorrelationCholesky z i k) q (coordinateProduct p η) := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  have hm : AEStronglyMeasurable (fun z ↦ partialCorrelationCholesky z i k)
      (coordinateProduct p η) :=
    (((continuous_apply k).comp ((continuous_apply i).comp
      continuous_partialCorrelationCholesky)).measurable).aestronglyMeasurable
  apply MemLp.of_bound hm 1
  have hz : ∀ᵐ z ∂coordinateProduct p η, ∀ ij, |z ij| ≤ 1 := by
    apply ae_all_iff.mpr
    intro ij
    exact (measurePreserving_eval (coordinateLaw η) ij).quasiMeasurePreserving.ae
      (coordinate_ae_abs_le_one ij)
  filter_upwards [hz] with z hz
  by_cases hk : k ≤ i
  · rw [← prod_entryFactor z i k hk, Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _)
      (fun ij _ ↦ abs_entryFactor_le_one i k ij (hz ij))
  · simp [partialCorrelationCholesky_apply_of_lt z (lt_of_not_ge hk)]

/-- The square of every entry in the independent centered-Beta partial-correlation
construction is integrable for positive shape. -/
theorem integrable_sq_partialCorrelationGram (hη : 0 < η) (i j : Fin p) :
    Integrable (fun z : strictLowerTriangle p → ℝ ↦ partialCorrelationGram z i j ^ 2)
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  have hsum : MemLp (fun z ↦ ∑ k ∈ Finset.Iic j,
      partialCorrelationCholesky z i k * partialCorrelationCholesky z j k) 2
      (coordinateProduct p η) :=
    memLp_finsetSum _ fun k _ ↦
      (memLp_cholesky_entry hη i k ∞).mul (memLp_cholesky_entry hη j k 2)
  simp_rw [← partialCorrelationGram_apply_eq_sum_Iic] at hsum
  exact hsum.integrable_sq

private theorem integral_gram_entry_sq_eq_sum (hη : 0 < η) {i j : Fin p} (hji : j < i) :
    (∫ z, partialCorrelationGram z i j ^ 2 ∂coordinateProduct p η) =
      ∑ k ∈ Finset.Iic j,
        (∫ z, partialCorrelationCholesky z i k ^ 2 ∂coordinateProduct p η) *
          (∫ z, partialCorrelationCholesky z j k ^ 2 ∂coordinateProduct p η) := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  let T (k : Fin p) (z : strictLowerTriangle p → ℝ) :=
    partialCorrelationCholesky z i k * partialCorrelationCholesky z j k
  have hT (k : Fin p) : MemLp (T k) 2 (coordinateProduct p η) :=
    (memLp_cholesky_entry hη i k ∞).mul (memLp_cholesky_entry hη j k 2)
  have hexp : (∫ z, partialCorrelationGram z i j ^ 2 ∂coordinateProduct p η) =
      ∑ k ∈ Finset.Iic j, ∑ l ∈ Finset.Iic j,
        ∫ z, T k z * T l z ∂coordinateProduct p η := by
    have he : (fun z ↦ partialCorrelationGram z i j ^ 2) =
        (fun z ↦ ∑ k ∈ Finset.Iic j, ∑ l ∈ Finset.Iic j, T k z * T l z) := by
      funext z
      rw [partialCorrelationGram_apply_eq_sum_Iic, pow_two, Finset.sum_mul_sum]
    rw [he, integral_finsetSum (f := fun k z ↦ ∑ l ∈ Finset.Iic j, T k z * T l z)
      _ (fun k _ ↦ integrable_finsetSum (f := fun l z ↦ T k z * T l z) _
        (fun l _ ↦ (hT k).integrable_mul (hT l)))]
    exact Finset.sum_congr rfl fun k _ ↦
      integral_finsetSum _ (fun l _ ↦ (hT k).integrable_mul (hT l))
  rw [hexp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · calc
      _ = ∫ z, partialCorrelationCholesky z i k ^ 2 *
          partialCorrelationCholesky z j k ^ 2 ∂coordinateProduct p η := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by dsimp only [T]; ring
      _ = _ := integral_cholesky_sq_mul_sq hη hji.ne' k
        ((Finset.mem_Iic.mp hk).trans hji.le) (Finset.mem_Iic.mp hk)
  · intro l hl hne
    rcases lt_or_gt_of_ne hne with h | h
    · simpa only [mul_comm] using
        integral_cholesky_cross_zero hη hji h (Finset.mem_Iic.mp hk)
    · exact integral_cholesky_cross_zero hη hji h (Finset.mem_Iic.mp hl)
  · exact fun h ↦ (h hk).elim

private theorem integral_gram_entry_sq_of_lt (hη : 0 < η) {i j : Fin p} (hji : j < i) :
    ∫ z, partialCorrelationGram z i j ^ 2 ∂coordinateProduct p η =
      1 / (2 * η + p - 1) := by
  rw [integral_gram_entry_sq_eq_sum hη hji, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  rw [integral_cholesky_sq hη i j hji.le, integral_cholesky_sq hη j j le_rfl]
  simp only [hji, ↓reduceIte, lt_self_iff_false]
  have hs : (∑ k ∈ Finset.Iio j,
      (∫ z, partialCorrelationCholesky z i k ^ 2 ∂coordinateProduct p η) *
        (∫ z, partialCorrelationCholesky z j k ^ 2 ∂coordinateProduct p η)) =
      j.val * (1 / (2 * η + p - 1)) ^ 2 := by
    have hc (k : Fin p) (hk : k ∈ Finset.Iio j) :
        (∫ z, partialCorrelationCholesky z i k ^ 2 ∂coordinateProduct p η) *
          (∫ z, partialCorrelationCholesky z j k ^ 2 ∂coordinateProduct p η) =
            (1 / (2 * η + p - 1)) ^ 2 := by
      have hkj := Finset.mem_Iio.mp hk
      rw [integral_cholesky_sq hη i k (hkj.le.trans hji.le),
        integral_cholesky_sq hη j k hkj.le]
      simp only [hkj, hkj.trans hji, ↓reduceIte, pow_two]
    rw [Finset.sum_congr rfl hc]
    simp [Fin.card_Iio, nsmul_eq_mul]
  rw [hs]
  have hd : 2 * η + p - 1 ≠ 0 := by
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have hd : 0 < 2 * η + p - 1 := by linarith
    exact hd.ne'
  field_simp [hd]
  ring

private theorem integral_gram_entry_zero_of_lt (hη : 0 < η) {i j : Fin p} (hji : j < i) :
    ∫ z, partialCorrelationGram z i j ∂coordinateProduct p η = 0 := by
  let (ij : strictLowerTriangle p) : IsProbabilityMeasure (coordinateLaw η ij) :=
    coordinate_probability hη ij
  simp_rw [partialCorrelationGram_apply_eq_sum_Iic]
  rw [integral_finsetSum (f := fun k z ↦
    partialCorrelationCholesky z i k * partialCorrelationCholesky z j k) _ (fun k _ ↦
    (memLp_cholesky_entry hη i k 2).integrable_mul (memLp_cholesky_entry hη j k 2))]
  apply Finset.sum_eq_zero
  intro k hk
  exact integral_cholesky_mul_zero hη hji k (Finset.mem_Iic.mp hk)

/-- Every off-diagonal entry in the independent centered-Beta partial-correlation
construction has second moment `1 / (2 * η + p - 1)`. -/
theorem integral_sq_partialCorrelationGram (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    ∫ z : strictLowerTriangle p → ℝ, partialCorrelationGram z i j ^ 2
      ∂(Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) =
        1 / (2 * η + p - 1) := by
  rcases lt_or_gt_of_ne hij with h | h
  · calc
      _ = ∫ z, partialCorrelationGram z j i ^ 2 ∂coordinateProduct p η := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ congrArg (fun x : ℝ ↦ x ^ 2)
          (by simpa only [star_trivial] using
            (posSemidef_partialCorrelationGram z).isHermitian.apply j i)
      _ = _ := integral_gram_entry_sq_of_lt hη h
  · exact integral_gram_entry_sq_of_lt hη h

/-- Every off-diagonal entry in the independent centered-Beta partial-correlation
construction has variance `1 / (2 * η + p - 1)`. -/
theorem variance_partialCorrelationGram (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) :
    variance (fun z : strictLowerTriangle p → ℝ ↦ partialCorrelationGram z i j)
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) =
        1 / (2 * η + p - 1) := by
  have hm : AEMeasurable (fun z ↦ partialCorrelationGram z i j) (coordinateProduct p η) :=
    (((continuous_apply j).comp ((continuous_apply i).comp
      continuous_partialCorrelationGram)).measurable).aemeasurable
  have hmean : (∫ z, partialCorrelationGram z i j ∂coordinateProduct p η) = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · have he : (fun z : strictLowerTriangle p → ℝ ↦ partialCorrelationGram z i j) =
          (fun z ↦ partialCorrelationGram z j i) := by
        funext z
        simpa only [star_trivial] using (posSemidef_partialCorrelationGram z).isHermitian.apply j i
      rw [he]
      exact integral_gram_entry_zero_of_lt hη h
    · exact integral_gram_entry_zero_of_lt hη h
  rw [variance_of_integral_eq_zero hm hmean]
  exact integral_sq_partialCorrelationGram hη hij

end TauCeti.Probability
