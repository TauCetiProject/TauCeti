/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Lindeberg sums of Wigner matrices

The Lindeberg sum of a random square matrix integrates the squared modulus of each off-diagonal
entry above a cutoff, adds over the ordered off-diagonal pairs and divides by the dimension.
It uses nonnegative extended integrals, so an infinite discarded second moment gives an infinite
sum. It vanishes exactly when the off-diagonal squared norms stay almost everywhere below the
cutoff, and is finite exactly when all discarded second moments are integrable.

For Wigner matrices the sum does not depend on the diagonal. In unnormalized coordinates each
strict upper entry contributes twice and the divisor is the square of the matrix size.
Square-integrable upper entries give a finite sum.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), §2.1, Theorem 2.4.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped BigOperators NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section LindebergSum

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Norm E]

/-- Integrate the squared modulus above the cutoff, sum over ordered off-diagonal pairs and
divide by the dimension `N`. The sum is infinite if any discarded second moment is infinite.
For Wigner matrices the entries already include the normalization, so the cutoff `r` corresponds
to an unnormalized norm cutoff `√(r * N)` in dimension `N`. -/
def wignerLindebergSum (A : Ω → Matrix ι ι E) (P : Measure Ω)
    (r : ℝ≥0) : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i : ι, ∑ j : {j : ι // j ≠ i},
    ∫⁻ ω, ENNReal.ofReal
      ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω) ∂P

/-- The entrywise formula for the normalized Lindeberg sum. -/
theorem wignerLindebergSum_def (A : Ω → Matrix ι ι E) (P : Measure Ω)
    (r : ℝ≥0) :
    wignerLindebergSum A P r =
      (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i : ι, ∑ j : {j : ι // j ≠ i},
        ∫⁻ ω, ENNReal.ofReal
          ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω) ∂P := by
  rw [wignerLindebergSum]

/-- Almost-everywhere equality of the off-diagonal entries preserves the Lindeberg sum. -/
theorem wignerLindebergSum_congr_ae
    {A B : Ω → Matrix ι ι E} (r : ℝ≥0)
    (h : ∀ i j, j ≠ i → (fun ω ↦ A ω j i) =ᵐ[P] (fun ω ↦ B ω j i)) :
    wignerLindebergSum A P r = wignerLindebergSum B P r := by
  simp only [wignerLindebergSum_def]
  congr 1
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ lintegral_congr_ae ?_
  filter_upwards [h i j j.property] with ω hω
  simp [Set.indicator_apply, hω]

/-- Raising the squared-modulus cutoff decreases the Lindeberg sum. -/
theorem wignerLindebergSum_antitone (A : Ω → Matrix ι ι E) :
    Antitone (wignerLindebergSum A P) := by
  intro r s hrs
  simp only [wignerLindebergSum_def]
  refine mul_le_mul_of_nonneg_left
    (sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ lintegral_mono ?_) zero_le
  intro ω
  by_cases h : (s : ℝ) < ‖A ω j i‖ ^ 2
  · have ht : (r : ℝ) < ‖A ω j i‖ ^ 2 := (NNReal.coe_le_coe.mpr hrs).trans_lt h
    simp [h, ht]
  · simp [Set.indicator_apply, h]

/-- There are no off-diagonal terms on a subsingleton index type. -/
@[simp]
theorem wignerLindebergSum_eq_zero_of_subsingleton [Subsingleton ι]
    (A : Ω → Matrix ι ι E) (r : ℝ≥0) : wignerLindebergSum A P r = 0 := by
  have (i : ι) : IsEmpty {j : ι // j ≠ i} :=
    ⟨fun j ↦ j.property (Subsingleton.elim _ _)⟩
  simp [wignerLindebergSum_def]

omit [Fintype ι] [DecidableEq ι] in
private theorem aemeasurable_wignerLindeberg_tail (A : Ω → Matrix ι ι E) (r : ℝ≥0)
    (i j : ι) (hA : AEMeasurable (fun ω ↦ ‖A ω j i‖) P) :
    AEMeasurable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P :=
  (hA.pow_const 2).indicator₀ (nullMeasurableSet_lt aemeasurable_const (hA.pow_const 2))

/-- With a.e.-measurable off-diagonal norms, the Lindeberg sum vanishes exactly when each
off-diagonal squared norm is almost everywhere at most the cutoff. -/
theorem wignerLindebergSum_eq_zero_iff (A : Ω → Matrix ι ι E) (r : ℝ≥0)
    (hA : ∀ (i : ι) (j : {j : ι // j ≠ i}), AEMeasurable (fun ω ↦ ‖A ω j i‖) P) :
    wignerLindebergSum A P r = 0 ↔ ∀ (i : ι) (j : {j : ι // j ≠ i}),
      ∀ᵐ ω ∂P, ‖A ω j i‖ ^ 2 ≤ (r : ℝ) := by
  simp only [wignerLindebergSum_def, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top,
    false_or, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le), mem_univ, true_implies]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  rw [lintegral_eq_zero_iff' (aemeasurable_wignerLindeberg_tail A r i j (hA i j)).ennreal_ofReal]
  refine eventually_congr (.of_forall fun ω ↦ ?_)
  by_cases h : (r : ℝ) < ‖A ω j i‖ ^ 2
  · have hpos := r.coe_nonneg.trans_lt h
    simp [h, hpos.not_ge, h.not_ge]
  · simp [h, le_of_not_gt h]

/-- If the discarded second moments are integrable, the Lindeberg sum is finite. -/
theorem wignerLindebergSum_ne_top (A : Ω → Matrix ι ι E) (r : ℝ≥0)
    (hA : ∀ (i : ι) (j : {j : ι // j ≠ i}),
      Integrable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P) :
    wignerLindebergSum A P r ≠ ∞ := by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [wignerLindebergSum_def]
    refine ENNReal.mul_ne_top (by simp [Fintype.card_ne_zero]) (ENNReal.sum_ne_top.mpr fun i _ ↦
      ENNReal.sum_ne_top.mpr fun j _ ↦ ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hA i j)
      (.of_forall fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
    exact ENNReal.ofReal_ne_top

/-- If the off-diagonal squared norms are integrable, the Lindeberg sum is finite. -/
theorem wignerLindebergSum_ne_top_of_integrable_norm_sq (A : Ω → Matrix ι ι E) (r : ℝ≥0)
    (hA : ∀ (i : ι) (j : {j : ι // j ≠ i}), Integrable (fun ω ↦ ‖A ω j i‖ ^ 2) P) :
    wignerLindebergSum A P r ≠ ∞ :=
  wignerLindebergSum_ne_top A r fun i j ↦
    (hA i j).indicator₀ (nullMeasurableSet_lt aemeasurable_const (hA i j).aemeasurable)

/-- For a.e.-measurable off-diagonal norms, the Lindeberg sum is finite exactly when all
discarded second moments are integrable. -/
theorem wignerLindebergSum_ne_top_iff (A : Ω → Matrix ι ι E) (r : ℝ≥0)
    (hA : ∀ (i : ι) (j : {j : ι // j ≠ i}), AEMeasurable (fun ω ↦ ‖A ω j i‖) P) :
    wignerLindebergSum A P r ≠ ∞ ↔ ∀ (i : ι) (j : {j : ι // j ≠ i}),
      Integrable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P := by
  refine ⟨fun h i j ↦ ?_, wignerLindebergSum_ne_top A r⟩
  rw [wignerLindebergSum_def, ne_eq, ENNReal.mul_eq_top] at h
  have hs := (not_or.mp h).1
  have hj := ENNReal.sum_ne_top.mp
    (ENNReal.sum_ne_top.mp (fun htop ↦ hs ⟨by simp, htop⟩) i (mem_univ i)) j (mem_univ j)
  have htail := (aemeasurable_wignerLindeberg_tail A r i j (hA i j)).aestronglyMeasurable
  exact (lintegral_ofReal_ne_top_iff_integrable htail
    (.of_forall fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)).mp hj

/-- For integrable discarded second moments, the real value of the Lindeberg sum uses Bochner
integrals of the squared modulus above the cutoff, summed over ordered off-diagonal pairs and
divided by the matrix dimension. -/
theorem wignerLindebergSum_toReal (A : Ω → Matrix ι ι E) (r : ℝ≥0)
    (hA : ∀ (i : ι) (j : {j : ι // j ≠ i}),
      Integrable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P) :
    (wignerLindebergSum A P r).toReal =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, ∑ j : {j : ι // j ≠ i},
        ∫ ω, {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω ∂P := by
  have hnonneg (i : ι) (j : {j : ι // j ≠ i}) (ω : Ω) :
      0 ≤ {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω :=
    Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  simp_rw [wignerLindebergSum_def, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← ofReal_integral_eq_lintegral_ofReal (hA _ _) (.of_forall (hnonneg _ _))]
  rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (integral_nonneg (hnonneg _ _))]

end LindebergSum

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}

/-- The upper/lower entry tails are unchanged by replacing the real diagonal. -/
theorem wignerLindebergSum_wignerMatrix_eq_replace_diag {N : ℕ} (ξ : StrictUpper → Ω → ℂ)
    (η η' : ℕ → Ω → ℝ) (r : ℝ≥0) :
    wignerLindebergSum (wignerMatrix ξ η N) P r =
      wignerLindebergSum (wignerMatrix ξ η' N) P r := by
  apply wignerLindebergSum_congr_ae
  intro i j hij
  refine .of_forall fun ω ↦ ?_
  simp only [wignerMatrix_eq_add_diagonal ξ η N ω, wignerMatrix_eq_add_diagonal ξ η' N ω,
    Matrix.add_apply, diagonal_apply_ne _ hij, add_zero]

private theorem lintegral_indicator_norm_wignerMatrix_apply_sq_eq
    {i j : Fin (n + 1)} (h : j ≠ i) (r : ℝ≥0) :
    let u : StrictUpper := ⟨(min j.val i.val, max j.val i.val),
      min_lt_max.mpr (Fin.val_ne_of_ne h)⟩
    (∫⁻ ω, ENNReal.ofReal ({ω | (r : ℝ) < ‖wignerMatrix ξ η (n + 1) ω j i‖ ^ 2}.indicator
      (fun ω ↦ ‖wignerMatrix ξ η (n + 1) ω j i‖ ^ 2) ω) ∂P) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ ω, ENNReal.ofReal
        ({ω | (r : ℝ) * (n + 1 : ℕ) < ‖ξ u ω‖ ^ 2}.indicator (fun ω ↦ ‖ξ u ω‖ ^ 2) ω) ∂P := by
  intro u
  have hN : 0 < (n + 1 : ℝ) := by positivity
  rw [← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_congr
  intro ω
  simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ h, Nat.cast_succ,
    Set.indicator_apply, Set.mem_ofPred_eq]
  have hcut : (r : ℝ) < (n + 1 : ℝ)⁻¹ * ‖ξ u ω‖ ^ 2 ↔
      (r : ℝ) * (n + 1 : ℝ) < ‖ξ u ω‖ ^ 2 := by
    rw [← div_eq_inv_mul, lt_div_iff₀ hN]
  dsimp only [u] at hcut ⊢
  simp only [hcut]
  split_ifs
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hN,
      ← Nat.cast_succ, ENNReal.ofReal_natCast, Nat.cast_succ]
  · simp

/-- In unnormalized coordinates the Lindeberg sum is twice the sum of the discarded second
moments over the strict upper triangle, divided by the square of the dimension. -/
theorem wignerLindebergSum_wignerMatrix_eq_sum {N : ℕ} (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (r : ℝ≥0) :
    wignerLindebergSum (wignerMatrix ξ η N) P r =
      2 * (N : ℝ≥0∞)⁻¹ ^ 2 * ∑ u : StrictUpperFin N,
        ∫⁻ ω, ENNReal.ofReal ({ω | (r : ℝ) * N < ‖ξ (wignerUpperIndex u) ω‖ ^ 2}.indicator
          (fun ω ↦ ‖ξ (wignerUpperIndex u) ω‖ ^ 2) ω) ∂P := by
  cases N with
  | zero => simp
  | succ n =>
    let edge (j i : Fin (n + 1)) (h : j ≠ i) : StrictUpper :=
      ⟨(min j.val i.val, max j.val i.val), min_lt_max.mpr (Fin.val_ne_of_ne h)⟩
    let T (u : StrictUpper) := ∫⁻ ω, ENNReal.ofReal
      ({ω | (r : ℝ) * (n + 1 : ℕ) < ‖ξ u ω‖ ^ 2}.indicator (fun ω ↦ ‖ξ u ω‖ ^ 2) ω) ∂P
    let g (i j : Fin (n + 1)) := if h : j ≠ i then T (edge j i h) else 0
    have hdiag (i : Fin (n + 1)) : g i i = 0 := dite_eq_right (not_not.mpr rfl)
    have hsymm (i j : Fin (n + 1)) : g i j = g j i := by
      by_cases h : j = i
      · rw [h]
      · have he : edge j i h = edge i j (Ne.symm h) :=
          Subtype.ext (by simp [edge, min_comm, max_comm])
        simp only [g, dite_eq_left h, dite_eq_left (Ne.symm h), he]
    have hrow (i : Fin (n + 1)) :
        (∑ j : {j // j ≠ i}, T (edge j i j.property)) = ∑ j, g i j := by
      rw [Fintype.sum_eq_add_sum_subtype_ne (g i) i, hdiag, zero_add]
      exact sum_congr rfl fun j _ ↦ by simp only [g, dite_eq_left j.property]
    have hupper (u : StrictUpperFin (n + 1)) : g u.val.1 u.val.2 = T (wignerUpperIndex u) := by
      have he : edge u.val.2 u.val.1 (Fin.ne_of_lt u.property).symm = wignerUpperIndex u :=
        Subtype.ext (by simp [edge, min_eq_right u.property.le, max_eq_left u.property.le])
      simp only [g, dite_eq_left (Fin.ne_of_lt u.property).symm, he]
    have hordered : (∑ i : Fin (n + 1), ∑ j : {j // j ≠ i}, T (edge j i j.property)) =
        2 * ∑ u : StrictUpperFin (n + 1), T (wignerUpperIndex u) := by
      simp_rw [hrow]
      rw [sum_symmetric_pairs g hsymm, sum_eq_zero fun i _ ↦ hdiag i, zero_add, nsmul_eq_mul,
        Nat.cast_ofNat]
      exact congrArg (2 * ·) (sum_congr rfl fun u _ ↦ hupper u)
    simp_rw [wignerLindebergSum_def, Fintype.card_fin]
    calc
      _ = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ i : Fin (n + 1), ∑ j : {j // j ≠ i}, T (edge j i j.property)) := by
        simp_rw [fun (i : Fin (n + 1)) (j : {j // j ≠ i}) ↦
          lintegral_indicator_norm_wignerMatrix_apply_sq_eq (ξ := ξ) (η := η) (P := P) j.property r]
        simp only [← mul_sum]
        rfl
      _ = _ := by rw [hordered, pow_two]; ac_rfl

/-- Square-integrable upper entries in the corner of size `n` give a finite Lindeberg sum,
whatever the diagonal. -/
theorem wignerLindebergSum_wignerMatrix_ne_top
    (hLp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) 2 P) (η : ℕ → Ω → ℝ) (r : ℝ≥0) :
    wignerLindebergSum (wignerMatrix ξ η n) P r ≠ ∞ := by
  rw [wignerLindebergSum_wignerMatrix_eq_replace_diag ξ η (fun _ _ ↦ 0)]
  exact wignerLindebergSum_ne_top_of_integrable_norm_sq _ r fun i j ↦
    (memLp_wignerMatrix_apply hLp (fun _ _ ↦ MemLp.zero') j.val i).integrable_norm_pow
      (by decide)

end TauCeti.Probability
