/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HardThreshold
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
public import TauCeti.Probability.Moments.CenteredTruncation

/-!
# Bounded centered approximation of Wigner off-diagonal entries

Replacing the upper entries by their centered truncations gives bounded centered entries
without changing their independence or identical distribution. The expected normalized squared
Frobenius error is at most the discarded second absolute moment when the upper entries
have a common centered, square-integrable law on a probability space.

The diagonal is kept unchanged: it needs no moment assumption and may depend on the upper
entries. Independence is needed only to assert independence of the approximating coordinates,
and is not used in the error estimates. This is the bounded-approximation reduction used when
extending the moment method to finite-second-moment entry laws.

For zero-diagonal corners, the matrix of discarded entries is the entrywise hard threshold
of the original corner at the normalized cutoff.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1 and Lemma 2.1.19.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology NNReal Matrix.Norms.Frobenius

namespace TauCeti.Probability

section HardThreshold

open Set

variable {Ω : Type*} {ξ : StrictUpper → Ω → ℂ}

/-- The discarded part of a zero-diagonal Wigner corner is exactly the entrywise
hard threshold at the cutoff divided by the square root of the dimension. -/
theorem wignerMatrix_zero_sub_indicator_eq_hardThreshold {n : ℕ}
    (r : ℝ≥0) (ω : Ω) :
    wignerMatrix ξ (fun _ _ ↦ 0) n ω -
      wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ r}.indicator (ξ ij)) (fun _ _ ↦ 0) n ω =
    (wignerMatrix ξ (fun _ _ ↦ 0) n ω).hardThreshold (r / Real.sqrt n) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.hardThreshold_apply]
  simp only [wignerMatrix_sub, Matrix.hardThreshold_apply,
    div_lt_norm_wignerMatrix_apply_iff _ _ _ hij]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, min_eq_left h.le, max_eq_right h.le,
      indicator_apply, mem_ofPred_eq, ← not_lt, ite_not]
    split_ifs <;> simp
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, min_eq_right h.le, max_eq_left h.le,
      indicator_apply, mem_ofPred_eq, ← not_lt, ite_not]
    split_ifs <;> simp

end HardThreshold

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Truncating and centering upper coordinates preserves their joint independence with the
unchanged diagonal coordinates. -/
theorem _root_.ProbabilityTheory.iIndepFun.wignerMatrix_centeredTruncation
    (h : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P) (R : ℝ≥0) :
    iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (fun ij ↦ centeredTruncation (ξ ij) P R) (fun i ω ↦ (η i ω : ℂ)) k) P := by
  let g (k : StrictUpper ⊕ ℕ) : ℂ → ℂ := match k with
    | .inl ij => fun z ↦ {z | ‖z‖ ≤ R}.indicator id z -
        ∫ ω, {ω | ‖ξ ij ω‖ ≤ R}.indicator (ξ ij) ω ∂P
    | .inr _ => id
  have hg (k) : Measurable (g k) := by
    cases k
    · exact (measurable_id.indicator
        (measurableSet_le measurable_norm measurable_const)).sub measurable_const
    · exact measurable_id
  convert h.comp g hg using 1
  funext k ω
  cases k <;> simp only [g, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    centeredTruncation_def, Set.indicator_apply, Set.mem_ofPred_eq, id_eq]

end TauCeti.Probability

namespace TauCeti

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}

/-- Every normalized entry of a zero-diagonal centered truncated Wigner corner on a
probability space has norm at most twice the cutoff divided by the square root of the dimension. -/
theorem norm_wignerMatrix_centeredTruncation_zero_apply_le [IsProbabilityMeasure P] {n : ℕ}
    (R : ℝ≥0) (ω : Ω) (i j : Fin n) :
    ‖wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) (fun _ _ ↦ 0) n ω i j‖ ≤
      2 * (R : ℝ) / Real.sqrt n := by
  by_cases h : i = j
  · subst j
    simpa only [wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, norm_zero] using
      (by positivity : 0 ≤ 2 * (R : ℝ) / Real.sqrt n)
  · rw [norm_wignerMatrix_apply_of_ne _ _ _ h, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (norm_centeredTruncation_le R ω) (Real.sqrt_nonneg _)

/-- In a zero-diagonal centered truncated Wigner corner on a probability space with
square-integrable upper entries, the absolute entry moment of order `k+2` is bounded
by the upper-entry second-moment bound divided by the dimension, times `(2 * R / √n)^k`. -/
theorem integral_norm_wignerMatrix_centeredTruncation_zero_apply_pow_le
    [IsProbabilityMeasure P] {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hLp : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) 2 P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P ≤ M)
    (R : ℝ≥0) (i j : Fin n) (k : ℕ) :
    ∫ ω, ‖wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R)
      (fun _ _ ↦ 0) n ω i j‖ ^ (k + 2) ∂P ≤
      (2 * (R : ℝ) / Real.sqrt n) ^ k * (M / n) := by
  have hupper (ij : StrictUpper) (hij : ij.val.2 < n) :
      ∫ ω, ‖centeredTruncation (ξ ij) P R ω‖ ^ (k + 2) ∂P ≤ (2 * (R : ℝ)) ^ k * M := by
    exact ((hLp ij hij).integral_norm_centeredTruncation_pow_le R k).trans
      (mul_le_mul_of_nonneg_left (hξ ij hij) (by positivity))
  have hdiag (i : ℕ) (_ : i < n) :
      ∫ _ : Ω, ‖(0 : ℝ)‖ ^ (k + 2) ∂P ≤ (2 * (R : ℝ)) ^ k * M := by
    simpa only [norm_zero, zero_pow (Nat.succ_ne_zero (k + 1)), integral_zero] using
      mul_nonneg (by positivity) hM
  refine (integral_norm_wignerMatrix_apply_pow_le hupper hdiag i j).trans_eq ?_
  rw [pow_add, inv_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_pow]
  ring

/-- In a zero-diagonal centered truncated Wigner corner on a probability space, if the upper
entries share a square-integrable law, the absolute entry moment of order `k+2` is bounded by
`(2 * R / √n)^k` times the common second moment divided by the dimension. -/
theorem integral_norm_wignerMatrix_centeredTruncation_zero_apply_pow_le_of_identDistrib
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {X : Ω' → ℂ}
    [IsProbabilityMeasure P] {n : ℕ}
    (hid : ∀ ij : StrictUpper, ij.val.2 < n → IdentDistrib (ξ ij) X P Q)
    (hX : MemLp X 2 Q) (R : ℝ≥0) (i j : Fin n) (k : ℕ) :
    ∫ ω, ‖wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R)
      (fun _ _ ↦ 0) n ω i j‖ ^ (k + 2) ∂P ≤
      (2 * (R : ℝ) / Real.sqrt n) ^ k * ((∫ ω, ‖X ω‖ ^ 2 ∂Q) / n) :=
  integral_norm_wignerMatrix_centeredTruncation_zero_apply_pow_le
    (integral_nonneg fun _ ↦ sq_nonneg _)
    (fun ij hij ↦ (hid ij hij).symm.memLp_snd hX)
    (fun ij hij ↦ ((hid ij hij).comp
      (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2))).integral_eq.le) R i j k

end TauCeti

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

variable {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
  [IsProbabilityMeasure P] {X : Ω' → ℂ} (hX : MemLp X 2 Q)
  (hmean : ∫ ω, X ω ∂Q = 0) (hd : ∀ ij, IdentDistrib (ξ ij) X P Q)

include hd hX

/-- The squared Frobenius error of bounded centered off-diagonal approximation is integrable,
regardless of the diagonal law. -/
theorem integrable_norm_wignerMatrix_sub_centeredTruncation_sq (R : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η n ω‖ ^ 2) P := by
  simp_rw [wignerMatrix_sub, sub_self]
  exact integrable_norm_wignerMatrix_sq
    (fun ij _ ↦ ((hd ij).symm.memLp_snd hX).sub
      (((hd ij).symm.memLp_snd hX).aestronglyMeasurable.memLp_centeredTruncation R))
    (fun _ _ ↦ memLp_const 0)

include hmean

/-- Uniform normalized mean-square approximation by bounded centered upper entries.
For upper entries with a common centered, square-integrable law on a probability space,
the bound is the second absolute moment discarded outside the cutoff. -/
theorem inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le
    (R : ℝ≥0) (n : ℕ) :
    (n + 1 : ℝ)⁻¹ * ∫ ω, ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η (n + 1) ω‖ ^ 2 ∂P ≤
        ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂Q := by
  have hm (ij : StrictUpper) : MemLp (fun ω ↦ ξ ij ω - centeredTruncation (ξ ij) P R ω) 2 P :=
    ((hd ij).symm.memLp_snd hX).sub
      (((hd ij).symm.memLp_snd hX).aestronglyMeasurable.memLp_centeredTruncation R)
  rw [integral_norm_wignerMatrix_sub_sq hm
    (fun ij ↦ (((hd ij).sub_centeredTruncation R).comp
      (measurable_norm.pow_const 2)).integral_eq)]
  have : IsProbabilityMeasure Q := ⟨by
    simpa only [Set.preimage_univ, measure_univ] using
      ((hd ⟨(0, 1), by decide⟩).measure_mem_eq (s := Set.univ) MeasurableSet.univ).symm⟩
  have he : 0 ≤ ∫ ω, ‖X ω - centeredTruncation X Q R ω‖ ^ 2 ∂Q :=
    integral_nonneg fun _ ↦ sq_nonneg _
  calc
    _ ≤ ∫ ω, ‖X ω - centeredTruncation X Q R ω‖ ^ 2 ∂Q := by
      have hc : (n : ℝ) / (n + 1) ≤ 1 := by
        exact (div_le_one (by positivity)).mpr (by linarith)
      simpa only [div_eq_inv_mul, mul_assoc, Function.comp_def] using
        mul_le_of_le_one_left he hc
    _ ≤ _ := hX.integral_norm_sub_centeredTruncation_sq_le hmean R

end TauCeti.Probability
