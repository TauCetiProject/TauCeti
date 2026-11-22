/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
public import TauCeti.Probability.Moments.CenteredTruncation

/-!
# Bounded centered approximation of Wigner off-diagonal entries

Replacing the upper entries by their centered truncations gives bounded entries without changing
their independence or identical distribution. On a probability space, the truncations of almost
everywhere strongly measurable upper entries have zero mean. The expected normalized squared
Frobenius error is at most the discarded second absolute moment when the upper entries of the
corner have a common centered, square-integrable law on a probability space.

The diagonal is kept unchanged: it needs no moment assumption and may depend on the upper
entries. Independence is needed only to assert independence of the approximating coordinates,
and is not used in the error estimates. This is the bounded-approximation reduction used when
extending the moment method to finite-second-moment entry laws.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1 and Lemma 2.1.19.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology NNReal Matrix.Norms.Frobenius

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Truncating and centering upper coordinates preserves their joint independence with the
unchanged diagonal coordinates. -/
theorem _root_.ProbabilityTheory.iIndepFun.wignerMatrix_centeredTruncation
    (h : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P) (R : ℝ≥0) :
    iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (fun ij ↦ centeredTruncation (ξ ij) P R) (fun i ω ↦ (η i ω : ℂ)) k) P := by
  choose g hg hgξ using fun ij ↦ exists_measurable_comp_eq_centeredTruncation (ξ ij) P R
  convert h.comp (fun k ↦ Sum.elim g (fun _ ↦ id) k) (fun k ↦ by
    cases k with
    | inl ij => exact hg ij
    | inr _ => exact measurable_id) using 1
  funext k
  cases k <;> simp only [Sum.elim_inl, Sum.elim_inr, hgξ, Function.id_comp]

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

/-- The squared Frobenius error of bounded centered off-diagonal approximation is integrable on a
finite measure space when the upper entries of the corner are square-integrable, regardless of the
diagonal law. -/
theorem integrable_norm_wignerMatrix_sub_centeredTruncation_sq [IsFiniteMeasure P] {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) 2 P) (R : ℝ≥0) :
    Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η n ω‖ ^ 2) P := by
  simp_rw [wignerMatrix_sub, sub_self]
  exact integrable_norm_wignerMatrix_sq
    (fun ij hij ↦ (hξ ij hij).sub ((hξ ij hij).aestronglyMeasurable.memLp_centeredTruncation R))
    (fun _ _ ↦ memLp_const 0)

variable {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {X : Ω' → ℂ}

/-- Uniform normalized mean-square approximation by bounded centered upper entries.
For upper entries of the corner with a common centered, square-integrable law, on a probability
space, the bound is the second absolute moment discarded outside the cutoff. -/
theorem inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le [IsProbabilityMeasure P]
    (hX : MemLp X 2 Q) (hmean : ∫ ω, X ω ∂Q = 0) (R : ℝ≥0) (n : ℕ)
    (hd : ∀ ij : StrictUpper, ij.val.2 < n + 1 → IdentDistrib (ξ ij) X P Q) :
    (n + 1 : ℝ)⁻¹ * ∫ ω, ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η (n + 1) ω‖ ^ 2 ∂P ≤
        ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂Q := by
  have hm (ij : StrictUpper) (hij : ij.val.2 < n + 1) :
      Integrable (fun ω ↦ ‖ξ ij ω - centeredTruncation (ξ ij) P R ω‖ ^ 2) P := by
    have h := ((hd ij hij).symm.memLp_snd hX).sub
      (((hd ij hij).symm.memLp_snd hX).aestronglyMeasurable.memLp_centeredTruncation R)
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  rw [integral_norm_wignerMatrix_sub_sq hm fun ij hij ↦
    (((hd ij hij).sub_centeredTruncation R).comp (measurable_norm.pow_const 2)).integral_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- A corner of size one has no upper entries, so the error vanishes.
    simpa using integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  have : IsProbabilityMeasure Q := by
    have h := hd ⟨(0, 1), by decide⟩ (by dsimp only; omega)
    exact (h.hasLaw (hasLaw_map h.aemeasurable_fst)).isProbabilityMeasure
  have he : 0 ≤ ∫ ω, ‖X ω - centeredTruncation X Q R ω‖ ^ 2 ∂Q :=
    integral_nonneg fun _ ↦ sq_nonneg _
  calc
    _ ≤ ∫ ω, ‖X ω - centeredTruncation X Q R ω‖ ^ 2 ∂Q := by
      have hc : (n : ℝ) / (n + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      simpa only [div_eq_inv_mul, mul_assoc, Function.comp_def] using
        mul_le_of_le_one_left he hc
    _ ≤ _ := hX.integral_norm_sub_centeredTruncation_sq_le hmean R

end TauCeti.Probability
