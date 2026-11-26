/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# The 2-norm unitalization of a completely positive contraction into a matrix algebra

Let `φ : A → M_k` be a completely positive contraction on a nonzero unital C⋆-algebra and
`h = φ(1)^{1/2}`. The Choi–Effros factorization
(`CompletelyPositiveMap.exists_unital_eq_sqrt_mul_mul_sqrt`) writes `φ(a) = h ψ(a) h` with `ψ`
unital completely positive. If `tr_k φ(1) ≥ 1 - δ`, then `ψ` is close to `φ` in the normalized
2-norm: `‖ψ(x) - φ(x)‖₂ ≤ 2‖x‖δ^{1/2}`, from `‖1 - h‖₂² ≤ 1 - tr_k φ(1)`, which holds because
`(1 - h)² ≤ 1 - h²` for `0 ≤ h ≤ 1` (`CStarMatrix.normalizedTwoNorm_sub_one_sq_le`).
Consequently `|tr_k ψ(x) - tr_k φ(x)| ≤ 2‖x‖δ^{1/2}` and
`‖ψ(ab) - ψ(a)ψ(b)‖₂ ≤ ‖φ(ab) - φ(a)φ(b)‖₂ + 6‖a‖‖b‖δ^{1/2}`.

## Main statements

* `CStarMatrix.normalizedTwoNorm_map_mul_sub_le_of_normalizedTwoNorm_sub_le`: maps that are close
  in the 2-norm have close multiplicativity defects.
* `CompletelyPositiveMap.exists_unital_normalizedTwoNorm_sub_le`: the 2-norm unitalization, with
  its trace and product estimates.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Lemma 2.7.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace CStarMatrix

variable {n : Type*} [Fintype n]

/-- **Close maps have close multiplicativity defects.** If `φ, ψ : A → M_k` are contractive and
`‖ψ(x) - φ(x)‖₂ ≤ c‖x‖` for every `x`, then
`‖ψ(ab) - ψ(a)ψ(b)‖₂ ≤ ‖φ(ab) - φ(a)φ(b)‖₂ + 3c‖a‖‖b‖`. -/
theorem normalizedTwoNorm_map_mul_sub_le_of_normalizedTwoNorm_sub_le {A : Type*}
    [NonUnitalNormedRing A] {φ ψ : A → CStarMatrix n n ℂ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (hψ : ∀ a, ‖ψ a‖ ≤ ‖a‖) {c : ℝ} (h : ∀ a, normalizedTwoNorm (ψ a - φ a) ≤ c * ‖a‖)
    (a b : A) :
    normalizedTwoNorm (ψ (a * b) - ψ a * ψ b) ≤
      normalizedTwoNorm (φ (a * b) - φ a * φ b) + 3 * c * ‖a‖ * ‖b‖ := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0` the hypothesis forces `A = 0` and `ψ 0 = φ 0`.
    have h0 (x : A) : x = 0 := by
      by_contra hx
      have := (normalizedTwoNorm_nonneg _).trans (h x)
      nlinarith [norm_pos_iff.2 hx]
    have hψφ : ψ 0 = φ 0 := sub_eq_zero.1 <| (normalizedTwoNorm_eq_zero_iff).1 <|
      le_antisymm ((h 0).trans (by simp)) (normalizedTwoNorm_nonneg _)
    simp [h0 a, h0 b, hψφ]
  have e : ψ (a * b) - ψ a * ψ b = (ψ (a * b) - φ (a * b)) + (φ (a * b) - φ a * φ b) +
      ((φ a - ψ a) * φ b + ψ a * (φ b - ψ b)) := by
    noncomm_ring
  rw [e]
  have h1 : normalizedTwoNorm (ψ (a * b) - φ (a * b)) ≤ c * ‖a‖ * ‖b‖ := by
    refine (h _).trans ?_
    rw [mul_assoc c ‖a‖]
    gcongr
    exact norm_mul_le a b
  have h2 : normalizedTwoNorm ((φ a - ψ a) * φ b) ≤ c * ‖a‖ * ‖b‖ := by
    refine (normalizedTwoNorm_mul_le_normalizedTwoNorm_mul_norm _ _).trans ?_
    rw [normalizedTwoNorm_sub_comm]
    exact mul_le_mul (h a) (hφ b) (norm_nonneg _) (by positivity)
  have h3 : normalizedTwoNorm (ψ a * (φ b - ψ b)) ≤ c * ‖a‖ * ‖b‖ := by
    refine (normalizedTwoNorm_mul_le_norm_mul_normalizedTwoNorm _ _).trans ?_
    rw [normalizedTwoNorm_sub_comm]
    calc ‖ψ a‖ * normalizedTwoNorm (ψ b - φ b) ≤ ‖a‖ * (c * ‖b‖) :=
          mul_le_mul (hψ a) (h b) (normalizedTwoNorm_nonneg _) (norm_nonneg _)
      _ = c * ‖a‖ * ‖b‖ := by ring
  calc normalizedTwoNorm ((ψ (a * b) - φ (a * b)) + (φ (a * b) - φ a * φ b) +
        ((φ a - ψ a) * φ b + ψ a * (φ b - ψ b)))
      ≤ normalizedTwoNorm (ψ (a * b) - φ (a * b)) + normalizedTwoNorm (φ (a * b) - φ a * φ b) +
        (normalizedTwoNorm ((φ a - ψ a) * φ b) + normalizedTwoNorm (ψ a * (φ b - ψ b))) :=
        (normalizedTwoNorm_add_le _ _).trans (add_le_add (normalizedTwoNorm_add_le _ _)
          (normalizedTwoNorm_add_le _ _))
    _ ≤ c * ‖a‖ * ‖b‖ + normalizedTwoNorm (φ (a * b) - φ a * φ b) +
        (c * ‖a‖ * ‖b‖ + c * ‖a‖ * ‖b‖) := by gcongr
    _ = normalizedTwoNorm (φ (a * b) - φ a * φ b) + 3 * c * ‖a‖ * ‖b‖ := by ring

end CStarMatrix

namespace CompletelyPositiveMap

open CStarMatrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **The 2-norm unitalization** (Brown, Lemma 2.7). A completely positive contraction
`φ : A → M_k` on a nonzero unital C⋆-algebra with `re tr_k φ(1) ≥ 1 - δ` factors as
`φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` and `ψ` unital completely positive, and then
`‖ψ(x) - φ(x)‖₂ ≤ 2‖x‖δ^{1/2}`, `|tr_k ψ(x) - tr_k φ(x)| ≤ 2‖x‖δ^{1/2}` and
`‖ψ(ab) - ψ(a)ψ(b)‖₂ ≤ ‖φ(ab) - φ(a)φ(b)‖₂ + 6‖a‖‖b‖δ^{1/2}`. -/
theorem exists_unital_normalizedTwoNorm_sub_le (φ : A →CP CStarMatrix n n ℂ)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) {δ : ℝ} (hδ : 1 - δ ≤ (normalizedTrace (φ 1)).re) :
    ∃ ψ : A →CP CStarMatrix n n ℂ, ψ 1 = 1 ∧
      (∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1)) ∧
      (∀ a, normalizedTwoNorm (ψ a - φ a) ≤ 2 * ‖a‖ * √δ) ∧
      (∀ a, ‖normalizedTrace (ψ a) - normalizedTrace (φ a)‖ ≤ 2 * ‖a‖ * √δ) ∧
      ∀ a b, normalizedTwoNorm (ψ (a * b) - ψ a * ψ b) ≤
        normalizedTwoNorm (φ (a * b) - φ a * φ b) + 6 * ‖a‖ * ‖b‖ * √δ := by
  obtain ⟨ψ, hψ1, hψ⟩ := exists_unital_eq_sqrt_mul_mul_sqrt φ
  have hψc (a : A) : ‖ψ a‖ ≤ ‖a‖ := by
    rcases isEmpty_or_nonempty n with hn | hn
    · have : ψ a = 0 := CStarMatrix.ext fun i ↦ isEmptyElim i
      simp [this]
    refine (CompletelyPositiveMapClass.norm_apply_le ψ a).trans
      (mul_le_of_le_one_left (norm_nonneg a) ?_)
    rw [hψ1, CStarRing.norm_one]
  have h2 (a : A) : normalizedTwoNorm (ψ a - φ a) ≤ 2 * ‖a‖ * √δ := by
    rcases isEmpty_or_nonempty n with hn | hn
    · rw [normalizedTwoNorm_of_isEmpty]
      positivity
    have h0 : 0 ≤ φ 1 := map_nonneg φ zero_le_one
    have hh0 : 0 ≤ CFC.sqrt (φ 1) := CFC.sqrt_nonneg _
    have hh1 : ‖CFC.sqrt (φ 1)‖ ≤ 1 :=
      (CFC.norm_sqrt _ h0).trans_le (Real.sqrt_le_one.2 ((hφ 1).trans CStarRing.norm_one.le))
    have hsq : normalizedTwoNorm (CFC.sqrt (φ 1) - 1) ≤ √δ := by
      refine Real.le_sqrt_of_sq_le ((normalizedTwoNorm_sub_one_sq_le hh0 hh1).trans ?_)
      rw [CFC.sqrt_mul_sqrt_self _ h0, normalizedTrace_sub, normalizedTrace_one, Complex.sub_re,
        Complex.one_re]
      linarith
    rw [hψ a]
    refine (normalizedTwoNorm_sub_mul_mul_le_of_norm_le_one (ψ a) hh1).trans ?_
    exact mul_le_mul (by gcongr; exact hψc a) hsq (normalizedTwoNorm_nonneg _) (by positivity)
  refine ⟨ψ, hψ1, hψ, h2, fun a => ?_, fun a b => ?_⟩
  · rw [← normalizedTrace_sub]
    exact (norm_normalizedTrace_le_normalizedTwoNorm _).trans (h2 a)
  · refine (normalizedTwoNorm_map_mul_sub_le_of_normalizedTwoNorm_sub_le hφ hψc
      (c := 2 * √δ) (fun x => (h2 x).trans_eq (by ring)) a b).trans_eq ?_
    ring

end CompletelyPositiveMap
