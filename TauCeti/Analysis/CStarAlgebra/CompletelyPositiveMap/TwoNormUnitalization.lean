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
`‖ψ(ab) - ψ(a)ψ(b)‖₂ ≤ ‖φ(ab) - φ(a)φ(b)‖₂ + 6‖a‖‖b‖δ^{1/2}`
(`CStarMatrix.normalizedTwoNorm_map_mul_sub_le_of_normalizedTwoNorm_sub_le`).

## Main statements

* `CompletelyPositiveMap.normalizedTwoNorm_sub_le_of_eq_sqrt_mul_mul_sqrt`: the 2-norm, trace and
  product estimates for any unital factor `ψ` with `φ(a) = h ψ(a) h`.
* `CompletelyPositiveMap.exists_unital_normalizedTwoNorm_sub_le`: the 2-norm unitalization, with
  its trace and product estimates.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Lemma 2.7.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveMap

open CStarMatrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **The 2-norm estimates for a unital Choi–Effros factor** (Brown, Lemma 2.7). If `φ : A → M_k`
is a completely positive contraction on a nonzero unital C⋆-algebra with `re tr_k φ(1) ≥ 1 - δ`,
and `ψ` is any unital completely positive map with `φ(a) = h ψ(a) h` for `h = φ(1)^{1/2}`, then
`‖ψ(x) - φ(x)‖₂ ≤ 2‖x‖δ^{1/2}`, `|tr_k ψ(x) - tr_k φ(x)| ≤ 2‖x‖δ^{1/2}` and
`‖ψ(ab) - ψ(a)ψ(b)‖₂ ≤ ‖φ(ab) - φ(a)φ(b)‖₂ + 6‖a‖‖b‖δ^{1/2}`. -/
theorem normalizedTwoNorm_sub_le_of_eq_sqrt_mul_mul_sqrt (φ ψ : A →CP CStarMatrix n n ℂ)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (hψ1 : ψ 1 = 1)
    (hψ : ∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1)) {δ : ℝ}
    (hδ : 1 - δ ≤ (normalizedTrace (φ 1)).re) :
    (∀ a, normalizedTwoNorm (ψ a - φ a) ≤ 2 * ‖a‖ * √δ) ∧
      (∀ a, ‖normalizedTrace (ψ a) - normalizedTrace (φ a)‖ ≤ 2 * ‖a‖ * √δ) ∧
      ∀ a b, normalizedTwoNorm (ψ (a * b) - ψ a * ψ b) ≤
        normalizedTwoNorm (φ (a * b) - φ a * φ b) + 6 * ‖a‖ * ‖b‖ * √δ := by
  have hψc : ∀ a, ‖ψ a‖ ≤ ‖a‖ := (CompletelyPositiveMapClass.norm_map_one_le_one_iff ψ).1 <| by
    rw [hψ1]
    nontriviality CStarMatrix n n ℂ
    exact CStarRing.norm_one.le
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
  refine ⟨h2, fun a => ?_, fun a b => ?_⟩
  · rw [← normalizedTrace_sub]
    exact (norm_normalizedTrace_le_normalizedTwoNorm _).trans (h2 a)
  · refine (normalizedTwoNorm_map_mul_sub_le_of_normalizedTwoNorm_sub_le hφ hψc
      (c := 2 * √δ) (fun x => (h2 x).trans_eq (by ring)) a b).trans_eq ?_
    ring

/-- **The 2-norm unitalization** (Brown, Lemma 2.7). A completely positive contraction
`φ : A → M_k` on a nonzero unital C⋆-algebra with `re tr_k φ(1) ≥ 1 - δ` factors as
`φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` and `ψ` unital completely positive, and then
`‖ψ(x) - φ(x)‖₂ ≤ 2‖x‖δ^{1/2}`, `|tr_k ψ(x) - tr_k φ(x)| ≤ 2‖x‖δ^{1/2}` and
`‖ψ(ab) - ψ(a)ψ(b)‖₂ ≤ ‖φ(ab) - φ(a)φ(b)‖₂ + 6‖a‖‖b‖δ^{1/2}`
(`CompletelyPositiveMap.normalizedTwoNorm_sub_le_of_eq_sqrt_mul_mul_sqrt`). -/
theorem exists_unital_normalizedTwoNorm_sub_le (φ : A →CP CStarMatrix n n ℂ)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) {δ : ℝ} (hδ : 1 - δ ≤ (normalizedTrace (φ 1)).re) :
    ∃ ψ : A →CP CStarMatrix n n ℂ, ψ 1 = 1 ∧
      (∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1)) ∧
      (∀ a, normalizedTwoNorm (ψ a - φ a) ≤ 2 * ‖a‖ * √δ) ∧
      (∀ a, ‖normalizedTrace (ψ a) - normalizedTrace (φ a)‖ ≤ 2 * ‖a‖ * √δ) ∧
      ∀ a b, normalizedTwoNorm (ψ (a * b) - ψ a * ψ b) ≤
        normalizedTwoNorm (φ (a * b) - φ a * φ b) + 6 * ‖a‖ * ‖b‖ * √δ := by
  obtain ⟨ψ, hψ1, hψ⟩ := exists_unital_eq_sqrt_mul_mul_sqrt φ
  exact ⟨ψ, hψ1, hψ, normalizedTwoNorm_sub_le_of_eq_sqrt_mul_mul_sqrt φ ψ hφ hψ1 hψ hδ⟩

end CompletelyPositiveMap
