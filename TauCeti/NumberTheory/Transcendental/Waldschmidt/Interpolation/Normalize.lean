/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Affine
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data
import TauCeti.NumberTheory.Height.Basic

/-!
# The normalized coefficients of Waldschmidt's linear form

In Waldschmidt's proof of his lower bound for linear forms in logarithms, a linear form
`c₀ + c₁ λ₁ + ⋯ + cₘ λₘ` with a nonzero coefficient is divided by the negative of that
coefficient; after renumbering the logarithms so that it is the last one, this gives

`c₀ + c₁ λ₁ + ⋯ + cₘ λₘ = -cₘ Λ`, `Λ = β₀ + β₁ λ₁ + ⋯ + β_{m-1} λ_{m-1} - λₘ`,

with `βᵢ = -cᵢ / cₘ` (`TauCeti.waldschmidtNormalize`). The arithmetic estimates of the proof are
stated in terms of the new coefficients `βᵢ`: the field containing them, their denominators and
the height `h(1 : β₀ : ⋯ : β_{m-1})`. This file records how each of these is controlled by the
original coefficients.

* **The field.** The `βᵢ` lie in every subfield containing the `cᵢ`, and normalization commutes
  with ring homomorphisms, such as complex embeddings of a number field.
* **The denominators.** The products `cₘ βᵢ` lie in every subring containing `c₀, …, c_{m-1}`,
  with no assumption on `cₘ`; when `cₘ ≠ 0` they equal `-cᵢ`, so `cₘ` is a common denominator
  of the `βᵢ` (when `cₘ = 0` the `βᵢ` and the products are all `0`). In the homogeneous rational
  case, where the `cᵢ` are integers, the `cₘ βᵢ` are integers; this is the hypothesis on the
  coefficients of the denominator bounds
  for the delta-polynomial rows (`Subring.mul_waldschmidtInterpolationMatrix_waldschmidtDelta_mem`).
* **The height.** The vector `(β₀, …, β_{m-1}, -1)` is a scalar multiple of `(c₀, c₁, …, cₘ)`,
  so the projective height `h(1 : β₀ : ⋯ : β_{m-1})`, which is the affine height of
  `(β₀, …, β_{m-1})` (`Height.mulHeightAff`), equals the projective height of
  `(c₀ : c₁ : ⋯ : cₘ)`. In particular it is at most `h(c₀) + h(c₁) + ⋯ + h(cₘ)`, which is how the
  height bound on the coefficients of the measure bounds the height of the normalized ones.

## Main results

* `TauCeti.add_sum_mul_eq_neg_mul_waldschmidtLinearForm_comp_swap`: normalization at an
  arbitrary nonzero coefficient `c_k`, after exchanging `λ_k` and `λₘ`.
* `TauCeti.waldschmidtNormalize_map`, `TauCeti.waldschmidtNormalize_mem`: the field of the
  normalized coefficients.
* `TauCeti.mul_waldschmidtNormalize_mem`,
  `TauCeti.intCast_mul_waldschmidtNormalize_intCast_mem_range_intCast`: their denominators.
* `TauCeti.snoc_waldschmidtNormalize_neg_one`: `(β₀, …, β_{m-1}, -1) = (-cₘ)⁻¹ (c₀, …, cₘ)`.
* `TauCeti.mulHeightAff_waldschmidtNormalize`: `H(1 : β₀ : ⋯ : β_{m-1}) = H(c₀ : ⋯ : cₘ)`.
* `TauCeti.logHeightAff_waldschmidtNormalize_le`:
  `h(1 : β₀ : ⋯ : β_{m-1}) ≤ h(c₀) + h(c₁) + ⋯ + h(cₘ)`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§9.2.1, 9.3.
-/

public section

open Finset Height

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K]

/-- **Normalization at an arbitrary coefficient.** If the coefficient `c_k` of the linear form
`c₀ + c₁ λ₁ + ⋯ + cₘ λₘ` is nonzero, then after exchanging `λ_k` and `λₘ` (and their
coefficients) the linear form is `-c_k` times the normalized linear form `Λ`, whose coefficients
are `-cᵢ / c_k`. -/
theorem add_sum_mul_eq_neg_mul_waldschmidtLinearForm_comp_swap (ι : K →+* ℂ)
    (l : Fin (n + 1) → ℂ) (c₀ : K) (c : Fin (n + 1) → K) {k : Fin (n + 1)} (hc : c k ≠ 0) :
    ι c₀ + ∑ j, ι (c j) * l j =
      -ι (c k) * waldschmidtLinearForm (l ∘ Equiv.swap k (Fin.last n))
        fun i ↦ ι (waldschmidtNormalize c₀ (c ∘ Equiv.swap k (Fin.last n)) i) := by
  rw [← Equiv.sum_comp (Equiv.swap k (Fin.last n))]
  simpa using add_sum_mul_eq_neg_mul_waldschmidtLinearForm ι (l ∘ Equiv.swap k (Fin.last n)) c₀
    (c ∘ Equiv.swap k (Fin.last n)) (by simpa using hc)

/-- Normalization commutes with ring homomorphisms: the normalized coefficients of the images of
the `cᵢ` are the images of the normalized coefficients. -/
theorem waldschmidtNormalize_map {L : Type*} [Field L] (f : K →+* L) (c₀ : K)
    (c : Fin (n + 1) → K) :
    waldschmidtNormalize (f c₀) (fun j ↦ f (c j)) = fun i ↦ f (waldschmidtNormalize c₀ c i) := by
  ext i
  cases i using Fin.cases <;> simp

/-- The normalized coefficients lie in every subfield containing the coefficients `cᵢ`. -/
theorem waldschmidtNormalize_mem {S : Type*} [SetLike S K] [SubfieldClass S K] (L : S) {c₀ : K}
    {c : Fin (n + 1) → K} (hc₀ : c₀ ∈ L) (hc : ∀ j, c j ∈ L) (i : Fin (n + 1)) :
    waldschmidtNormalize c₀ c i ∈ L := by
  cases i using Fin.cases with
  | zero =>
    rw [waldschmidtNormalize_zero]
    exact div_mem (neg_mem hc₀) (hc _)
  | succ k =>
    rw [waldschmidtNormalize_succ]
    exact div_mem (neg_mem (hc _)) (hc _)

/-- If the numerator coefficients `c₀, …, c_{m-1}` lie in a subring `A`, then so do the products
`cₘ βᵢ`, without requiring `cₘ ∈ A`. When `cₘ ≠ 0` these products are `-cᵢ`, so `cₘ` is a
common denominator of the `βᵢ`; when `cₘ = 0` they are all `0`. -/
theorem mul_waldschmidtNormalize_mem {S : Type*} [SetLike S K] [SubringClass S K] (A : S)
    {c₀ : K} {c : Fin (n + 1) → K} (hc₀ : c₀ ∈ A) (hc : ∀ j : Fin n, c j.castSucc ∈ A)
    (i : Fin (n + 1)) :
    c (Fin.last n) * waldschmidtNormalize c₀ c i ∈ A := by
  rcases eq_or_ne (c (Fin.last n)) 0 with h | h
  · rw [h, zero_mul]
    exact zero_mem A
  cases i using Fin.cases with
  | zero =>
    rw [waldschmidtNormalize_zero, mul_div_cancel₀ _ h]
    exact neg_mem hc₀
  | succ k =>
    rw [waldschmidtNormalize_succ, mul_div_cancel₀ _ h]
    exact neg_mem (hc _)

/-- **Denominators in the homogeneous rational case.** If the coefficients are integers `aᵢ`,
then `aₘ βᵢ` is an integer for every normalized coefficient `βᵢ`. -/
theorem intCast_mul_waldschmidtNormalize_intCast_mem_range_intCast (a₀ : ℤ)
    (a : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    (a (Fin.last n) : K) * waldschmidtNormalize (a₀ : K) (fun j ↦ (a j : K)) i ∈
      Set.range (Int.cast : ℤ → K) :=
  Subring.mem_bot.1 <| mul_waldschmidtNormalize_mem (⊥ : Subring K)
    (c := fun j ↦ (a j : K)) (intCast_mem _ a₀) (fun j ↦ intCast_mem _ (a j.castSucc)) i

/-- The coefficient vector `(β₀, β₁, …, β_{m-1}, -1)` of the normalized linear form is the
coefficient vector `(c₀, c₁, …, cₘ)` of the original linear form divided by `-cₘ`. -/
theorem snoc_waldschmidtNormalize_neg_one (c₀ : K) (c : Fin (n + 1) → K)
    (hc : c (Fin.last n) ≠ 0) :
    (Fin.snoc (waldschmidtNormalize c₀ c) (-1) : Fin (n + 2) → K) =
      (-c (Fin.last n))⁻¹ • Fin.cons c₀ c := by
  ext i
  cases i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, Pi.smul_apply, ← Fin.succ_last, Fin.cons_succ, smul_eq_mul, inv_neg,
      neg_mul, inv_mul_cancel₀ hc]
  | cast i =>
    rw [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
    cases i using Fin.cases with
    | zero =>
      rw [waldschmidtNormalize_zero, Fin.castSucc_zero, Fin.cons_zero]
      field_simp
    | succ k =>
      rw [waldschmidtNormalize_succ, ← Fin.succ_castSucc, Fin.cons_succ]
      field_simp

variable [AdmissibleAbsValues K]

/-- **The height of the normalized coefficients.** If `cₘ ≠ 0`, the projective height
`H(1 : β₀ : ⋯ : β_{m-1})` of the normalized coefficients, which is their affine height, equals the
projective height `H(c₀ : c₁ : ⋯ : cₘ)` of the original coefficients. -/
theorem mulHeightAff_waldschmidtNormalize (c₀ : K) (c : Fin (n + 1) → K)
    (hc : c (Fin.last n) ≠ 0) :
    mulHeightAff (waldschmidtNormalize c₀ c) = mulHeight (Fin.cons c₀ c : Fin (n + 2) → K) := by
  -- Appending the coordinate `1` at the end computes the affine height.
  have hsnoc : (Fin.snoc (waldschmidtNormalize c₀ c) 1 : Fin (n + 2) → K) =
      (fun o : Option (Fin (n + 1)) ↦ o.elim 1 (waldschmidtNormalize c₀ c)) ∘
        finSuccEquivLast := by
    ext i
    cases i using Fin.lastCases <;> simp [finSuccEquivLast_castSucc]
  -- Changing the sign of the last coordinate does not change the height.
  have hsign : mulHeight (Fin.snoc (waldschmidtNormalize c₀ c) 1 : Fin (n + 2) → K) =
      mulHeight (Fin.snoc (waldschmidtNormalize c₀ c) (-1) : Fin (n + 2) → K) :=
    mulHeight_eq_of_forall_eq_or_eq_neg fun i ↦ by cases i using Fin.lastCases <;> simp
  rw [mulHeightAff_def, ← mulHeight_comp_equiv finSuccEquivLast, ← hsnoc, hsign,
    snoc_waldschmidtNormalize_neg_one c₀ c hc,
    mulHeight_smul_eq_mulHeight _ (inv_ne_zero (neg_ne_zero.2 hc))]

/-- The logarithmic form of `TauCeti.mulHeightAff_waldschmidtNormalize`:
`h(1 : β₀ : ⋯ : β_{m-1}) = h(c₀ : c₁ : ⋯ : cₘ)`. -/
theorem logHeightAff_waldschmidtNormalize (c₀ : K) (c : Fin (n + 1) → K)
    (hc : c (Fin.last n) ≠ 0) :
    logHeightAff (waldschmidtNormalize c₀ c) = logHeight (Fin.cons c₀ c : Fin (n + 2) → K) := by
  rw [logHeightAff_eq_log_mulHeightAff, logHeight_eq_log_mulHeight,
    mulHeightAff_waldschmidtNormalize c₀ c hc]

/-- **Height bound for the normalized coefficients.**
`h(1 : β₀ : ⋯ : β_{m-1}) ≤ h(c₀) + h(c₁) + ⋯ + h(cₘ)`. When `cₘ = 0` the normalized coefficients
are all `0`, and the bound holds trivially. -/
theorem logHeightAff_waldschmidtNormalize_le (c₀ : K) (c : Fin (n + 1) → K) :
    logHeightAff (waldschmidtNormalize c₀ c) ≤ logHeight₁ c₀ + ∑ j, logHeight₁ (c j) := by
  rcases eq_or_ne (c (Fin.last n)) 0 with hc | hc
  · have h0 : waldschmidtNormalize c₀ c = 0 := by
      ext i
      cases i using Fin.cases <;> simp [hc]
    rw [h0, logHeightAff_zero]
    exact add_nonneg (zero_le_logHeight₁ _) (sum_nonneg fun j _ ↦ zero_le_logHeight₁ _)
  rw [logHeightAff_waldschmidtNormalize c₀ c hc]
  calc
    _ ≤ logHeightAff (Fin.cons c₀ c : Fin (n + 2) → K) := logHeight_le_logHeightAff _
    _ ≤ ∑ i, logHeight₁ ((Fin.cons c₀ c : Fin (n + 2) → K) i) :=
      logHeightAff_le_sum_logHeight₁ _
    _ = logHeight₁ c₀ + ∑ j, logHeight₁ (c j) := by
      rw [Fin.sum_univ_succ]
      simp

end TauCeti
