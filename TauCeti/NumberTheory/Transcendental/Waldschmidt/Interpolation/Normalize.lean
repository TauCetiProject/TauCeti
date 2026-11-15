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
# The height of the normalized coefficients of Waldschmidt's linear form

In Waldschmidt's proof of his lower bound for linear forms in logarithms, a linear form
`c₀ + c₁ λ₁ + ⋯ + cₘ λₘ` with a nonzero coefficient is divided by the negative of that
coefficient; after renumbering the logarithms so that it is the last one, this gives

`c₀ + c₁ λ₁ + ⋯ + cₘ λₘ = -cₘ Λ`, `Λ = β₀ + β₁ λ₁ + ⋯ + β_{m-1} λ_{m-1} - λₘ`,

with `βᵢ = -cᵢ / cₘ` (`TauCeti.waldschmidtNormalize`). The arithmetic estimates of the proof are
stated in terms of the new coefficients `βᵢ`: the field containing them, their denominators and
the height `h(1 : β₀ : ⋯ : β_{m-1})`. The field and the denominators are controlled by the
elementary normalization API next to the definition of `TauCeti.waldschmidtNormalize`: the `βᵢ`
lie in every subfield containing the `cᵢ` (`TauCeti.waldschmidtNormalize_mem`), and the products
`cₘ βᵢ` lie in every subring containing `c₀, …, c_{m-1}`
(`TauCeti.mul_waldschmidtNormalize_mem`). This file records how the height is controlled.

The vector `(β₀, …, β_{m-1}, -1)` is a scalar multiple of `(c₀, c₁, …, cₘ)`
(`TauCeti.snoc_waldschmidtNormalize_neg_one`), so the projective height
`h(1 : β₀ : ⋯ : β_{m-1})`, which is the affine height of `(β₀, …, β_{m-1})`
(`Height.mulHeightAff`), equals the projective height of `(c₀ : c₁ : ⋯ : cₘ)`. In particular it
is at most `h(c₀) + h(c₁) + ⋯ + h(cₘ)`, which is how the height bound on the coefficients of the
measure bounds the height of the normalized ones.

## Main results

* `TauCeti.mulHeightAff_waldschmidtNormalize`: `H(1 : β₀ : ⋯ : β_{m-1}) = H(c₀ : ⋯ : cₘ)`.
* `TauCeti.logHeightAff_waldschmidtNormalize`: its logarithmic form.
* `TauCeti.logHeightAff_waldschmidtNormalize_le`:
  `h(1 : β₀ : ⋯ : β_{m-1}) ≤ h(c₀) + h(c₁) + ⋯ + h(cₘ)`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§9.2.1, 9.3.
-/

public section

open Finset Height

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K] [AdmissibleAbsValues K]

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
