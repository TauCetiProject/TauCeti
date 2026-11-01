/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith

/-!
# The Rademacher convexity inequality

The average norm of a finite signed sum dominates the norm of each summand, and hence their
maximum. Signs are represented by Boolean functions, with `true` acting by negation; `𝔼` is
Mathlib's uniform finite average. No completeness or finite-dimensionality is required.

Applied to scalar multiples of vectors, this inequality compares the maximum of the lengths
of the individual terms with a signed-sum average. For independent symmetric coefficients,
integrating removes the signs and gives a lower bound for the expected norm of the sum.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.3.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- **Rademacher convexity inequality:** the uniform average norm of the signed sums of a
finite family dominates the norm of each vector in the family. -/
theorem norm_le_expect_norm_sum_sign (v : ι → E) (j : ι) :
    ‖v j‖ ≤ 𝔼 ε : ι → Bool, ‖∑ i, if ε i then -v i else v i‖ := by
  classical
  have hinvol : Function.Involutive
      (fun (ε : ι → Bool) i ↦ if i = j then !(ε i) else ε i) := by
    intro ε
    funext i
    by_cases h : i = j <;> simp [h]
  let flip : (ι → Bool) ≃ (ι → Bool) := hinvol.toPerm
  let S (ε : ι → Bool) : E := ∑ i, if ε i then -v i else v i
  -- Pair a sign pattern with its single-coordinate flip, then average the triangle inequality.
  have hpair (ε : ι → Bool) : 2 * ‖v j‖ ≤ ‖S ε‖ + ‖S (flip ε)‖ := by
    have hdiff : S ε - S (flip ε) = if ε j then -(2 : ℝ) • v j else (2 : ℝ) • v j := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j]
      · cases h : ε j <;> simp [flip, h, two_smul, sub_eq_add_neg]
      · intro i _ hij
        simp [flip, hij]
      · simp
    have hn : ‖S ε - S (flip ε)‖ = 2 * ‖v j‖ := by
      rw [hdiff]
      cases ε j <;> simp [norm_smul]
    exact hn ▸ norm_sub_le (S ε) (S (flip ε))
  have havg := Finset.le_expect Finset.univ_nonempty (fun ε _ ↦ hpair ε)
  have hflip : (𝔼 ε, ‖S (flip ε)‖) = 𝔼 ε, ‖S ε‖ :=
    Fintype.expect_equiv flip _ _ (fun _ ↦ rfl)
  rw [Finset.expect_add_distrib, hflip] at havg
  linarith

open Classical in
/-- The maximum length of a nonempty finite family is bounded by the average norm of its
Rademacher sums. -/
theorem sup'_norm_le_expect_norm_sum_sign [Nonempty ι] (v : ι → E) :
    Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖v i‖) ≤
      𝔼 ε : ι → Bool, ‖∑ i, if ε i then -v i else v i‖ := by
  exact Finset.sup'_le _ _ fun i _ ↦ norm_le_expect_norm_sum_sign v i

end TauCeti
