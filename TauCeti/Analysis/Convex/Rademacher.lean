/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Bool

/-!
# The Rademacher convexity inequality

The average norm of a finite signed sum dominates the norm of each summand, hence
also their maximum. Signs are indexed by `ι → Bool`, with `true` representing `+1`.
The average is Mathlib's finite expectation, so it is normalized even when `ι` is empty.
No completeness assumption on the range space is needed.

This inequality lets one compare the expected norm of a sum of independent symmetric
random vectors with the expected maximum of their norms.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.3.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- The Rademacher average of the norm of a sum dominates the norm of each summand. -/
theorem norm_le_expect_norm_sum_sign (v : ι → E) (i : ι) :
    ‖v i‖ ≤ 𝔼 ε : ι → Bool, ‖∑ j, if ε j then v j else -v j‖ := by
  classical
  let e : (ι → Bool) ≃ (ι → Bool) := Equiv.piCongrRight fun j ↦
    if j = i then Equiv.boolNot else Equiv.refl Bool
  have he (ε : ι → Bool) (j : ι) : e ε j = if j = i then !(ε j) else ε j := by
    by_cases h : j = i <;> simp [e, h, Equiv.piCongrRight_apply, Equiv.boolNot]
  have hpair (ε : ι → Bool) :
      2 * ‖v i‖ ≤ ‖∑ j, if ε j then v j else -v j‖ +
        ‖∑ j, if e ε j then v j else -v j‖ := by
    have hsub : (∑ j, if ε j then v j else -v j) -
        (∑ j, if e ε j then v j else -v j) =
        if ε i then v i + v i else -(v i + v i) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · cases h : ε i <;> simp [he, h, sub_eq_add_neg]
      · intro j _ hji
        simp [he, hji]
      · simp
    have hnorm := norm_sub_le (∑ j, if ε j then v j else -v j)
      (∑ j, if e ε j then v j else -v j)
    rw [hsub] at hnorm
    simpa only [apply_ite norm, norm_neg, ← two_smul ℝ, norm_smul,
      Real.norm_ofNat, ite_self] using hnorm
  have h := Finset.expect_le_expect (s := Finset.univ) fun ε _ ↦ hpair ε
  have heq := Fintype.expect_equiv e
    (fun ε ↦ ‖∑ j, if e ε j then v j else -v j‖)
    (fun ε ↦ ‖∑ j, if ε j then v j else -v j‖) (fun _ ↦ rfl)
  rw [Finset.expect_const (Finset.univ_nonempty), Finset.expect_add_distrib, heq] at h
  linarith

open Classical in
/-- The maximum norm of a nonempty finite family is bounded by its Rademacher average. -/
theorem max_norm_le_expect_norm_sum_sign [Nonempty ι] (v : ι → E) :
    Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖v i‖) ≤
      𝔼 ε : ι → Bool, ‖∑ j, if ε j then v j else -v j‖ := by
  exact Finset.sup'_le _ _ fun i _ ↦ norm_le_expect_norm_sum_sign v i

end TauCeti
