/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Dioph.NormalForm

/-!
# Checks for integer polynomials as Diophantine polynomials

These computations pin the conventions of `MvPolynomial.toPoly` and of the finite normal form
of Diophantine sets.

* At the natural assignment `(1, 3)`, the polynomial `X₀ - 2 X₁` has value `-5`: the
  evaluation is in `ℤ`, with no truncated natural subtraction.
* `X₀ (X₀ - 1)` vanishes at `0` and at `1` but is not the zero function: its value at `2` is `2`.
* Compressing witnesses needs an injective renaming: `u - v - 1` has the natural root `(1, 0)`,
  whereas collapsing both witnesses to one variable gives the constant `-1`, which has none.
* The even natural numbers are Diophantine, with the single witness of `x - 2 y`.
-/

public section

namespace TauCeti.Examples.Dioph

open MvPolynomial

/-- `X₀ - 2 X₁` has value `-5` at the natural assignment `(1, 3)`. -/
theorem toPoly_sub_apply :
    toPoly (X 0 - 2 * X 1 : MvPolynomial (Fin 2) ℤ) ![1, 3] = -5 := by
  simp

/-- `X₀ (X₀ - 1)` has value `2` at `2`, so it is not the zero polynomial function. -/
theorem toPoly_mul_sub_one_ne_zero :
    toPoly (X 0 * (X 0 - 1) : MvPolynomial (Fin 1) ℤ) ≠ 0 := by
  intro h
  have h2 := congrArg (fun f : Poly (Fin 1) ↦ f ![2]) h
  norm_num at h2

/-- The polynomial `u - v - 1` in two witnesses and no inputs. -/
noncomputable def uSubVSubOne : MvPolynomial (Empty ⊕ Fin 2) ℤ :=
  X (.inr 0) - X (.inr 1) - 1

/-- `u - v - 1` has the natural root `(1, 0)`, but after collapsing both witnesses to a single
variable it has no natural root: the injectivity hypothesis of
`MvPolynomial.exists_eval_rename_sumMap_eq_zero_iff` cannot be dropped. -/
theorem exists_root_and_not_exists_root_rename_const :
    (∃ z : Fin 2 → ℕ, eval (Sum.elim Empty.elim (Nat.cast ∘ z)) uSubVSubOne = 0) ∧
      ¬ ∃ y : Unit → ℕ, eval (Sum.elim Empty.elim (Nat.cast ∘ y))
        (rename (Sum.map id fun _ ↦ ()) uSubVSubOne) = 0 := by
  refine ⟨⟨![1, 0], by simp [uSubVSubOne]⟩, ?_⟩
  rintro ⟨y, hy⟩
  simp [uSubVSubOne] at hy

/-- The even natural numbers form a Diophantine set, cut out by `x - 2 y`. -/
theorem dioph_even : Dioph {x : Fin 1 → ℕ | Even (x 0)} := by
  refine Dioph.of_mvPolynomial (β := Fin 1) (X (.inl 0) - 2 * X (.inr 0)) fun x ↦ ?_
  simp only [Set.mem_ofPred_eq, map_sub, map_mul, eval_X, Function.comp_apply, Sum.elim_inl,
    Sum.elim_inr, map_ofNat, sub_eq_zero]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨fun _ ↦ k, by push_cast [hk]; ring⟩
  · rintro ⟨y, hy⟩
    exact ⟨y 0, by omega⟩

end TauCeti.Examples.Dioph
