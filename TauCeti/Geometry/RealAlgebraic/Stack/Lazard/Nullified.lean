/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic

/-!
# A nullified polynomial with a nonzero Lazard evaluation

This file works out the basic example of Lazard's treatment of nullification. Let
`f = x₁ (z + 1) + x₀ x₂` in the base variables `x₀, x₁, x₂` and the distinguished last variable
`z`, and let `L ⊆ ℝ³` be the line `x₀ = x₁ = 0`. Over every point of `L` the ordinary fibre of
`f` is the zero polynomial in `z`, so ordinary specialization, on which the Collins and McCallum
lifting steps rely, carries no information about `f` above `L`: every point of the cylinder is a
root of the fibre. Over the point `(0, 0, s)`, Lazard evaluation instead divides out the largest
power of `x₀` (none), sets `x₀ = 0`, divides out the largest power of `x₁` (one), and sets
`x₁ = 0` and `x₂ = s`: it removes the base exponent `(0, 1, 0)` and leaves the nonzero
polynomial `z + 1`.

Accordingly `f` has a Lazard delineation over `L` with the single constant section `z = -1`. On
that section the Lazard valuation of `f` is `(0, 1, 0, 1)`, and on the two sectors it is
`(0, 1, 0, 0)`; so the Lazard valuation of `f`, although not constant on the cylinder over `L`,
is constant on each cell of this stack, as `TauCeti.LazardDelineation` guarantees in general.

The Lazard computations reduce to the ultrametric rule for sums
(`MvPolynomial.lazardEval_add_of_lazardValuation_lt`): after moving `z` into the coefficients, the
summand `x₁ (z + 1)` has strictly smaller Lazard valuation over `L` than `x₀ x₂`, so it alone
determines the Lazard evaluation and the removed exponents.

## Main declarations

* `TauCeti.lazardNullifiedExample`: the polynomial `x₁ (z + 1) + x₀ x₂`.
* `TauCeti.eval_optionEquivRight_rename_lazardNullifiedExample`: its ordinary fibres over `L`
  vanish.
* `TauCeti.lazardEval_optionEquivRight_rename_lazardNullifiedExample`,
  `TauCeti.lazardExponent_optionEquivRight_rename_lazardNullifiedExample`: over `L` its Lazard
  evaluation is `z + 1`, with removed base exponent `(0, 1, 0)`.
* `TauCeti.lazardDelineationNullifiedExample`: its Lazard delineation over `L`.
* `TauCeti.lazardValuation_lazardNullifiedExample_snoc`: its Lazard valuations above `L`.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Sections 2 and 5.
-/

public section

open MvPolynomial Set

open scoped Polynomial

namespace TauCeti

/-- The polynomial `x₁ (z + 1) + x₀ x₂` in the base variables `x₀, x₁, x₂` and the last variable
`z`. Its ordinary fibres over the line `x₀ = x₁ = 0` vanish identically, while its Lazard
evaluations there are `z + 1`. -/
noncomputable def lazardNullifiedExample : MvPolynomial (Fin 4) ℝ :=
  X 1 * (X 3 + 1) + X 0 * X 2

theorem lazardNullifiedExample_def :
    lazardNullifiedExample = X 1 * (X 3 + 1) + X 0 * X 2 := (rfl)

/-- Moving the last variable into the coefficients turns `x₁ (z + 1) + x₀ x₂` into a polynomial
in the base variables over `ℝ[z]`; over a point with `x₁ = 0` its first summand is
`(x₁ - x₁(α)) (z + 1)`. -/
private theorem optionEquivRight_rename_lazardNullifiedExample {x : Fin 3 → ℝ} (h1 : x 1 = 0) :
    optionEquivRight ℝ (Fin 3) (rename finSuccEquivLast lazardNullifiedExample) =
      (X 1 - C ((Polynomial.C ∘ x) 1)) * C (Polynomial.X + 1) + X 0 * X 2 := by
  have e0 : finSuccEquivLast (0 : Fin 4) = some 0 := (rfl)
  have e1 : finSuccEquivLast (1 : Fin 4) = some 1 := (rfl)
  have e2 : finSuccEquivLast (2 : Fin 4) = some 2 := (rfl)
  have e3 : finSuccEquivLast (3 : Fin 4) = none := (rfl)
  simp [lazardNullifiedExample_def, e0, e1, e2, e3, h1]

/-- The Lazard valuation of the first summand `(x₁ - x₁(α)) (z + 1)` at `α` is `(0, 1, 0)`. -/
private theorem lazardValuation_X_sub_C_mul_C (x : Fin 3 → ℝ) :
    ((X 1 - C ((Polynomial.C ∘ x) 1)) * C (Polynomial.X + 1) :
      MvPolynomial (Fin 3) ℝ[X]).lazardValuation (Polynomial.C ∘ x) =
        ↑(toLex (Finsupp.single (1 : Fin 3) 1)) := by
  rw [lazardValuation_mul, lazardValuation_X_sub_C,
    lazardValuation_C_of_ne_zero (Polynomial.X_add_C_ne_zero 1), add_zero]

/-- Over a point with `x₀ = 0`, the second summand `x₀ x₂` has Lazard valuation above `(0, 1, 0)`,
since it is divisible by `x₀ - 0`. -/
private theorem lt_lazardValuation_X_mul_X {x : Fin 3 → ℝ} (h0 : x 0 = 0) :
    ↑(toLex (Finsupp.single (1 : Fin 3) 1)) <
      (X 0 * X 2 : MvPolynomial (Fin 3) ℝ[X]).lazardValuation (Polynomial.C ∘ x) := by
  have hX0 : (X 0 : MvPolynomial (Fin 3) ℝ[X]) = X 0 - C ((Polynomial.C ∘ x) 0) := by simp [h0]
  calc (↑(toLex (Finsupp.single (1 : Fin 3) 1)) : WithTop (Lex (Fin 3 →₀ ℕ)))
      < ↑(toLex (Finsupp.single (0 : Fin 3) 1)) :=
        WithTop.coe_lt_coe.2 (Finsupp.Lex.single_lt_iff.2 (by decide))
    _ ≤ (X 0 : MvPolynomial (Fin 3) ℝ[X]).lazardValuation (Polynomial.C ∘ x) +
        (X 2 : MvPolynomial (Fin 3) ℝ[X]).lazardValuation (Polynomial.C ∘ x) := by
        rw [hX0, lazardValuation_X_sub_C]
        exact le_add_of_nonneg_right (zero_le_lazardValuation _ _)
    _ ≤ _ := le_lazardValuation_mul _ _ _

/-- The polynomial `x₁ (z + 1) + x₀ x₂` is nonzero: it takes the value `1` at `(0, 1, 0, 0)`. -/
theorem lazardNullifiedExample_ne_zero : lazardNullifiedExample ≠ 0 := by
  intro h
  have := congrArg (eval ![0, 1, 0, 0]) h
  simp [lazardNullifiedExample_def] at this

/-- **Nullification.** Over every point of the line `x₀ = x₁ = 0`, the ordinary fibre of
`x₁ (z + 1) + x₀ x₂` is the zero polynomial in `z`. -/
theorem eval_optionEquivRight_rename_lazardNullifiedExample {x : Fin 3 → ℝ} (h0 : x 0 = 0)
    (h1 : x 1 = 0) :
    eval (Polynomial.C ∘ x)
      (optionEquivRight ℝ (Fin 3) (rename finSuccEquivLast lazardNullifiedExample)) = 0 := by
  rw [optionEquivRight_rename_lazardNullifiedExample h1]
  simp [h0]

/-- Over every point of the line `x₀ = x₁ = 0`, the Lazard evaluation of `x₁ (z + 1) + x₀ x₂`
is `z + 1`, although its ordinary fibre vanishes
(`TauCeti.eval_optionEquivRight_rename_lazardNullifiedExample`). -/
theorem lazardEval_optionEquivRight_rename_lazardNullifiedExample {x : Fin 3 → ℝ}
    (h0 : x 0 = 0) (h1 : x 1 = 0) :
    (optionEquivRight ℝ (Fin 3) (rename finSuccEquivLast lazardNullifiedExample)).lazardEval
      (Polynomial.C ∘ x) = Polynomial.X + 1 := by
  rw [optionEquivRight_rename_lazardNullifiedExample h1, lazardEval_add_of_lazardValuation_lt
    ((lazardValuation_X_sub_C_mul_C x).trans_lt (lt_lazardValuation_X_mul_X h0)),
    lazardEval_mul, lazardEval_X_sub_C, lazardEval_C, one_mul]

/-- Over every point of the line `x₀ = x₁ = 0`, Lazard evaluation of `x₁ (z + 1) + x₀ x₂`
removes exactly one power of `x₁`, and no power of `x₀` or `x₂`. -/
theorem lazardExponent_optionEquivRight_rename_lazardNullifiedExample {x : Fin 3 → ℝ}
    (h0 : x 0 = 0) (h1 : x 1 = 0) :
    (optionEquivRight ℝ (Fin 3) (rename finSuccEquivLast lazardNullifiedExample)).lazardExponent
      (Polynomial.C ∘ x) = Finsupp.single 1 1 := by
  have hX1 : (X 1 - C ((Polynomial.C ∘ x) 1) : MvPolynomial (Fin 3) ℝ[X]) ≠ 0 := by
    simp [h1, X_ne_zero]
  have hX : (Polynomial.X + 1 : ℝ[X]) ≠ 0 := Polynomial.X_add_C_ne_zero 1
  rw [optionEquivRight_rename_lazardNullifiedExample h1, lazardExponent_add_of_lazardValuation_lt
    ((lazardValuation_X_sub_C_mul_C x).trans_lt (lt_lazardValuation_X_mul_X h0)),
    lazardExponent_mul hX1 (C_ne_zero.2 hX), lazardExponent_X_sub_C, lazardExponent_C, add_zero]

/-- **The Lazard delineation of a nullified polynomial.** Over the line `x₀ = x₁ = 0`, where all
ordinary fibres of `x₁ (z + 1) + x₀ x₂` vanish, the polynomial has the Lazard delineation with
the single constant section `z = -1`, of multiplicity one, and removed base exponent
`(0, 1, 0)`. -/
noncomputable def lazardDelineationNullifiedExample :
    LazardDelineation (fun _ : Unit ↦ lazardNullifiedExample)
      {x : Fin 3 → ℝ | x 0 = 0 ∧ x 1 = 0} where
  nonempty := ⟨0, rfl, rfl⟩
  count := 1
  root _ _ := -1
  continuous_root _ := continuous_const
  strictMono_root _ := Subsingleton.strictMono _
  exponent _ := Finsupp.single 1 1
  lazardExponent_eq _ x :=
    lazardExponent_optionEquivRight_rename_lazardNullifiedExample x.2.1 x.2.2
  multiplicity _ _ := 1
  rootMultiplicity_root _ _ x := by
    rw [lazardEval_optionEquivRight_rename_lazardNullifiedExample x.2.1 x.2.2,
      ← Polynomial.C_1, ← sub_neg_eq_add, ← Polynomial.C_neg, Polynomial.rootMultiplicity_X_sub_C]
    simp
  exists_root_eq _ x _ t ht := by
    rw [lazardEval_optionEquivRight_rename_lazardNullifiedExample x.2.1 x.2.2] at ht
    refine ⟨0, ?_⟩
    have := ht.eq_zero
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at this
    linarith
  exists_multiplicity_pos _ := ⟨(), one_pos⟩

@[simp]
theorem lazardDelineationNullifiedExample_count : lazardDelineationNullifiedExample.count = 1 :=
  (rfl)

@[simp]
theorem lazardDelineationNullifiedExample_root (i : Fin lazardDelineationNullifiedExample.count)
    (x : {x : Fin 3 → ℝ | x 0 = 0 ∧ x 1 = 0}) :
    lazardDelineationNullifiedExample.root i x = -1 :=
  (rfl)

@[simp]
theorem lazardDelineationNullifiedExample_exponent (k : Unit) :
    lazardDelineationNullifiedExample.exponent k = Finsupp.single 1 1 :=
  (rfl)

@[simp]
theorem lazardDelineationNullifiedExample_multiplicity (k : Unit)
    (i : Fin lazardDelineationNullifiedExample.count) :
    lazardDelineationNullifiedExample.multiplicity k i = 1 :=
  (rfl)

/-- **Lazard valuations above the nullified line.** At a point `(x, t)` with `x₀ = x₁ = 0`, the
Lazard valuation of `x₁ (z + 1) + x₀ x₂` is `(0, 1, 0, 1)` when `t = -1`, on the section of
`TauCeti.lazardDelineationNullifiedExample`, and `(0, 1, 0, 0)` otherwise, on its sectors. -/
theorem lazardValuation_lazardNullifiedExample_snoc {x : Fin 3 → ℝ} (h0 : x 0 = 0)
    (h1 : x 1 = 0) (t : ℝ) :
    lazardNullifiedExample.lazardValuation (Fin.snoc x t) =
      ↑(toLex (Finsupp.snoc (Finsupp.single (1 : Fin 3) 1) (if t = -1 then 1 else 0))) := by
  rw [lazardValuation_snoc lazardNullifiedExample_ne_zero,
    lazardExponent_optionEquivRight_rename_lazardNullifiedExample h0 h1,
    lazardEval_optionEquivRight_rename_lazardNullifiedExample h0 h1, ← Polynomial.C_1,
    ← sub_neg_eq_add, ← Polynomial.C_neg, Polynomial.rootMultiplicity_X_sub_C]

end TauCeti
