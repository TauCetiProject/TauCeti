/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
public import TauCeti.NumberTheory.QuadraticForm.Global.TernaryObstruction
import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic

/-!
# An isometry of ternary forms over `ℚ` through the hyperbolic plane

The ternary forms `⟨1, 1, -1⟩` and `⟨1, 2, -2⟩` over `ℚ`, that is `x² + y² - z²` and
`x² + 2y² - 2z²`, are isometric. Elementary Witt theory proves this: `⟨1, -1⟩` and `⟨2, -2⟩` are
both hyperbolic planes, so both forms are `⟨1⟩ ⊥ H`.

The global classification of quadratic forms over a number field predicts the same isometry from
the invariants alone. Computed directly from the coefficients, without the isometry, the system of
local invariants of `⟨1, a, -a⟩` over any number field is independent of `a`: rank `3`,
discriminant the class of `-1` (as `1 · a · (-a) = -a²`), trivial Hasse sign at every finite place
(`(1, ·)_v = 1` and `(a, -a)_v = 1`), and positive index `2` at every real place (exactly one of
`a` and `-a` is positive there). So the two forms have the same system, consistently with the
explicit isometry.

## Main results

All in the namespace `TauCeti.NumberField.QuadraticForm`:

* `equivalent_sumTwoSquaresSubSq_sqAddTwoSqSubTwoSq`: `⟨1, 1, -1⟩` and `⟨1, 2, -2⟩` are
  isometric over `ℚ`.
* `globalInvariants_sumTwoSquaresSubSq`, `globalInvariants_sqAddTwoSqSubTwoSq`: the systems of
  local invariants of `⟨1, 1, -1⟩` and `⟨1, 2, -2⟩`, which coincide. Both specialize
  `globalInvariants_weightedSumSquares_one_self_neg` from
  `TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter I, §3, for hyperbolic planes.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §66, for the global invariants.
-/

public section
noncomputable section

open IsDedekindDomain NumberField QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

/-- The ternary form `⟨1, 2, -2⟩` over `ℚ`, isometric to `⟨1, 1, -1⟩`. -/
def sqAddTwoSqSubTwoSq : _root_.QuadraticForm ℚ (Fin 3 → ℚ) :=
  weightedSumSquares ℚ ![(1 : ℚ), 2, -2]

/-- `sqAddTwoSqSubTwoSq` is the diagonal form `⟨1, 2, -2⟩`. -/
theorem sqAddTwoSqSubTwoSq_def : sqAddTwoSqSubTwoSq = weightedSumSquares ℚ ![(1 : ℚ), 2, -2] :=
  (rfl)

/-- The value of `⟨1, 2, -2⟩` at `(x, y, z)` is `x² + 2y² - 2z²`. -/
@[simp]
theorem sqAddTwoSqSubTwoSq_apply (x : Fin 3 → ℚ) :
    sqAddTwoSqSubTwoSq x = x 0 ^ 2 + 2 * x 1 ^ 2 - 2 * x 2 ^ 2 := by
  simp [sqAddTwoSqSubTwoSq, weightedSumSquares_apply, Fin.sum_univ_three, pow_two]
  ring

/-- **An isometry through the hyperbolic plane.** `⟨1, 1, -1⟩ ≅ ⟨1, 2, -2⟩` over `ℚ`: both binary
summands `⟨1, -1⟩` and `⟨2, -2⟩` are hyperbolic planes. -/
theorem equivalent_sumTwoSquaresSubSq_sqAddTwoSqSubTwoSq :
    sumTwoSquaresSubSq.Equivalent sqAddTwoSqSubTwoSq := by
  let : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  rw [sumTwoSquaresSubSq_def, sqAddTwoSqSubTwoSq_def]
  refine equivalent_weightedSumSquares_of_pair (i := 1) (j := 2) (by decide) ?_ fun k hk1 hk2 => ?_
  · have h₁ := equivalent_weightedSumSquares_self_neg_hyperbolicPlane (1 : ℚˣ)
    have h₂ :=
      equivalent_weightedSumSquares_self_neg_hyperbolicPlane (Units.mk0 (2 : ℚ) two_ne_zero)
    simp only [Units.val_one, Units.val_mk0] at h₁ h₂
    simpa using h₁.trans h₂.symm
  · fin_cases k <;> simp_all

/-- `⟨1, 2, -2⟩` is nondegenerate. -/
theorem nondegenerate_sqAddTwoSqSubTwoSq : sqAddTwoSqSubTwoSq.Nondegenerate := by
  rw [sqAddTwoSqSubTwoSq_def]
  exact nondegenerate_weightedSumSquares fun i =>
    isRegular_iff_ne_zero.mpr (by fin_cases i <;> simp)

/-- The system of local invariants of `⟨1, 1, -1⟩`: rank `3`, discriminant the class of `-1`,
trivial Hasse sign at every finite place, and positive index `2` at the real place. -/
theorem globalInvariants_sumTwoSquaresSubSq :
    sumTwoSquaresSubSq.globalInvariants nondegenerate_sumTwoSquaresSubSq =
      { rank := 3, discr := squareClass (-1), finiteHasse := 1,
        realPositiveIndex := fun _ => 2 } := by
  have hQ : sumTwoSquaresSubSq = weightedSumSquares ℚ ![1, ((1 : ℚˣ) : ℚ), -((1 : ℚˣ) : ℚ)] := by
    simp [sumTwoSquaresSubSq_def]
  rw [← globalInvariants_weightedSumSquares_one_self_neg 1 (hQ ▸ nondegenerate_sumTwoSquaresSubSq)]
  congr

/-- The system of local invariants of `⟨1, 2, -2⟩`: it is the same as that of `⟨1, 1, -1⟩`. -/
theorem globalInvariants_sqAddTwoSqSubTwoSq :
    sqAddTwoSqSubTwoSq.globalInvariants nondegenerate_sqAddTwoSqSubTwoSq =
      { rank := 3, discr := squareClass (-1), finiteHasse := 1,
        realPositiveIndex := fun _ => 2 } := by
  have hQ : sqAddTwoSqSubTwoSq =
      weightedSumSquares ℚ ![1, ((Units.mk0 2 two_ne_zero : ℚˣ) : ℚ),
        -((Units.mk0 2 two_ne_zero : ℚˣ) : ℚ)] := by
    simp [sqAddTwoSqSubTwoSq_def]
  rw [← globalInvariants_weightedSumSquares_one_self_neg _
    (hQ ▸ nondegenerate_sqAddTwoSqSubTwoSq)]
  congr

end TauCeti.NumberField.QuadraticForm
