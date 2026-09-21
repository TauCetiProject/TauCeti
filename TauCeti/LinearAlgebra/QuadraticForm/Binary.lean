/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.LinearCombination

/-!
# Binary diagonal quadratic forms in normal form

A *binary* form here is a diagonal form in two variables, that is
`QuadraticMap.weightedSumSquares R ![a, b] : QuadraticForm R (Fin 2 → R)`, classically written
`⟨a, b⟩`. This file proves the two normal-form theorems that pin such a form down.

The first is the **representation normal form**: a unit `c` is represented by `⟨a, b⟩` exactly
when `c` may be taken as the first coefficient, the second being forced to `a * b * c`. Its
content is a single explicit change of variables. If `a x² + b y² = c` with `c` invertible, then
the vector `(x, y)` and its orthogonal companion `(-b y, a x)` form a basis, because the
determinant of the pair is exactly `c`, and reading `⟨a, b⟩` in that basis gives `⟨c, a b c⟩`.
Since `a * b * c` and `a * b * c⁻¹` differ by the square `c²`, the two spellings of the second
coefficient found in the sources present the same form. Only the *represented* value has to be a
unit here, so this half of the theory is developed over a commutative ring.

The second is the **binary equivalence criterion**: two binary forms with unit coefficients are
isometric exactly when they have the same discriminant modulo squares and represent a common
unit. One direction follows from the discriminant change-of-variables formula; the other applies
the representation normal form to both sides and compares the forced second coefficients.

Both statements are about the *unit* value set `QuadraticMap.unitValueSet`. Invertibility of the
represented value carries the whole content of the first theorem: every quadratic form represents
`0` through the zero vector, so a reading at `c = 0` says nothing.

## Main definitions

* `TauCeti.isometryEquivBinaryNormalForm`: the change of variables carrying `⟨c, a b c⟩` to
  `⟨a, b⟩`, built from a solution of `a x² + b y² = c`.

## Main results

* `TauCeti.mem_unitValueSet_binary_iff_equivalent`: the representation normal form, Lam I.2.3 (2).
* `TauCeti.equivalent_binaryNormalForm_inv`: the two spellings `a b c` and `a b c⁻¹` of the
  forced second coefficient present the same form.
* `TauCeti.isSquare_mul_mul_of_equivalent_binary`: isometric binary forms have equal
  discriminants modulo squares.
* `TauCeti.equivalent_binary_iff`: the binary equivalence criterion, Lam I.5.1.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Proposition 2.3 and Proposition 5.1.
-/

public section

open QuadraticMap

namespace TauCeti

universe u

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- A binary diagonal form represents its first coefficient. -/
theorem represents_binary_left (a b : R) : Represents (weightedSumSquares R ![a, b]) a :=
  (represents_iff _ _).mpr <| Set.mem_range.mpr
    ⟨![1, 0], by simp [weightedSumSquares_apply, Fin.sum_univ_two]⟩

/-- The first coefficient of a binary diagonal form lies in its unit value set. -/
theorem mem_unitValueSet_binary_left (a : Rˣ) (b : R) :
    a ∈ unitValueSet (weightedSumSquares R ![(a : R), b]) :=
  mem_unitValueSet.mpr (represents_binary_left _ _)

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- The **binary representation normal form** as an explicit change of variables: a solution of
`a x² + b y² = c` with `c` invertible carries `⟨c, a * b * c⟩` to `⟨a, b⟩`.

The map sends the first standard basis vector to `(x, y)`, on which `⟨a, b⟩` takes the value `c`,
and the second to the orthogonal companion `(-b y, a x)`, on which `⟨a, b⟩` takes the value
`a * b * c`. Its determinant is `a x² + b y² = c`, which is why the hypothesis asks for a unit. -/
def isometryEquivBinaryNormalForm (a b x y : R) (c : Rˣ) (h : a * x ^ 2 + b * y ^ 2 = c) :
    (weightedSumSquares R ![(c : R), a * b * c]).IsometryEquiv (weightedSumSquares R ![a, b]) where
  toFun v := ![x * v 0 - b * y * v 1, y * v 0 + a * x * v 1]
  invFun v := ![(↑c⁻¹ : R) * (a * x * v 0 + b * y * v 1), (↑c⁻¹ : R) * (x * v 1 - y * v 0)]
  map_add' u v := by
    ext i
    fin_cases i <;> · simp; ring
  map_smul' r v := by
    ext i
    fin_cases i <;> · simp; ring
  left_inv v := by
    have hc : (↑c⁻¹ : R) * (a * x ^ 2 + b * y ^ 2) = 1 := by rw [h]; exact c.inv_mul
    ext i
    fin_cases i <;> simp
    · linear_combination v 0 * hc
    · linear_combination v 1 * hc
  right_inv v := by
    have hc : (↑c⁻¹ : R) * (a * x ^ 2 + b * y ^ 2) = 1 := by rw [h]; exact c.inv_mul
    ext i
    fin_cases i <;> simp
    · linear_combination v 0 * hc
    · linear_combination v 1 * hc
  map_app' v := by
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    linear_combination (v 0 * v 0 + a * b * (v 1 * v 1)) * h

/-- The explicit coordinates of the isometry on a vector. -/
@[simp]
theorem isometryEquivBinaryNormalForm_apply (a b x y : R) (c : Rˣ)
    (h : a * x ^ 2 + b * y ^ 2 = c) (v : Fin 2 → R) :
    isometryEquivBinaryNormalForm a b x y c h v =
      ![x * v 0 - b * y * v 1, y * v 0 + a * x * v 1] :=
  (rfl)

/-- The explicit coordinates of the inverse isometry on a vector. -/
@[simp]
theorem isometryEquivBinaryNormalForm_symm_apply (a b x y : R) (c : Rˣ)
    (h : a * x ^ 2 + b * y ^ 2 = c) (v : Fin 2 → R) :
    (isometryEquivBinaryNormalForm a b x y c h).symm v =
      ![(↑c⁻¹ : R) * (a * x * v 0 + b * y * v 1),
        (↑c⁻¹ : R) * (x * v 1 - y * v 0)] :=
  (rfl)

/-- **The binary representation normal form**, Lam I.2.3 (2): a unit represented by a binary
diagonal form may be taken as its first coefficient. -/
theorem equivalent_binaryNormalForm_of_mem_unitValueSet {a b : R} {c : Rˣ}
    (h : c ∈ unitValueSet (weightedSumSquares R ![a, b])) :
    (weightedSumSquares R ![a, b]).Equivalent
      (weightedSumSquares R ![(c : R), a * b * c]) := by
  obtain ⟨v, hv⟩ := Set.mem_range.mp
    ((represents_iff _ _).mp (mem_unitValueSet.mp h))
  rw [weightedSumSquares_apply, Fin.sum_univ_two] at hv
  refine ⟨(isometryEquivBinaryNormalForm a b (v 0) (v 1) c ?_).symm⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at hv
  linear_combination hv

/-- **The binary representation normal form**, Lam I.2.3 (2). A binary diagonal form represents a
unit `c` exactly when it is isometric to `⟨c, a * b * c⟩`.

⚠ That `c` is a unit is essential: every quadratic form represents the scalar `0` through the
zero vector, and `⟨a, b⟩` is in general not isometric to `⟨0, 0⟩`. -/
theorem mem_unitValueSet_binary_iff_equivalent (a b : R) (c : Rˣ) :
    c ∈ unitValueSet (weightedSumSquares R ![a, b]) ↔
      (weightedSumSquares R ![a, b]).Equivalent
        (weightedSumSquares R ![(c : R), a * b * c]) := by
  refine ⟨fun h => equivalent_binaryNormalForm_of_mem_unitValueSet h, fun h => ?_⟩
  rw [h.unitValueSet_eq]
  exact mem_unitValueSet_binary_left _ _

/-- The two spellings of the second coefficient of the binary normal form present the same form:
`a * b * c` and `a * b * c⁻¹` differ by the square `c²`, so `⟨c, a b c⟩` and `⟨c, a b c⁻¹⟩` are
isometric.

Sources state the normal form both ways, the second because the square class of the second
coefficient is forced to be that of the discriminant `a * b` divided by `c`. -/
theorem equivalent_binaryNormalForm_inv (a b : R) (c : Rˣ) :
    (weightedSumSquares R ![(c : R), a * b * c]).Equivalent
      (weightedSumSquares R ![(c : R), a * b * (c⁻¹ : Rˣ)]) :=
  ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares ![1, c] (by
    intro i
    fin_cases i
    · simp
    · simp
      linear_combination (a * b * (c : R)) * c.inv_mul)⟩

/-- Two binary diagonal forms with unit coefficients that have the same discriminant modulo
squares and represent a common unit are isometric. This is the substantial direction of
Lam I.5.1, and it needs no assumption on the characteristic. -/
theorem equivalent_binary_of_isSquare_of_mem_unitValueSet {a b c d e : Rˣ}
    (hdisc : IsSquare (a * b * (c * d)))
    (hab : e ∈ unitValueSet (weightedSumSquares R ![(a : R), (b : R)]))
    (hcd : e ∈ unitValueSet (weightedSumSquares R ![(c : R), (d : R)])) :
    (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)]) := by
  obtain ⟨t, ht⟩ := hdisc
  refine (equivalent_binaryNormalForm_of_mem_unitValueSet hab).trans
    (Equivalent.trans ?_
      (equivalent_binaryNormalForm_of_mem_unitValueSet hcd).symm)
  refine ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares ![1, t * (c * d)⁻¹] ?_⟩
  intro i
  fin_cases i
  · simp
  · have hu : c * (d * (e * (t * (c * d)⁻¹) ^ 2)) = a * (b * e) := by
      rw [pow_two]
      calc
        c * (d * (e * ((t * (c * d)⁻¹) * (t * (c * d)⁻¹)))) =
            (t * t) * ((c * d)⁻¹ * (c * d)⁻¹ * (c * d)) * e := by ac_rfl
        _ = (a * b * (c * d)) * ((c * d)⁻¹ * (c * d)⁻¹ * (c * d)) * e := by rw [ht]
        _ = a * (b * e) := by simp [mul_assoc]
    simpa [mul_assoc] using congrArg Units.val hu

/-- Isometric binary diagonal forms with unit coefficients have the same discriminant modulo
squares: the discriminant of `⟨a, b⟩` is `a * b` and that of `⟨c, d⟩` is `c * d`, and the two
agree modulo squares exactly when their product `a * b * (c * d)` is a square. -/
theorem isSquare_mul_mul_of_equivalent_binary [Invertible (2 : R)] {a b c d : Rˣ}
    (h : (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)])) :
    IsSquare (a * b * (c * d)) := by
  obtain ⟨f⟩ := h
  have heq : weightedSumSquares R ![(a : R), (b : R)] =
      (weightedSumSquares R ![(c : R), (d : R)]).comp f.toLinearMap :=
    QuadraticMap.ext fun x => (f.map_app x).symm
  have hdisc := congrArg QuadraticForm.discr' heq
  rw [QuadraticForm.discr'_comp, LinearMap.det_toMatrix'] at hdisc
  have hdiag (x y : Rˣ) :
      QuadraticForm.discr' (weightedSumSquares R ![(x : R), (y : R)]) = (x : R) * y := by
    rw [QuadraticForm.discr', Matrix.det_fin_two]
    simp [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
      QuadraticMap.associated_eq_self_apply, QuadraticMap.associated_apply,
      weightedSumSquares_apply, Fin.sum_univ_two]
  rw [hdiag, hdiag] at hdisc
  refine ⟨LinearEquiv.det f.toLinearEquiv * c * d, Units.ext ?_⟩
  simp only [Units.val_mul, LinearEquiv.coe_det]
  linear_combination ((c : R) * d) * hdisc

/-- **The binary equivalence criterion**, Lam I.5.1. Two binary diagonal forms with unit
coefficients are isometric exactly when their discriminants agree modulo squares and they
represent a common unit.

The quotient-free spelling `IsSquare (a * b * (c * d))` of "equal discriminants" is the one that
`TauCeti.squareClass_eq_zero_iff` translates into the square-class group. -/
theorem equivalent_binary_iff [Invertible (2 : R)] (a b c d : Rˣ) :
    (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
        (weightedSumSquares R ![(c : R), (d : R)]) ↔
      IsSquare (a * b * (c * d)) ∧
        ∃ e : Rˣ, e ∈ unitValueSet (weightedSumSquares R ![(a : R), (b : R)]) ∧
          e ∈ unitValueSet (weightedSumSquares R ![(c : R), (d : R)]) := by
  refine ⟨fun h => ⟨isSquare_mul_mul_of_equivalent_binary h, a,
    mem_unitValueSet_binary_left _ _, ?_⟩,
    fun ⟨hdisc, _, hab, hcd⟩ => equivalent_binary_of_isSquare_of_mem_unitValueSet hdisc hab hcd⟩
  rw [← h.unitValueSet_eq]
  exact mem_unitValueSet_binary_left _ _

end CommRing

/-- **Worked example.** Over `ℚ` the binary forms `⟨1, 1⟩` and `⟨2, 2⟩` are isometric: their
discriminants `1` and `4` agree modulo squares, and both represent `2`, once as `1² + 1²` and once
as `2 · 1² + 2 · 0²`. Concretely `x² + y²` becomes `2 s² + 2 t²` under `(s, t) ↦ (s - t, s + t)`. -/
example : (weightedSumSquares ℚ ![(1 : ℚ), 1]).Equivalent (weightedSumSquares ℚ ![(2 : ℚ), 2]) := by
  have : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have hu : ((Units.mk0 (2 : ℚ) two_ne_zero : ℚˣ) : ℚ) = 2 := rfl
  have key := equivalent_binary_iff (R := ℚ) 1 1 (Units.mk0 2 two_ne_zero)
    (Units.mk0 2 two_ne_zero)
  simp only [hu, Units.val_one] at key
  refine key.mpr ⟨⟨Units.mk0 2 two_ne_zero, by rw [one_mul, one_mul]⟩,
    Units.mk0 2 two_ne_zero, ?_, ?_⟩
  · refine mem_unitValueSet.mpr ((represents_iff _ _).mpr
      (Set.mem_range.mpr ⟨![1, 1], ?_⟩))
    norm_num [weightedSumSquares_apply, Fin.sum_univ_two]
  · simpa [hu] using mem_unitValueSet_binary_left (R := ℚ) (Units.mk0 2 two_ne_zero) 2

end TauCeti
