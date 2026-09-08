/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.Algebra.Ring.Identities
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
unit. One direction is the Brahmagupta–Fibonacci identity applied to the images of the two
standard basis vectors; the other applies the representation normal form to both sides and
compares the forced second coefficients.

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

-- The statements formalised here are the "binary forms in normal form" milestone of Layer 0 of
-- the `TauCetiRoadmap/QuadraticFormInvariants` roadmap, whose `Suggested.lean` fixes the spelling
-- of a binary diagonal form as `weightedSumSquares K ![(a : K), b]`.

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

/-- The coordinates of the change of variables. The body of `isometryEquivBinaryNormalForm` is
not exposed, so this equation lemma is the interface downstream modules rewrite with; the
parentheses around `rfl` elaborate it against the expected type, which unfolds the sealed body. -/
@[simp]
theorem isometryEquivBinaryNormalForm_apply (a b x y : R) (c : Rˣ)
    (h : a * x ^ 2 + b * y ^ 2 = c) (v : Fin 2 → R) :
    isometryEquivBinaryNormalForm a b x y c h v =
      ![x * v 0 - b * y * v 1, y * v 0 + a * x * v 1] :=
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

end CommRing

section Field

variable {K : Type u} [Field K]

/-- Isometric binary diagonal forms with unit coefficients have the same discriminant modulo
squares: the discriminant of `⟨a, b⟩` is `a * b` and that of `⟨c, d⟩` is `c * d`, and the two
agree modulo squares exactly when their product `a * b * (c * d)` is a square. -/
theorem isSquare_mul_mul_of_equivalent_binary [Invertible (2 : K)] {a b c d : Kˣ}
    (h : (weightedSumSquares K ![(a : K), (b : K)]).Equivalent
      (weightedSumSquares K ![(c : K), (d : K)])) :
    IsSquare (a * b * (c * d)) := by
  -- Let `u` and `v` be the images of the two standard basis vectors. Comparing the values at
  -- `(1, 0)`, at `(0, 1)` and at `(1, 1)` shows that `u` and `v` are orthogonal for `⟨c, d⟩`, so
  -- Brahmagupta's identity `sq_add_mul_sq_mul_sq_add_mul_sq`, read at `n = c * d`, collapses to
  -- its second summand.
  obtain ⟨f⟩ := h
  have key : ∀ p : Fin 2 → K,
      (c : K) * f p 0 ^ 2 + (d : K) * f p 1 ^ 2 = (a : K) * p 0 ^ 2 + (b : K) * p 1 ^ 2 := by
    intro p
    have hp := f.map_app p
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul] at hp
    linear_combination hp
  obtain ⟨u, v, hu, hv, hw⟩ : ∃ u v : Fin 2 → K,
      (c : K) * u 0 ^ 2 + (d : K) * u 1 ^ 2 = a ∧
      (c : K) * v 0 ^ 2 + (d : K) * v 1 ^ 2 = b ∧
      (c : K) * (u 0 + v 0) ^ 2 + (d : K) * (u 1 + v 1) ^ 2 = (a : K) + b := by
    refine ⟨f ![1, 0], f ![0, 1], by simpa using key ![1, 0], by simpa using key ![0, 1], ?_⟩
    have hadd : f ![1, 1] = f ![1, 0] + f ![0, 1] := by
      rw [← map_add]
      congr 1
      ext i
      fin_cases i <;> simp
    have := key ![1, 1]
    rw [hadd] at this
    simpa using this
  have hortho : (c : K) * (u 0 * v 0) + (d : K) * (u 1 * v 1) = 0 := by
    have h2 : (2 : K) * ((c : K) * (u 0 * v 0) + (d : K) * (u 1 * v 1)) = 0 := by
      linear_combination hw - hu - hv
    exact (mul_eq_zero.mp h2).resolve_left (isUnit_of_invertible (2 : K)).ne_zero
  have hdet : (a : K) * b = (c : K) * d * (u 0 * v 1 - u 1 * v 0) ^ 2 := by
    -- Brahmagupta's identity at `n = c * d` reads `c² a b = c² (c u₀v₀ + d u₁v₁)²
    -- + c² · c d (u₀v₁ - u₁v₀)²`, whose first summand vanishes by `hortho`.
    have brahmagupta := sq_add_mul_sq_mul_sq_add_mul_sq (n := (c : K) * d)
      (x₁ := (c : K) * u 0) (x₂ := u 1) (y₁ := (c : K) * v 0) (y₂ := -v 1)
    refine mul_left_cancel₀ (mul_ne_zero c.ne_zero c.ne_zero) ?_
    linear_combination brahmagupta - (c : K) ^ 2 * b * hu
      - (c : K) ^ 2 * ((c : K) * u 0 ^ 2 + (d : K) * u 1 ^ 2) * hv
      + (c : K) ^ 2 * ((c : K) * (u 0 * v 0) + (d : K) * (u 1 * v 1)) * hortho
  have hne : u 0 * v 1 - u 1 * v 0 ≠ 0 := fun h0 =>
    mul_ne_zero a.ne_zero b.ne_zero (by rw [hdet, h0]; ring)
  refine ⟨c * d * Units.mk0 _ hne, Units.ext ?_⟩
  simp only [Units.val_mul, Units.val_mk0]
  linear_combination ((c : K) * d) * hdet

/-- Two binary diagonal forms with unit coefficients that have the same discriminant modulo
squares and represent a common unit are isometric. This is the substantial direction of
Lam I.5.1, and it needs no assumption on the characteristic. -/
theorem equivalent_binary_of_isSquare_of_mem_unitValueSet {a b c d e : Kˣ}
    (hdisc : IsSquare (a * b * (c * d)))
    (hab : e ∈ unitValueSet (weightedSumSquares K ![(a : K), (b : K)]))
    (hcd : e ∈ unitValueSet (weightedSumSquares K ![(c : K), (d : K)])) :
    (weightedSumSquares K ![(a : K), (b : K)]).Equivalent
      (weightedSumSquares K ![(c : K), (d : K)]) := by
  obtain ⟨t, ht⟩ := hdisc
  have ht' : (a : K) * b * ((c : K) * d) = (t : K) * t := congrArg Units.val ht
  refine (equivalent_binaryNormalForm_of_mem_unitValueSet hab).trans
    (Equivalent.trans ?_
      (equivalent_binaryNormalForm_of_mem_unitValueSet hcd).symm)
  refine ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares ![1, t * (c * d)⁻¹] ?_⟩
  intro i
  fin_cases i
  · simp
  · simp
    field_simp
    linear_combination -ht'

/-- **The binary equivalence criterion**, Lam I.5.1. Two binary diagonal forms with unit
coefficients are isometric exactly when their discriminants agree modulo squares and they
represent a common unit.

The quotient-free spelling `IsSquare (a * b * (c * d))` of "equal discriminants" is the one that
`TauCeti.squareClass_eq_zero_iff` translates into the square-class group. -/
theorem equivalent_binary_iff [Invertible (2 : K)] (a b c d : Kˣ) :
    (weightedSumSquares K ![(a : K), (b : K)]).Equivalent
        (weightedSumSquares K ![(c : K), (d : K)]) ↔
      IsSquare (a * b * (c * d)) ∧
        ∃ e : Kˣ, e ∈ unitValueSet (weightedSumSquares K ![(a : K), (b : K)]) ∧
          e ∈ unitValueSet (weightedSumSquares K ![(c : K), (d : K)]) := by
  refine ⟨fun h => ⟨isSquare_mul_mul_of_equivalent_binary h, a,
    mem_unitValueSet_binary_left _ _, ?_⟩,
    fun ⟨hdisc, _, hab, hcd⟩ => equivalent_binary_of_isSquare_of_mem_unitValueSet hdisc hab hcd⟩
  rw [← h.unitValueSet_eq]
  exact mem_unitValueSet_binary_left _ _

end Field

/-- **Worked example.** Over `ℚ` the binary forms `⟨1, 1⟩` and `⟨2, 2⟩` are isometric: their
discriminants `1` and `4` agree modulo squares, and both represent `2`, once as `1² + 1²` and once
as `2 · 1² + 2 · 0²`. Concretely `x² + y²` becomes `2 s² + 2 t²` under `(s, t) ↦ (s - t, s + t)`.

This is the smallest instance in which a nontrivial isometry of diagonal forms is produced by the
criterion, and it is the single binary move that Witt's chain-equivalence theorem starts from. -/
example : (weightedSumSquares ℚ ![(1 : ℚ), 1]).Equivalent (weightedSumSquares ℚ ![(2 : ℚ), 2]) := by
  have : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have hu : ((Units.mk0 (2 : ℚ) two_ne_zero : ℚˣ) : ℚ) = 2 := rfl
  have key := equivalent_binary_iff (K := ℚ) 1 1 (Units.mk0 2 two_ne_zero)
    (Units.mk0 2 two_ne_zero)
  simp only [hu, Units.val_one] at key
  refine key.mpr ⟨⟨Units.mk0 2 two_ne_zero, by rw [one_mul, one_mul]⟩,
    Units.mk0 2 two_ne_zero, ?_, ?_⟩
  · refine mem_unitValueSet.mpr ((represents_iff _ _).mpr
      (Set.mem_range.mpr ⟨![1, 1], ?_⟩))
    norm_num [weightedSumSquares_apply, Fin.sum_univ_two]
  · simpa [hu] using mem_unitValueSet_binary_left (R := ℚ) (Units.mk0 2 two_ne_zero) 2

end TauCeti
