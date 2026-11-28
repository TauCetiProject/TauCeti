/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The determinant-sign decomposition of the orthogonal group

Over a commutative ring without zero divisors in which `2 ≠ 0`, an orthogonal matrix has
determinant `1` or `-1`, and the two values are distinct. Fixing a coordinate `i`, the diagonal
reflection `r` negating `i` has determinant `-1` and squares to the identity, so every orthogonal
matrix `A` is uniquely either a special orthogonal matrix `S` (when `det A = 1`) or a product
`S * r` with `S` special orthogonal (when `det A = -1`). This is the decomposition of the
orthogonal group into the two cosets of the special orthogonal group, packaged as an equivalence
of types `orthogonalGroup n R ≃ specialOrthogonalGroup n R × Bool`, the Boolean recording
whether the determinant is `-1`.

The equivalence is only a bijection of carriers. It is not a group isomorphism with a direct
product: for instance the orthogonal group in dimension two is not commutative, while the
special orthogonal group in dimension two is.

Counting both sides, `Nat.card` of the orthogonal group is twice that of the special orthogonal
group whenever the index type is nonempty. For a finite coefficient ring, such as a finite field
of odd characteristic, this is the familiar index-two count; when the groups are infinite both
sides are `0`. For an empty index type both groups are trivial, of cardinality `1`, and the factor
two fails.

## Main definitions

* `TauCeti.orthogonalGroupEquivSpecialOrthogonalGroupProdBool`: the determinant-sign
  decomposition of the orthogonal group, relative to a chosen coordinate.

## Main declarations

* `TauCeti.coe_orthogonalDiagonalReflection_mul_self`: the diagonal reflection is an involution.
* `TauCeti.coe_orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_fst` and
  `TauCeti.orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_snd`: the forward formulas.
* `TauCeti.coe_orthogonalGroupEquivSpecialOrthogonalGroupProdBool_symm_apply`: the inverse
  formula, multiplying by the diagonal reflection exactly on the determinant `-1` coset.
* `TauCeti.orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_snd_eq_false_iff` and
  `TauCeti.det_orthogonalGroupEquivSpecialOrthogonalGroupProdBool_symm_apply`: the flag selects
  the determinant sign in both directions.
* `TauCeti.card_orthogonalGroup_eq_two_mul_card_specialOrthogonalGroup`: the orthogonal group has
  twice as many elements as the special orthogonal group over a nonempty index type.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section DeterminantSign

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (R : Type*) [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]

omit [NoZeroDivisors R] [NeZero (2 : R)] in
/-- The diagonal reflection negating one coordinate is an involution. -/
theorem coe_orthogonalDiagonalReflection_mul_self (i : n) :
    (orthogonalDiagonalReflection R i : Matrix n n R) * orthogonalDiagonalReflection R i = 1 := by
  rw [coe_orthogonalDiagonalReflection, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

omit [NoZeroDivisors R] [NeZero (2 : R)] in
/-- Multiplying an orthogonal matrix of determinant `-1` by a diagonal reflection gives a special
orthogonal matrix. -/
private theorem mul_orthogonalDiagonalReflection_mem_specialOrthogonalGroup
    {A : Matrix n n R} (hA : A ∈ orthogonalGroup n R) (h : A.det = -1) (i : n) :
    A * (orthogonalDiagonalReflection R i : Matrix n n R) ∈ specialOrthogonalGroup n R := by
  rw [mem_specialOrthogonalGroup_iff, det_mul, det_orthogonalDiagonalReflection, h]
  exact ⟨Submonoid.mul_mem _ hA (orthogonalDiagonalReflection R i).property, by ring⟩

open Classical in
/-- The determinant-sign decomposition of the orthogonal group relative to the coordinate `i`:
an orthogonal matrix of determinant `1` is sent to itself with the flag `false`, and one of
determinant `-1` is sent to its product with the diagonal reflection negating `i`, with the flag
`true`. This is an equivalence of types only, not a group isomorphism with a direct product. -/
def orthogonalGroupEquivSpecialOrthogonalGroupProdBool (i : n) :
    orthogonalGroup n R ≃ specialOrthogonalGroup n R × Bool where
  toFun A :=
    if h : (A : Matrix n n R).det = 1 then
      (⟨A, (mem_specialOrthogonalGroup_iff).2 ⟨A.property, h⟩⟩, false)
    else
      (⟨A * (orthogonalDiagonalReflection R i : Matrix n n R),
        mul_orthogonalDiagonalReflection_mem_specialOrthogonalGroup R A.property
          ((det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property).resolve_left h) i⟩, true)
  invFun p :=
    ⟨if p.2 then p.1 * (orthogonalDiagonalReflection R i : Matrix n n R) else p.1, by
      split
      · exact Submonoid.mul_mem _ ((mem_specialOrthogonalGroup_iff).1 p.1.property).1
          (orthogonalDiagonalReflection R i).property
      · exact ((mem_specialOrthogonalGroup_iff).1 p.1.property).1⟩
  left_inv A := by
    dsimp only
    by_cases h : (A : Matrix n n R).det = 1
    · rw [dite_eq_left h]
      rfl
    · rw [dite_eq_right h]
      refine Subtype.ext ?_
      change (A : Matrix n n R) * _ * _ = A
      rw [Matrix.mul_assoc, coe_orthogonalDiagonalReflection_mul_self, Matrix.mul_one]
  right_inv p := by
    obtain ⟨⟨S, hS⟩, b⟩ := p
    have hdet := ((mem_specialOrthogonalGroup_iff).1 hS).2
    cases b
    · exact dite_eq_left hdet
    · have h : (S * (orthogonalDiagonalReflection R i : Matrix n n R)).det ≠ 1 := by
        rw [det_mul, det_orthogonalDiagonalReflection, hdet, one_mul]
        exact fun h' => two_ne_zero (α := R) (by linear_combination -h')
      refine (dite_eq_right h).trans (Prod.ext (Subtype.ext ?_) rfl)
      change S * _ * _ = S
      rw [Matrix.mul_assoc, coe_orthogonalDiagonalReflection_mul_self, Matrix.mul_one]

open Classical in
/-- The special orthogonal component of the determinant-sign decomposition is the matrix itself
on determinant `1`, and its product with the diagonal reflection otherwise. -/
@[simp]
theorem coe_orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_fst (i : n)
    (A : orthogonalGroup n R) :
    ((orthogonalGroupEquivSpecialOrthogonalGroupProdBool R i A).1 : Matrix n n R) =
      if (A : Matrix n n R).det = 1 then (A : Matrix n n R)
      else A * (orthogonalDiagonalReflection R i : Matrix n n R) := by
  by_cases h : (A : Matrix n n R).det = 1 <;>
    simp only [orthogonalGroupEquivSpecialOrthogonalGroupProdBool, Equiv.coe_fn_mk, h,
      ↓reduceDIte, ↓reduceIte]

open Classical in
/-- The Boolean component of the determinant-sign decomposition records whether the determinant
is `-1`. -/
@[simp]
theorem orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_snd (i : n)
    (A : orthogonalGroup n R) :
    (orthogonalGroupEquivSpecialOrthogonalGroupProdBool R i A).2 =
      decide ((A : Matrix n n R).det = -1) := by
  by_cases h : (A : Matrix n n R).det = 1
  · have hne : (1 : R) ≠ -1 := fun h' => two_ne_zero (α := R) (by linear_combination h')
    rw [h, decide_eq_false hne]
    exact congrArg Prod.snd (dite_eq_left h)
  · rw [(det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property).resolve_left h,
      decide_eq_true rfl]
    exact congrArg Prod.snd (dite_eq_right h)

/-- The Boolean component of the determinant-sign decomposition is `false` exactly on the
special orthogonal matrices. -/
theorem orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_snd_eq_false_iff (i : n)
    (A : orthogonalGroup n R) :
    (orthogonalGroupEquivSpecialOrthogonalGroupProdBool R i A).2 = false ↔
      (A : Matrix n n R).det = 1 := by
  rw [orthogonalGroupEquivSpecialOrthogonalGroupProdBool_apply_snd, decide_eq_false_iff_not]
  constructor
  · exact (det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property).resolve_right
  · rintro h h'
    exact two_ne_zero (α := R) (by linear_combination h' - h)

/-- The inverse of the determinant-sign decomposition multiplies by the diagonal reflection
exactly when the flag is `true`. -/
@[simp]
theorem coe_orthogonalGroupEquivSpecialOrthogonalGroupProdBool_symm_apply (i : n)
    (S : specialOrthogonalGroup n R) (b : Bool) :
    ((orthogonalGroupEquivSpecialOrthogonalGroupProdBool R i).symm (S, b) : Matrix n n R) =
      if b then S * (orthogonalDiagonalReflection R i : Matrix n n R) else S :=
  (rfl)

/-- The inverse of the determinant-sign decomposition lands in determinant `-1` exactly when the
flag is `true`, and in determinant `1` otherwise. -/
theorem det_orthogonalGroupEquivSpecialOrthogonalGroupProdBool_symm_apply (i : n)
    (S : specialOrthogonalGroup n R) (b : Bool) :
    ((orthogonalGroupEquivSpecialOrthogonalGroupProdBool R i).symm (S, b) :
        Matrix n n R).det = if b then -1 else 1 := by
  have hdet := ((mem_specialOrthogonalGroup_iff).1 S.property).2
  cases b
  · exact hdet
  · change (S * (orthogonalDiagonalReflection R i : Matrix n n R)).det = -1
    rw [det_mul, det_orthogonalDiagonalReflection, hdet, one_mul]

end DeterminantSign

/-- Over a nonempty index type, and a commutative ring without zero divisors in which `2 ≠ 0`,
`Nat.card` of the orthogonal group is twice that of the special orthogonal group. Over a finite
field of odd characteristic this counts the two determinant cosets; when the groups are infinite
both sides are `0`. -/
theorem card_orthogonalGroup_eq_two_mul_card_specialOrthogonalGroup {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (R : Type*) [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)] :
    Nat.card (orthogonalGroup n R) = 2 * Nat.card (specialOrthogonalGroup n R) := by
  rw [Nat.card_congr (orthogonalGroupEquivSpecialOrthogonalGroupProdBool R
    (Classical.arbitrary n)), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

section IsEmpty

variable {n : Type*} [Fintype n] [DecidableEq n] [IsEmpty n] (R : Type*) [CommRing R]

/-- Over an empty index type the orthogonal group has exactly one element. -/
example : Nat.card (orthogonalGroup n R) = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

/-- Over an empty index type the special orthogonal group has exactly one element. -/
example : Nat.card (specialOrthogonalGroup n R) = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

end IsEmpty

end TauCeti
