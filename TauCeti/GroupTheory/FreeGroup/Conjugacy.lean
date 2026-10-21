/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.Group.Conj

/-!
# Conjugacy and cyclic rotation in free groups

Rotating a word conjugates the free-group element it represents. Together with Mathlib's
explicit cyclic-reduction conjugator, this relates rotation of cyclic reductions to
conjugacy of the original elements.

The explicit cyclic-reduction conjugator uses Mathlib's
`FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically` from
`Mathlib.GroupTheory.FreeGroup.CyclicallyReduced`.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- Rotating a word is conjugation by the inverse of its initial segment. -/
theorem conj_mk_rotate (u : List (α × Bool)) (n : ℕ) :
    (mk (u.take (n % u.length)))⁻¹ * mk u * mk (u.take (n % u.length)) =
      mk (u.rotate n) := by
  let p := u.take (n % u.length)
  let q := u.drop (n % u.length)
  have hu : u = p ++ q := (List.take_append_drop _ _).symm
  have hv : u.rotate n = q ++ p := List.rotate_eq_drop_append_take_mod
  calc
    _ = (mk p)⁻¹ * (mk p * mk q) * mk p := by rw [mul_mk, ← hu]
    _ = mk q * mk p := by rw [inv_mul_cancel_left]
    _ = mk (u.rotate n) := by rw [hv, ← mul_mk]

/-- Two words related by a cyclic rotation represent conjugate elements of a free group.
The words need not be reduced. -/
theorem isConj_mk_of_isRotated {u v : List (α × Bool)} (h : u.IsRotated v) :
    IsConj (mk u) (mk v) := by
  obtain ⟨n, rfl⟩ := h
  exact isConj_iff.mpr ⟨(mk (u.take (n % u.length)))⁻¹,
    by simpa only [inv_inv] using conj_mk_rotate u n⟩

/-- The cyclic reduction of any word has an explicit group conjugator. -/
theorem mk_conjugator_mul_mk_reduceCyclically (L : List (α × Bool)) [DecidableEq α] :
    mk (reduceCyclically.conjugator L) *
        mk (reduceCyclically L) *
        (mk (reduceCyclically.conjugator L))⁻¹ = mk L := by
  rw [inv_mk, mul_mk, mul_mk, reduceCyclically.conj_conjugator_reduceCyclically]

/-- The element of any word is conjugate to the element of its cyclic reduction. -/
theorem isConj_mk_reduceCyclically (L : List (α × Bool)) [DecidableEq α] :
    IsConj (mk L) (mk (reduceCyclically L)) := by
  apply IsConj.symm
  exact isConj_iff.mpr ⟨mk (reduceCyclically.conjugator L),
    mk_conjugator_mul_mk_reduceCyclically L⟩

/-- Elements whose cyclic reductions differ by a rotation are conjugate. -/
theorem isConj_of_isRotated_reduceCyclically [DecidableEq α] {x y : FreeGroup α}
    (h : (reduceCyclically x.toWord).IsRotated (reduceCyclically y.toWord)) :
    IsConj x y := by
  simpa only [mk_toWord] using
    (isConj_mk_reduceCyclically x.toWord).trans <|
      (isConj_mk_of_isRotated h).trans (isConj_mk_reduceCyclically y.toWord).symm

end FreeGroup
