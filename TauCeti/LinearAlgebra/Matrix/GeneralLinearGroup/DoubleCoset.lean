/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Determinants and negation along a double coset of `GL ι R`

The determinant is constant on a double coset `s * {g} * t` as soon as every coefficient has
determinant one, and negating a matrix leaves its `(H, t)`-double coset unchanged whenever `-1`
belongs to `H`. Nothing here is arithmetic: the arguments hold over any commutative ring (resp.
ring) and any finite index type.

The arithmetic consumers — `SL_n(ℤ)`, `GL_n(ℤ)`, and the congruence subgroups inside them —
specialise these in `TauCeti.NumberTheory.HeckeRing.GLn.Basic` and
`TauCeti.NumberTheory.HeckeRing.GLn.Rational`.

## Main results

* `DoubleCoset.det_eq_of_mem_doubleCoset_of_det_eq_one`: the determinant is constant on a
  double coset whose coefficient sets have determinant one.
* `DoubleCoset.doubleCoset_neg_of_neg_one_mem_left`: negating a matrix leaves its `(H, t)`-double
  coset unchanged when `-1 ∈ H`.
-/

public section

open Matrix
open scoped Pointwise

namespace DoubleCoset

section Det

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The determinant is constant on a double coset `s * {a} * t` whose coefficient sets `s` and
`t` consist of matrices of determinant one. -/
lemma det_eq_of_mem_doubleCoset_of_det_eq_one {s t : Set (GL ι R)}
    (hs : ∀ γ ∈ s, (↑γ : Matrix ι ι R).det = 1)
    (ht : ∀ γ ∈ t, (↑γ : Matrix ι ι R).det = 1) {a b : GL ι R}
    (hb : b ∈ doubleCoset a s t) :
    (↑b : Matrix ι ι R).det = (↑a : Matrix ι ι R).det := by
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := mem_doubleCoset.mp hb
  simp [hs γ₁ hγ₁, ht γ₂ hγ₂]

end Det

/-- Whenever `-1` belongs to the left subgroup `H`, negating a matrix in `GL ι R` leaves its
`(H, t)`-double coset unchanged. -/
lemma doubleCoset_neg_of_neg_one_mem_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [Ring R] {H : Subgroup (GL ι R)} {t : Set (GL ι R)}
    (hneg : (-1 : GL ι R) ∈ H) (g : GL ι R) :
    doubleCoset (-g) H t = doubleCoset g H t := by
  rw [doubleCoset, ← neg_one_mul, ← Set.singleton_mul_singleton, ← mul_assoc,
    Subgroup.subgroup_mul_singleton hneg, ← doubleCoset]

end DoubleCoset
