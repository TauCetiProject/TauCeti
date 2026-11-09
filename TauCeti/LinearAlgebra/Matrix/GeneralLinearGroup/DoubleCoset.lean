/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Determinants along a double coset of `GL ι R`

The determinant is constant on a double coset `s * {g} * t` as soon as every coefficient has
determinant one. Nothing here is arithmetic: the argument is multiplicativity of `Matrix.det`,
so it holds over any commutative ring and any finite index type.

The arithmetic consumers — `SL_n(ℤ)` and the congruence subgroups inside it — specialise this
in `TauCeti.NumberTheory.HeckeRing.GLn.Basic`.

## Main results

* `DoubleCoset.det_eq_of_mem_doubleCoset_of_det_eq_one`: the determinant is constant on a
  double coset whose coefficient sets have determinant one.
-/

public section

open Matrix

namespace DoubleCoset

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

end DoubleCoset
