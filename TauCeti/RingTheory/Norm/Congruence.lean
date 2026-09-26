/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs

/-!
# The norm only sees its argument modulo a multiplier it kills

`Algebra.norm R : S →* R` is the determinant of multiplication in a basis, so it is a polynomial
in the coordinates of its argument. Consequently it is compatible with reduction: if a ring
homomorphism `f : R →+* R'` kills `a`, then `f` cannot tell `Algebra.norm R (x + a • y)` from
`Algebra.norm R x`.

The proof is exactly that observation. Multiplication by `x + a • y` has matrix
`leftMulMatrix x + a • leftMulMatrix y` in a fixed basis, `f` kills the second summand entrywise,
and the determinant commutes with applying `f` to every entry. Neither freeness nor finiteness is
assumed: when `S` has no finite `R`-basis both norms are Mathlib's junk value `1`.

The intended reading is a congruence. Over `ℤ` with `f` the reduction `ℤ →+* ZMod M` and `a = M`,
this says the integer norm of an algebraic integer is determined modulo `M` by that integer
modulo `M` — so a norm residue is constant on cosets of `M • S`, which is what lets a count of
algebraic integers with a prescribed norm residue be organised by cosets of a sublattice.

## Main results

* `TauCeti.Algebra.map_norm_add_smul_of_map_eq_zero`: a ring homomorphism killing `a` identifies
  the norms of `x + a • y` and `x`.
-/

public section

namespace TauCeti

namespace Algebra

/-- **The norm is unchanged modulo anything that kills the multiplier.** If `f : R →+* R'` sends
`a` to zero, it sends `Algebra.norm R (x + a • y)` and `Algebra.norm R x` to the same element.

Read over `ℤ →+* ZMod M` with `a = M`, this is the statement that the norm residue modulo `M`
depends only on the argument modulo `M`. No hypothesis relates `x` and `y`; the whole content is
that the perturbation is a multiple of something `f` annihilates. (If `S` has no finite `R`-basis
both norms are `1`, so neither freeness nor finiteness is needed.) -/
theorem map_norm_add_smul_of_map_eq_zero {R S R' : Type*} [CommRing R] [Ring S] [CommRing R']
    [Algebra R S] (f : R →+* R') {a : R} (ha : f a = 0) (x y : S) :
    f (Algebra.norm R (x + a • y)) = f (Algebra.norm R x) := by
  classical
  by_cases h : ∃ s : Finset S, Nonempty (Module.Basis s R S)
  · obtain ⟨s, ⟨b⟩⟩ := h
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det,
      RingHom.map_det, map_add, map_smul]
    congr 1
    ext i j
    simp [ha]
  · -- with no finite basis both norms are Mathlib's junk value `1`
    simp [Algebra.norm_eq_one_of_not_exists_basis R h]

end Algebra

end TauCeti
