/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Coordinates of tuples in a finite basis

A finite basis `b` of `M`, indexed by `ι`, identifies `M` with `ι → R` through
`Module.Basis.equivFun`. Applying this to each entry of a `J`-indexed tuple and uncurrying
identifies `J → M` with functions on `J × ι`; the index type `J` need not be finite.

## Main results

* `Module.Basis.piEquivFun`: the coordinates of `J`-indexed tuples in a finite basis.
* `Module.Basis.piEquivFun_apply`: each coordinate of a tuple is a basis coordinate of an entry.
* `Module.Basis.repr_piEquivFun_symm_apply`: the tuple with prescribed coordinates has those
  basis coordinates.
-/

public section

namespace Module.Basis

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Finite ι]

variable (J : Type*) in
/-- Coordinates in a finite basis `b` identify `J`-indexed tuples of vectors with functions on
the pairs of an index in `J` and a basis index. -/
noncomputable def piEquivFun (b : Basis ι R M) : (J → M) ≃ₗ[R] (J × ι → R) :=
  (LinearEquiv.piCongrRight fun _ => b.equivFun).trans (LinearEquiv.curry R R J ι).symm

/-- A coordinate of a tuple is the corresponding basis coordinate of an entry. -/
@[simp] theorem piEquivFun_apply {J : Type*} (b : Basis ι R M) (v : J → M) (i : J × ι) :
    b.piEquivFun J v i = b.repr (v i.1) i.2 := by
  simp [piEquivFun, Function.uncurry]

/-- The tuple with prescribed coordinates has those basis coordinates. -/
@[simp] theorem repr_piEquivFun_symm_apply {J : Type*} (b : Basis ι R M) (a : J × ι → R)
    (j : J) (i : ι) : b.repr ((b.piEquivFun J).symm a j) i = a (j, i) := by
  have h := b.piEquivFun_apply ((b.piEquivFun J).symm a) (j, i)
  rwa [LinearEquiv.apply_symm_apply, eq_comm] at h

end Module.Basis
