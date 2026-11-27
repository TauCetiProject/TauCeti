/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ColumnRowFixing

/-!
# `SL₂` in two rows and columns of `GL_ι`

For indices `a` and `a'` of a finite type `ι`, `TauCeti.rootSL R a a'` is the copy of `SL₂(R)`
inside `GL_ι(R)` acting on the coordinates `a` and `a'`: the invertible matrices of determinant
`1` that agree with the identity matrix at `(i, j)` unless both `i` and `j` are among `a`, `a'`.
It is built from `TauCeti.columnRowFixingSubgroup` and the kernel of the determinant.

## Main definitions

* `TauCeti.rootSL R a a'`: the group `SL₂^{a,a'}(R)`.

## Main results

* `TauCeti.mem_rootSL_iff`: membership in terms of entries and the determinant.

The definition is adapted from `New.rootSL` in the file
`New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

@[expose] public section

open Matrix

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R]

/-- The group `SL₂(R)` placed in the rows and columns `a`, `a'` of `GL_ι(R)`: the matrices of
determinant `1` that agree with the identity matrix at `(i, j)` unless both `i` and `j` are among
`a`, `a'`. It is trivial for `a = a'`. -/
def rootSL (a a' : ι) : Subgroup (GL ι R) :=
  columnRowFixingSubgroup R ({a, a'}ᶜ : Set ι) {a, a'}ᶜ ⊓ GeneralLinearGroup.det.ker

variable {R}

/-- A matrix lies in `rootSL R a a'` if it has determinant `1` and agrees with the identity
matrix at every entry outside the rows and columns `a`, `a'`. -/
theorem mem_rootSL_iff {a a' : ι} {g : GL ι R} :
    g ∈ rootSL R a a' ↔
      (∀ i j, (i ≠ a ∧ i ≠ a') ∨ (j ≠ a ∧ j ≠ a') → (g : Matrix ι ι R) i j = (1 : Matrix ι ι R) i j)
        ∧ (g : Matrix ι ι R).det = 1 := by
  simp only [rootSL, Subgroup.mem_inf, mem_columnRowFixingSubgroup_iff, MonoidHom.mem_ker,
    Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
  constructor
  · rintro ⟨⟨hc, hr⟩, hdet⟩
    exact ⟨fun i j h ↦ h.elim (fun hi ↦ hr i (by simpa using hi) j)
      (fun hj ↦ hc j (by simpa using hj) i), hdet⟩
  · rintro ⟨h, hdet⟩
    exact ⟨⟨fun j hj i ↦ h i j (.inr (by simpa using hj)),
      fun i hi j ↦ h i j (.inl (by simpa using hi))⟩, hdet⟩

end TauCeti
