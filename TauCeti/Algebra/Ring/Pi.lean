/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod

/-!
# Product ring equivalences: coordinate slices and zero-factor elimination

Records multiplication identities for the coordinate slices `e.symm (Pi.single i a)` of a ring
equivalence `e : E ≃+* ∀ i, A i` (`RingEquiv.symm_single_one_mul`, `RingEquiv.symm_single_mul`),
and discards zero factors of a product of rings via `RingEquiv.piNontrivial` (splitting along
`Nontrivial (A i)` with `RingEquiv.piEquivPiSubtypeProd` and absorbing zero factors via
`RingEquiv.prodZeroRing`).

## Main definitions

* `RingEquiv.piNontrivial A : (∀ i, A i) ≃+* ∀ j : {i // Nontrivial (A i)}, A j`: restriction to
  the nonzero factors; its inverse fills the zero factors with `0`.
-/

public section

namespace RingEquiv

section CoordinateSlices

variable {E : Type*} [Semiring E] {ι : Type*} [DecidableEq ι] {A : ι → Type*}
  [∀ i, Semiring (A i)]

/-- Multiplying on the left by `e.symm (Pi.single i 1)` projects `x` onto the `i`-th slice. -/
theorem symm_single_one_mul (e : E ≃+* ∀ i, A i) (i : ι) (x : E) :
    e.symm (Pi.single i 1) * x = e.symm (Pi.single i (e x i)) :=
  e.injective <| by simp [← Pi.single_mul_left]

/-- The `i`-th coordinate embedding `a ↦ e.symm (Pi.single i a)` preserves multiplication. -/
theorem symm_single_mul (e : E ≃+* ∀ i, A i) (i : ι) (u v : A i) :
    e.symm (Pi.single i (u * v)) = e.symm (Pi.single i u) * e.symm (Pi.single i v) := by
  rw [Pi.single_mul, map_mul]

end CoordinateSlices

section PiNontrivial

variable {ι : Type*} (A : ι → Type*) [∀ i, NonAssocSemiring (A i)]

open Classical in
/-- A product of rings is isomorphic to the product of its nonzero factors: restriction to the
indices `i` with `Nontrivial (A i)` is a ring isomorphism, whose inverse fills the remaining,
zero, factors with `0`. -/
noncomputable def piNontrivial : (∀ i, A i) ≃+* ∀ j : {i // Nontrivial (A i)}, A j :=
  haveI (i : {i // ¬Nontrivial (A i)}) : Subsingleton (A i) :=
    not_nontrivial_iff_subsingleton.mp i.property
  (piEquivPiSubtypeProd (fun i ↦ Nontrivial (A i)) A).trans
    (prodZeroRing (∀ j : {i // Nontrivial (A i)}, A j) (∀ j : {i // ¬Nontrivial (A i)}, A j)).symm

@[simp]
theorem piNontrivial_apply (x : ∀ i, A i) (j : {i // Nontrivial (A i)}) :
    piNontrivial A x j = x j :=
  (rfl)

open Classical in
theorem piNontrivial_symm_apply (y : ∀ j : {i // Nontrivial (A i)}, A j) (i : ι) :
    (piNontrivial A).symm y i = if h : Nontrivial (A i) then y ⟨i, h⟩ else 0 :=
  (rfl)

/-- On a nonzero factor, the inverse of `RingEquiv.piNontrivial` is the given coordinate. -/
@[simp]
theorem piNontrivial_symm_apply_coe (y : ∀ j : {i // Nontrivial (A i)}, A j)
    (j : {i // Nontrivial (A i)}) : (piNontrivial A).symm y j = y j := by
  classical
  rw [piNontrivial_symm_apply, dite_eq_left_of_eq_true (eq_true j.property)]

end PiNontrivial

end RingEquiv
