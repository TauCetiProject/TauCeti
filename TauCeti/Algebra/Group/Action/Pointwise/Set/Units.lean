/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Prod

/-!
# Units of product monoids acting on product sets

A unit of a product of monoids acts on the product by left multiplication in each coordinate. This
file records that this action moves product sets coordinatewise, by the components of the unit.
These are the unit counterparts of Mathlib's `Set.smul_set_prod` and `Set.smul_set_univ_pi`, in
which a single scalar acts on every factor.

## Main results

* `Units.smul_set_prod`: a unit `x` of `R × S` sends `s ×ˢ t` to `(x₁ • s) ×ˢ (x₂ • t)`.
* `Units.smul_set_univ_pi`: a unit `x` of `Π i, T i` sends the box `univ.pi C` to the box with
  factors `x i • C i`.
-/

public section

open Set
open scoped Pointwise

namespace Units

/-- A unit of `R × S` acts on a product set coordinatewise. -/
theorem smul_set_prod {R S : Type*} [Monoid R] [Monoid S] (x : (R × S)ˣ) (s : Set R)
    (t : Set S) :
    x • s ×ˢ t =
      (Units.map (MonoidHom.fst R S) x • s) ×ˢ (Units.map (MonoidHom.snd R S) x • t) := by
  ext p
  simp only [mem_smul_set_iff_inv_smul_mem, mem_prod]
  simp [Units.smul_def]

/-- A unit of `Π i, T i` acts on a box coordinatewise. -/
theorem smul_set_univ_pi {ι : Type*} {T : ι → Type*} [∀ i, Monoid (T i)] (x : (Π i, T i)ˣ)
    (C : ∀ i, Set (T i)) :
    x • univ.pi C = univ.pi fun i ↦ Units.map (Pi.evalMonoidHom T i) x • C i := by
  ext p
  simp only [mem_smul_set_iff_inv_smul_mem, mem_univ_pi]
  simp [Units.smul_def]

end Units
